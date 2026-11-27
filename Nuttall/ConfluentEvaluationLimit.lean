import Nuttall.ForwardDifferenceKernel
import Nuttall.ForwardDifferenceLimit

namespace Nuttall

open Filter Function Set
open scoped BigOperators ContDiff Topology

/-- The first n evaluation rows may coalesce to jets at t while the last
row remains an evaluation at s. The limiting determinant is nonnegative
if the equally spaced evaluation determinants are eventually nonnegative. -/
theorem det_firstJets_lastValue_nonneg_of_eventually (n : ℕ)
    (f : Fin (n+1) → ℝ → ℝ) (hf : ∀ j, ContDiff ℝ n (f j)) (t s : ℝ)
    (hgrid : ∀ᶠ h in 𝓝[>] (0:ℝ), 0 ≤
      (Matrix.of fun (i j : Fin (n+1)) =>
        Fin.lastCases (motive := fun _ => ℝ) (f j s)
          (fun k : Fin n => f j (t+k.val • h)) i).det) :
    0 ≤ (Matrix.of fun (i j : Fin (n+1)) =>
      Fin.lastCases (motive := fun _ => ℝ) (f j s)
        (fun k : Fin n => iteratedDeriv k.val (f j) t) i).det := by
  let A (h : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j =>
    Fin.lastCases (f j s) (fun k : Fin n => ((fwdDiff h)^[k.val] (f j) t)/h^k.val) i
  let W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j =>
    Fin.lastCases (f j s) (fun k : Fin n => iteratedDeriv k.val (f j) t) i
  have hA : Tendsto A (𝓝[>] (0:ℝ)) (𝓝 W) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i
    · simpa only [A, W, Matrix.of_apply, Fin.lastCases_last] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => f j s) (𝓝[>] (0:ℝ)) (𝓝 (f j s)))
    · simpa only [A, W, Matrix.of_apply, Fin.lastCases_castSucc] using
        tendsto_normalized_fwdDiff ((hf j).of_le (by exact_mod_cast k.isLt.le)) t
  have hdet : Continuous (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => M.det) :=
    continuous_id.matrix_det
  apply ge_of_tendsto ((hdet.continuousAt (x := W)).tendsto.comp hA)
  filter_upwards [self_mem_nhdsWithin, hgrid] with h hh hnonneg
  have hp : 0 < h := mem_Ioi.mp hh
  let c (i : Fin (n+1)) : ℝ := Fin.lastCases 1 (fun k : Fin n => h^k.val) i
  have hc : ∀ i, 0 < c i := by
    intro i
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i
    · simp [c]
    · simpa only [c, Fin.lastCases_castSucc] using pow_pos hp k.val
  have he : (Matrix.of fun (i j : Fin (n+1)) =>
      Fin.lastCases (motive := fun _ => ℝ) (f j s)
        (fun k : Fin n => (fwdDiff h)^[k.val] (f j) t) i) =
      Matrix.of (fun i j => c i * A h i j) := by
    ext i j
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i
    · simp [A, c]
    · simp only [A, c, Matrix.of_apply, Fin.lastCases_castSucc]
      exact (mul_div_cancel₀ _ (pow_ne_zero _ hp.ne')).symm
  rw [det_gridWithLast_eq_det_forwardDiff, he, Matrix.det_mul_column] at hnonneg
  exact (mul_nonneg_iff_of_pos_left (Finset.prod_pos (fun i _ => hc i))).mp hnonneg

/-- Positive gaps between the final point and the first cluster let the
ordinary evaluation inequality pass to the mixed jet determinant. -/
theorem det_firstJets_lastValue_nonneg (n : ℕ) (f : Fin (n+1) → ℝ → ℝ)
    (hf : ∀ j, ContDiff ℝ n (f j)) {t s : ℝ} (hts : t < s)
    (hdet : ∀ u : Fin (n+1) → ℝ, StrictMono u → (∀ i, t ≤ u i) →
      0 ≤ (Matrix.of fun (i j : Fin (n+1)) => f j (u i)).det) :
    0 ≤ (Matrix.of fun (i j : Fin (n+1)) =>
      Fin.lastCases (motive := fun _ => ℝ) (f j s)
        (fun k : Fin n => iteratedDeriv k.val (f j) t) i).det := by
  apply det_firstJets_lastValue_nonneg_of_eventually n f hf
  have hδ : 0 < (s-t)/((n:ℝ)+1) := div_pos (sub_pos.mpr hts) (by positivity)
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0:ℝ), h < (s-t)/((n:ℝ)+1) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hlt
  let u (i : Fin (n+1)) : ℝ := Fin.lastCases s (fun k : Fin n => t+k.val • h) i
  have hpos : 0 < h := mem_Ioi.mp hh
  have hs : h*((n:ℝ)+1) < s-t := (lt_div_iff₀ (by positivity)).mp hlt
  have hb (i : Fin n) : t+i.val • h < s := by
    have hi : (i.val:ℝ) ≤ (n:ℝ) := by exact_mod_cast i.isLt.le
    have hmul := mul_le_mul_of_nonneg_right hi hpos.le
    simp only [nsmul_eq_mul]
    nlinarith only [hs, hmul, hpos]
  have hmono : StrictMono u := by
    intro i j
    refine Fin.lastCases ?_ (fun a : Fin n => ?_) i
    · intro hbad
      exact (not_lt_of_ge (Fin.le_last j) hbad).elim
    · refine Fin.lastCases ?_ (fun b : Fin n => ?_) j
      · intro _
        simpa only [u, Fin.lastCases_castSucc, Fin.lastCases_last] using hb a
      · intro hab
        have h' : (a.val:ℝ) < (b.val:ℝ) := by exact_mod_cast (Fin.lt_def.1 hab)
        simpa only [u, Fin.lastCases_castSucc, nsmul_eq_mul] using
          add_lt_add_of_le_of_lt (le_refl t) (mul_lt_mul_of_pos_right h' hpos)
  have ht (i : Fin (n+1)) : t ≤ u i := by
    refine Fin.lastCases ?_ (fun a : Fin n => ?_) i
    · simpa only [u, Fin.lastCases_last] using hts.le
    · simp only [u, Fin.lastCases_castSucc, nsmul_eq_mul, le_add_iff_nonneg_right]
      positivity
  have he : (Matrix.of fun (i j : Fin (n+1)) =>
      Fin.lastCases (motive := fun _ => ℝ) (f j s) (fun k : Fin n => f j (t+k.val • h)) i) =
      Matrix.of (fun i j => f j (u i)) := by
    ext i j
    refine Fin.lastCases ?_ (fun a : Fin n => ?_) i <;> simp [u]
  rw [he]
  exact hdet u hmono ht

#print axioms det_firstJets_lastValue_nonneg_of_eventually
#print axioms det_firstJets_lastValue_nonneg

end Nuttall
