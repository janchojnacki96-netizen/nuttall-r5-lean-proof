import Nuttall.ReverseSignRegularity
import Nuttall.EvaluationDeterminant
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Nuttall

open Filter MeasureTheory Set

private theorem measurePreserving_openTail_add (a d : ℝ) :
    MeasurePreserving (MeasurableEquiv.addRight d)
      (volume.restrict (Ioi a)) (volume.restrict (Ioi (d+a))) := by
  let e := MeasurableEquiv.addRight d
  have he : MeasurePreserving e volume volume :=
    ⟨e.measurable, map_add_right_eq_self volume d⟩
  have hp : e ⁻¹' Ioi (d+a) = Ioi a := by
    ext s
    change d+a < s+d ↔ a < s
    rw [add_comm d a, add_lt_add_iff_right]
  simpa only [hp] using he.restrict_preimage (s := Ioi (d+a)) measurableSet_Ioi

private theorem tailIntegral_translate (f : ℝ → ℝ) (a d : ℝ) :
    ∫ s in Ioi a, f (d+s) = tailIntegral f (d+a) := by
  unfold tailIntegral
  rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  calc
    _ = ∫ s in Ioi a, f ((MeasurableEquiv.addRight d) s) := by
      apply integral_congr_ae
      filter_upwards with s
      change f (d+s) = f (s+d)
      rw [add_comm]
    _ = _ := (measurePreserving_openTail_add a d).integral_comp' f

private theorem integrableOn_psi_translate (m : ℕ) (a d : ℝ) :
    IntegrableOn (fun s => psi m (d+s)) (Ioi a) := by
  let e := MeasurableEquiv.addRight d
  have hi := (psi_integrableOn m (d+a)).mono_set Ioi_subset_Ici_self
  have h := ((measurePreserving_openTail_add a d).integrable_comp_emb e.measurableEmbedding).2 hi
  have hh : (psi m) ∘ e = fun s => psi m (d+s) := funext (fun s => by
    change psi m (s+d) = psi m (d+s)
    rw [add_comm])
  rw [← hh]
  exact h

def tailPartition {n : ℕ} (y : Fin (n+1) → ℝ) (j : Fin (n+1)) : Set ℝ :=
  Fin.lastCases (Ioi (y (Fin.last n))) (fun i => Ioc (y i.castSucc) (y i.succ)) j

private theorem tailPartition_subset {n : ℕ} (y : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    tailPartition y j ⊆ Ioi (y j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [tailPartition]
  · simp only [tailPartition, Fin.lastCases_castSucc]
    exact Ioc_subset_Ioi_self

private theorem measurableSet_tailPartition {n : ℕ} (y : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    MeasurableSet (tailPartition y j) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [tailPartition]
  · simp [tailPartition]

private theorem strictMono_of_tailPartition {n : ℕ} {y : Fin (n+1) → ℝ}
    (hy : Monotone y) {z : Fin (n+1) → ℝ} (hz : ∀ i, z i ∈ tailPartition y i) :
    StrictMono z := by
  intro i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · intro j hj
    exact (not_lt_of_ge (Fin.le_last j) hj).elim
  · intro j hj
    have hk : k.succ ≤ j := by
      simp only [Fin.le_def, Fin.val_succ]
      exact Nat.succ_le_of_lt hj
    have hupper : z k.castSucc ≤ y k.succ := by
      have h := hz k.castSucc
      simp only [tailPartition, Fin.lastCases_castSucc, mem_Ioc] at h
      exact h.2
    exact hupper.trans_lt ((hy hk).trans_lt (tailPartition_subset y j (hz j)))

private theorem det_eq_of_row_eq_add_next {n : ℕ} {A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hLast : ∀ j, A (Fin.last n) j = B (Fin.last n) j)
    (hNext : ∀ (i : Fin n) j, A i.castSucc j = B i.castSucc j + A i.succ j) :
    A.det = B.det := by
  have h : (A.submatrix Fin.revPerm id).det = (B.submatrix Fin.revPerm id).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
    · intro j
      simpa [Matrix.submatrix] using hLast j
    · intro i j
      simpa [Matrix.submatrix, Fin.rev_succ, Fin.rev_castSucc] using hNext i.rev j
  rw [Matrix.det_permute, Matrix.det_permute] at h
  exact mul_left_cancel₀ (by exact_mod_cast Units.ne_zero (Equiv.Perm.sign (Fin.revPerm (n := n+1)))) h

/-- Successive upper-tail integration domains can be replaced by disjoint
ordered intervals, using determinant-preserving differences of consecutive rows. -/
theorem det_tail_eq_integral_on_ordered_partition {n : ℕ} (y : Fin (n+1) → ℝ)
    (hy : Monotone y) (g : Fin (n+1) → ℝ → ℝ)
    (hg : ∀ i j, IntegrableOn (g j) (Ioi (y i))) :
    (Matrix.of (fun i j => ∫ s in Ioi (y i), g j s)).det =
      ∫ z : Fin (n+1) → ℝ, (Matrix.of (fun i j => g j (z i))).det
        ∂Measure.pi (fun i => volume.restrict (tailPartition y i)) := by
  let A := Matrix.of (fun i j => ∫ s in Ioi (y i), g j s)
  let B := Matrix.of (fun i j => ∫ s in tailPartition y i, g j s)
  have he : A.det = B.det := by
    apply det_eq_of_row_eq_add_next
    · intro j
      simp [A,B,tailPartition]
    · intro i j
      have hi : y i.castSucc ≤ y i.succ := hy Fin.castSucc_lt_succ.le
      have hd : Ioi (y i.castSucc) \ Ioi (y i.succ) = Ioc (y i.castSucc) (y i.succ) := by
        ext x
        simp
      have h := setIntegral_sdiff measurableSet_Ioi (hg i.castSucc j) (Ioi_subset_Ioi hi)
      rw [hd] at h
      simpa [A,B,tailPartition] using (eq_sub_iff_add_eq.1 h).symm
  rw [he]
  exact det_integral_rows _ g (fun i j => (hg i j).mono_set (tailPartition_subset y i))

/-- A successful level remains successful after another tail integration. -/
theorem reverseSignRegular.psi_succ {m r : ℕ} (h : reverseSignRegular (psi m) r) :
    reverseSignRegular (psi (m+1)) r := by
  intro p hp hpr x y hx hy hx₀ hy₀
  cases p with
  | zero => omega
  | succ n =>
    let G (i : Fin (n+1)) (s : ℝ) := psi m (x i+s)
    let μ (i : Fin (n+1)) := volume.restrict (tailPartition y i)
    let A := Matrix.of (fun i j => psi (m+1) (x i+y j))
    change 0 ≤ kernelMinorSign (n+1) * A.det
    rw [← Matrix.det_transpose A]
    have he : A.transpose = Matrix.of (fun i j => ∫ s in Ioi (y i), G j s) := by
      ext i j
      exact (tailIntegral_translate (psi m) (y i) (x j)).symm
    rw [he, det_tail_eq_integral_on_ordered_partition y hy.monotone G
      (fun i j => integrableOn_psi_translate m (y i) (x j)), ← integral_const_mul]
    have hcoords : ∀ᵐ z ∂Measure.pi μ, ∀ i, z i ∈ tailPartition y i := by
      rw [ae_all_iff]
      intro i
      exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := i)).eventually
        (ae_restrict_mem (measurableSet_tailPartition y i))
    apply integral_nonneg_of_ae
    filter_upwards [hcoords] with z hz
    have hzmono := strictMono_of_tailPartition hy.monotone hz
    have hzpos (i) : 0 < z i := (hy₀ i).trans (tailPartition_subset y i (hz i))
    have hRR := h (n+1) hp hpr x z hx hzmono hx₀ hzpos
    rw [← Matrix.det_transpose] at hRR
    exact hRR

/-- Monotonicity in the integration level in the weak reverse sign convention. -/
theorem reverseSignRegular.psi_of_le {m l r : ℕ} (hm : m ≤ l)
    (h : reverseSignRegular (psi m) r) : reverseSignRegular (psi l) r := by
  induction hm with
  | refl => exact h
  | step _ ih => exact ih.psi_succ

#print axioms reverseSignRegular.psi_succ
#print axioms reverseSignRegular.psi_of_le

end Nuttall
