import Nuttall.ConfluentEvaluationLimit
import Nuttall.DeterminantRowIntegral
import Nuttall.PsiDerivativeTailIntegral
import Nuttall.SignedKernelCriterion

namespace Nuttall

open Function MeasureTheory Set
open scoped BigOperators ContDiff

private noncomputable def signedPsiJet (m j : ℕ) (s : ℝ) : ℝ :=
  (-1:ℝ)^j * iteratedDeriv j (psi m) s

private theorem signedPsiJet_contDiff (m j d : ℕ) : ContDiff ℝ d (signedPsiJet m j) := by
  unfold signedPsiJet
  apply contDiff_const.mul
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv' d j ((contDiff_psi m).of_le (by simp))

private theorem iteratedDeriv_signedPsiJet (m i j : ℕ) (s : ℝ) :
    iteratedDeriv i (signedPsiJet m j) s = (-1:ℝ)^j * iteratedDeriv (i+j) (psi m) s := by
  unfold signedPsiJet
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate, Function.iterate_add_apply]

private theorem signedPsiJet_familyWronskian (m p : ℕ) (s : ℝ) :
    familyWronskian (fun j : Fin p => signedPsiJet m j.val) s =
      kernelMinorSign p * wronskian (psi m) p s := by
  let A : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun i j => iteratedDeriv (i.val+j.val) (psi m) s
  have h : (Matrix.of fun i j : Fin p => iteratedDeriv i.val (signedPsiJet m j.val) s) =
      Matrix.of (fun i j => (-1:ℝ)^j.val * A i j) := by
    ext i j
    exact iteratedDeriv_signedPsiJet m i.val j.val s
  rw [familyWronskian, h, Matrix.det_mul_row, kernelMinorSign, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]
  all_goals rfl

private theorem signedPsiJet_eval_det_pos (m n : ℕ) {a : ℝ}
    (hW : ∀ p ≤ n+1, ∀ s > a, 0 < kernelMinorSign p * wronskian (psi m) p s)
    (u : Fin (n+1) → ℝ) (hu : StrictMono u) (hu₀ : ∀ i, a < u i) :
    0 < (Matrix.of (fun i j => signedPsiJet m j.val (u i))).det := by
  let B := u (Fin.last n) + 1
  have huB (i : Fin (n+1)) : u i ∈ Ioo a B := by
    refine ⟨hu₀ i, ?_⟩
    have hi := hu.monotone (Fin.le_last i)
    dsimp [B]
    linarith only [hi]
  refine det_eval_pos_of_familyWronskians (S := ∅) countable_empty
    (fun j => signedPsiJet m j.val) ?_ ?_ ?_ ?_ u hu huB (by simp)
  · intro j d _
    exact (signedPsiJet_contDiff m j.val d).contDiffOn
  · intro j d _
    have hd := (signedPsiJet_contDiff m j.val (d+1)).contDiff_iteratedDeriv d
      (by exact_mod_cast Nat.le_succ d)
    exact hd.contDiffOn.locallyLipschitzOn (convex_Ioo _ _)
  · intro j s _ _
    exact (signedPsiJet_contDiff m j.val n).contDiffAt
  · intro k hk s hs _
    change 0 < familyWronskian (fun j : Fin (k+1) => signedPsiJet m j.val) s
    rw [signedPsiJet_familyWronskian]
    exact hW (k+1) (by omega) s hs.1

/-- Strict signs of the Wronskians on an open tail survive one integration. -/
theorem psi_succ_signed_wronskian_pos_on_tail (m n : ℕ) {a t : ℝ} (ht : a < t)
    (hW : ∀ p ≤ n+1, ∀ s > a, 0 < kernelMinorSign p * wronskian (psi m) p s) :
    0 < kernelMinorSign (n+1) * wronskian (psi (m+1)) (n+1) t := by
  let f (j : Fin (n+1)) := signedPsiJet m j.val
  let A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j =>
     Fin.lastCases 0 (fun k : Fin n => iteratedDeriv k.val (f j) t) i
  let z (s : ℝ) := (A.updateRow (Fin.last n) (fun j => f j s)).det
  have hupdate (row : Fin (n+1) → ℝ) :
      A.updateRow (Fin.last n) row =
        Matrix.of (fun i j => Fin.lastCases (row j) (fun k : Fin n => iteratedDeriv k.val (f j) t) i) := by
    ext i j
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i
    · simp
    · simp [A, Matrix.updateRow_ne k.castSucc_ne_last]
  have hf : ∀ j, ContDiff ℝ n (f j) := fun j => signedPsiJet_contDiff m j.val n
  have hnonneg (s : ℝ) (hs : t < s) : 0 ≤ z s := by
    dsimp [z]
    rw [hupdate]
    refine det_firstJets_lastValue_nonneg n f hf hs ?_
    intro u hu hu₀
    exact (signedPsiJet_eval_det_pos m n hW u hu (fun i => ht.trans_le (hu₀ i))).le
  have hjet : iteratedDeriv n z t = kernelMinorSign (n+1) * wronskian (psi m) (n+1) t := by
    dsimp [z]
    rw [iteratedDeriv_det_updateRow A (Fin.last n) f hf, hupdate, ← signedPsiJet_familyWronskian,
      familyWronskian]
    congr 1
    ext i j
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i <;> simp [familyWronskian, f]
  have hI : ∀ j, IntegrableOn (f j) (Ioi t) := by
    intro j
    exact (integrableOn_iteratedDeriv_psi_Ioi m j.val t).const_mul _
  have hzpos : 0 < ∫ s in Ioi t, z s :=
    integral_Ioi_pos_of_iteratedDeriv_ne_zero (contDiff_det_updateRow A _ f hf)
      (integrable_det_updateRow A _ f hI) hnonneg (by rw [hjet]; exact (hW _ le_rfl _ ht).ne')
  change 0 < ∫ s in Ioi t, (A.updateRow (Fin.last n) (fun j => f j s)).det at hzpos
  rw [← det_updateRow_integral A (Fin.last n) f hI, hupdate] at hzpos
  let C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ := Matrix.of fun i j =>
    (-1:ℝ)^j.val * iteratedDeriv (i.val+j.val) (psi (m+1)) t
  have hm : (Matrix.of fun i j : Fin (n+1) =>
      Fin.lastCases (motive := fun _ => ℝ) (∫ s in Ioi t, f j s)
        (fun k : Fin n => iteratedDeriv k.val (f j) t) i) =
      Matrix.of (fun i j => Fin.lastCases (motive := fun _ => ℝ) (C 0 j)
        (fun k : Fin n => -C k.succ j) i) := by
    ext i j
    refine Fin.lastCases ?_ (fun k : Fin n => ?_) i
    · simp only [Matrix.of_apply, Fin.lastCases_last, f, signedPsiJet, C, Fin.val_zero, zero_add,
        integral_const_mul, iteratedDeriv_psi_succ_eq_integral_Ioi]
    · simp only [Matrix.of_apply, Fin.lastCases_castSucc, f, iteratedDeriv_signedPsiJet, C, Fin.val_succ]
      rw [show k.val+1+j.val = (k.val+j.val)+1 by omega, iteratedDeriv_succ_psi_succ]
      ring
  rw [hm, det_rotate_negated_rows] at hzpos
  rw [← signedPsiJet_familyWronskian]
  have hC : (Matrix.of fun i j : Fin (n+1) => iteratedDeriv i.val (signedPsiJet (m+1) j.val) t) = C := by
    ext i j
    exact iteratedDeriv_signedPsiJet (m+1) i.val j.val t
  rwa [familyWronskian, hC]

#print axioms psi_succ_signed_wronskian_pos_on_tail

end Nuttall
