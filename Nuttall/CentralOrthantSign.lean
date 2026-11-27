import Nuttall.ShiftedMomentEvaluationPositivity
import Nuttall.ShiftedOrthantConvergence
import Mathlib.Data.Fin.Tuple.Sort

namespace Nuttall

open Filter Set
open scoped BigOperators

private theorem shiftedOrthantIntegrand_perm {p : ℕ} (X : ℝ) (k : Fin p → ℕ)
    (u : Fin p → ℝ) (σ : Equiv.Perm (Fin p)) :
    shiftedOrthantIntegrand X (fun i _ => shiftedMoment (k i)) (u ∘ σ) =
      shiftedOrthantIntegrand X (fun i _ => shiftedMoment (k i)) u := by
  let A := Matrix.of (fun i j : Fin p => shiftedMoment (k i) (u j))
  let V := Matrix.vandermonde (fun j => Real.exp (4*u j))
  have hV : Matrix.vandermonde (fun j => Real.exp (4*(u ∘ σ) j)) =
      V.submatrix σ id := by
    ext i j
    simp [V, Matrix.vandermonde_apply]
  unfold shiftedOrthantIntegrand
  change (A.submatrix id σ).det * _ * _ = A.det * V.det * _
  rw [hV, Matrix.det_permute', Matrix.det_permute]
  simp only [Function.comp_apply]
  rw [Equiv.prod_comp σ (fun j => thetaOrthantWeight X (u j))]
  let ε : ℝ := ((Equiv.Perm.sign σ : ℤˣ) : ℤ)
  have he : |ε| = 1 := by
    dsimp [ε]
    exact_mod_cast Equiv.Perm.sign_abs σ
  have he' : ε^2 = 1 := by rw [← sq_abs, he, one_pow]
  change (ε * A.det) * (ε * V.det) * _ = _
  rw [show (ε * A.det) * (ε * V.det) = ε^2 * (A.det * V.det) by ring, he', one_mul]

/-- On increasing nodes the Vandermonde and weight factors have positive sign. -/
private theorem shiftedOrthantIntegrand_pos_of_eval {p : ℕ} {X : ℝ} {k : Fin p → ℕ}
    {u : Fin p → ℝ} (hu : StrictMono u)
    (hdet : 0 < (Matrix.of (fun i j => shiftedMoment (k j) (u i))).det) :
    0 < shiftedOrthantIntegrand X (fun i _ => shiftedMoment (k i)) u := by
  unfold shiftedOrthantIntegrand
  have hV : 0 < (Matrix.vandermonde (fun j => Real.exp (4*u j))).det := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
    exact sub_pos.2 (Real.exp_lt_exp.2 (by
      have := hu (Finset.mem_Ioi.1 hj)
      linarith))
  have hA : 0 < (Matrix.of (fun i j => shiftedMoment (k i) (u j))).det := by
    rw [← Matrix.det_transpose]
    exact hdet
  have hwt : 0 < ∏ j, thetaOrthantWeight X (u j) := by
    apply Finset.prod_pos
    intro j _
    unfold thetaOrthantWeight
    positivity
  exact mul_pos (mul_pos hA hV) hwt

/-- The central orthant integrand has the same positive sign for every
injective tuple of nodes, independent of its ordering. On collisions it vanishes. -/
theorem eventually_shiftedOrthantIntegrand_central_sign :
    ∀ᶠ r : ℕ in atTop, ∀ p : ℕ, 1 ≤ p → p ≤ r →
      ∀ (X : ℝ) (u : Fin p → ℝ), (∀ i, u i ∈ Ioo 0 (shiftCriticalCutoff r)) →
        0 ≤ shiftedOrthantIntegrand X (fun i _ => shiftedMoment (2*r-p+i.val-1)) u ∧
        (Function.Injective u →
          0 < shiftedOrthantIntegrand X (fun i _ => shiftedMoment (2*r-p+i.val-1)) u) := by
  filter_upwards [eventually_shiftedMoment_evaluation_det_pos] with r hr p hp hpr X u hu
  by_cases hinj : Function.Injective u
  · let σ := Tuple.sort u
    have hstrict : StrictMono (u ∘ σ) :=
      (Tuple.monotone_sort u).strictMono_of_injective (hinj.comp σ.injective)
    have hpos := shiftedOrthantIntegrand_pos_of_eval (X := X) hstrict
      (hr p hp hpr _ hstrict (fun i => hu (σ i)))
    rw [shiftedOrthantIntegrand_perm] at hpos
    exact ⟨hpos.le, fun _ => hpos⟩
  · have hV : (Matrix.vandermonde (fun j => Real.exp (4*u j))).det = 0 := by
      by_contra hv
      apply hinj
      intro i j hij
      exact Matrix.det_vandermonde_ne_zero_iff.1 hv (congrArg (fun x => Real.exp (4*x)) hij)
    constructor
    · simp [shiftedOrthantIntegrand, hV]
    · exact fun h => (hinj h).elim

#print axioms eventually_shiftedOrthantIntegrand_central_sign

end Nuttall
