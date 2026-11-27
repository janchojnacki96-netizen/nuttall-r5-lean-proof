import Nuttall.ShiftedThetaAlgebra
import Nuttall.TailMoments
import Nuttall.ProductTailTranslation

namespace Nuttall

open MeasureTheory Set
open scoped BigOperators

/-- Translate the product integral for one fixed tuple of positive theta
indices. The resulting coordinate lower bounds are the corresponding knots. -/
theorem integral_fixed_indices_shift {p : ℕ} (k n : Fin p → ℕ)
    (hn : ∀ i, 0 < n i) (t : ℝ) :
    (∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySummand (n j) (x j) *
        (auxiliaryDerivativePolynomial i.val).eval (auxiliaryCoordinate (n j) (x j)))).det
        ∂Measure.pi (fun _ => volume.restrict (Ici t))) =
    (thetaScale t * Real.exp t)^p * (4 * thetaScale t)^(p*(p-1)/2) *
      ∫ u : Fin p → ℝ,
        (Matrix.of (fun (i j : Fin p) =>
          tailMomentWeight (k i) (u j-thetaKnot (n j)))).det *
        (Matrix.vandermonde (fun j => Real.exp (4*u j))).det *
        (∏ j : Fin p, thetaOrthantWeight (thetaScale t) (u j) / Real.sqrt (n j : ℝ))
        ∂Measure.pi (fun j => volume.restrict (Ici (thetaKnot (n j)))) := by
  let d : Fin p → ℝ := fun j => thetaKnot (n j)-t
  let F (u : Fin p → ℝ) : ℝ :=
    (Matrix.of (fun (i j : Fin p) =>
      tailMomentWeight (k i) (u j-thetaKnot (n j)))).det *
    (Matrix.vandermonde (fun j => Real.exp (4*u j))).det *
    (∏ j : Fin p, thetaOrthantWeight (thetaScale t) (u j) / Real.sqrt (n j : ℝ))
  let C := (thetaScale t * Real.exp t)^p * (4 * thetaScale t)^(p*(p-1)/2)
  have htranslate := integral_product_tails_add (fun _ : Fin p => t) d F
  have hlo (j : Fin p) : t + d j = thetaKnot (n j) := by dsimp [d]; ring
  simp only [hlo] at htranslate
  change _ = C * ∫ u : Fin p → ℝ, F u ∂Measure.pi (fun j => volume.restrict (Ici (thetaKnot (n j))))
  rw [← htranslate, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have hx (j : Fin p) : t + (x j-t) = x j := by ring
  have hu (j : Fin p) : x j-t+thetaKnot (n j) = x j+d j := by dsimp [d]; ring
  have hw (j : Fin p) : x j+d j-thetaKnot (n j) = x j-t := by dsimp [d]; ring
  have hdet := det_auxiliary_summands_shift n hn t (fun j => x j-t)
  simp only [hx, hu] at hdet
  have htranspose :
      (Matrix.of (fun (i j : Fin p) => auxiliarySummand (n j) (x j) *
        (auxiliaryDerivativePolynomial i.val).eval (auxiliaryCoordinate (n j) (x j)))).det =
      (Matrix.of (fun (i j : Fin p) => auxiliarySummand (n i) (x i) *
        (auxiliaryDerivativePolynomial j.val).eval (auxiliaryCoordinate (n i) (x i)))).det := by
    rw [← Matrix.det_transpose]
    rfl
  rw [htranspose, hdet]
  simp only [F, hw, C]
  ring

#print axioms integral_fixed_indices_shift

end Nuttall
