import W5.ThetaSecondCellHeadPositiveWPolynomial
import W5.ThetaSecondCellPositiveCellUpper
import W5.ThetaAllSquareIndexNineMoments

/-!
# True original correction integral bounded by positive polynomial integral

Reuse the exact original B_ij polynomial cell enclosure and the
Mathlib finite-polynomial Lebesgue integrability implicit in the
already-proved weighted Gamma moment reduction. The resulting
inequality is valid simultaneously for every original theta entry
and every n>=1; it involves the ACTUAL original correction integral,
not an abstract finite approximation.

This is independent of the finite K arithmetic and of proving
nonnegative polynomial coefficients. PR #135 covers the latter;
PR #136 covers the double-binomial expansion of the same polynomial.
-/

namespace W5
open MeasureTheory

/-- The existing integrability of individual original weighted
Gamma moments implies integrability of ANY weighted polynomial.
No new integration technique is needed: Mathlib's polynomial
coefficient expansion and finite integrable sum suffice. -/
theorem thetaHeadWeightedPolynomial_integrableOn
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (P : Polynomial ℝ) :
    IntegrableOn (fun w : ℝ =>
      (Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)) * P.eval w)
      (Set.Ici (0:ℝ)) volume := by
  classical
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)
  have hsum : IntegrableOn
      (fun w : ℝ =>
        ∑ k ∈ Finset.range (P.natDegree+1),
          P.coeff k * (W w * w^k))
      (Set.Ici (0:ℝ)) volume :=
    integrable_finsetSum (Finset.range (P.natDegree+1))
      (fun k _ =>
        (thetaAuditedOneWeightedMoment_integrable y hy hy1 k).const_mul
          (P.coeff k))
  have hfunc : (fun w : ℝ => W w * P.eval w) =
      (fun w : ℝ =>
        ∑ k ∈ Finset.range (P.natDegree+1),
          P.coeff k * (W w * w^k)) := by
    funext w
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  change IntegrableOn (fun w : ℝ => W w * P.eval w)
    (Set.Ici (0:ℝ)) volume
  rw [hfunc]
  exact hsum

/-- The genuine original signed correction integral has modulus
dominated by the weighted integral of the EXACT positive factorial
polynomial at the rational cell endpoints. This is one universal
measure-theoretic bridge for all 25 coefficients; no quadrature or
unproved coefficient assumptions appear. -/
theorem thetaHeadOriginalIntegral_abs_le_positiveIntegral
    (a b : ℚ) (x : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin 5)
    (ha : (0:ℝ) < (a:ℝ))
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1) :
    |∫ w in Set.Ici (0:ℝ),
        Real.exp (-w) *
          (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
          coefficientPolynomial i j
            ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)
      ∂volume| ≤
      ∫ w in Set.Ici (0:ℝ),
        (Real.exp (-w) *
          (1+w*(x/(n:ℝ))^2)^((1:ℝ)/4)) *
        (thetaHeadPositiveWPolynomial
          (((n:ℝ)^2-1)/(a:ℝ)) ((n:ℝ)^2) (b:ℝ) i j).eval w
      ∂volume := by
  have hx : 0 < x := ha.trans_le hax
  have hx1 : x ≤ 1 := hxb.trans hb
  have hnR : (0:ℝ) < (n:ℝ) := by
    have h : 0 < n := by omega
    exact_mod_cast h
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hy : 0 < x/(n:ℝ) := div_pos hx hnR
  have hy1 : x/(n:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    linarith
  let P : Polynomial ℝ :=
    thetaHeadPositiveWPolynomial
      (((n:ℝ)^2-1)/(a:ℝ)) ((n:ℝ)^2) (b:ℝ) i j
  let y : ℝ := x/(n:ℝ)
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)
  have hG : IntegrableOn (fun w : ℝ => W w * P.eval w)
      (Set.Ici (0:ℝ)) volume :=
    thetaHeadWeightedPolynomial_integrableOn y hy hy1 P
  have hwgt (w : ℝ) :
      1+w*x^2/((n:ℝ)^2) = 1+w*y^2 := by
    dsimp [y]
    rw [div_pow]
    ring
  have hpoint : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici (0:ℝ))),
      ‖Real.exp (-w) *
        (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
        coefficientPolynomial i j
          ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)‖ ≤
          W w * P.eval w := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hW : 0 ≤ W w := by
      dsimp [W]
      have hbase : 0 ≤ 1+w*y^2 := by positivity
      exact mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg hbase _)
    have hpoly :=
      thetaPositivePolynomial_cell_upper
        (a:ℝ) (b:ℝ) x ((n:ℝ)^2) w ha hax hxb hp hw i j
    calc
      ‖Real.exp (-w) *
        (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
        coefficientPolynomial i j
          ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)‖ =
        W w * |coefficientPolynomial i j
          ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)| := by
          rw [Real.norm_eq_abs, abs_mul, hwgt w]
          rw [abs_of_nonneg hW]
      _ ≤ W w * thetaCoefficientPositivePolynomial i j
          (((n:ℝ)^2-1)/(a:ℝ)+w*(b:ℝ))
          (((n:ℝ)^2)+w*(b:ℝ)^2) :=
        mul_le_mul_of_nonneg_left hpoly hW
      _ = W w * P.eval w := by
        dsimp [P]
        rw [thetaHeadPositiveWPolynomial_eval]
  have hnorm :=
    norm_integral_le_of_norm_le hG hpoint
  simpa only [Real.norm_eq_abs, P, W, y] using hnorm

end W5
