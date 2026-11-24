import W5.ThetaCoarseGammaMomentBoxes
import W5.ThetaAudited768IntervalMatrices

/-!
# Second-order real lower Gamma moments for the original theta kernel

The quarter-Gamma UPPER bound shrinks moment uncertainty, but the
upper end of the n=1 interval in the second cell still requires a
strictly positive correction to the LOWER bound M₀ ≥ 1.

Use the globally valid quadratic lower polynomial for the actual
real fourth root; integrate it with the SAME pre-existing Mathlib
Gamma factorial moments. No Taylor numerical oracle, sampling,
new axiom, or parallel LDL proof is introduced.
-/

namespace W5
open MeasureTheory

/-- The quadratic Taylor polynomial of the real fourth root is a
GLOBAL lower bound for nonnegative t. The factorization in the
proof is exact, and all its factors are nonnegative for r ≥ 1. -/
theorem thetaFourthRoot_one_add_quadratic_lower
    (t : ℝ) (ht : 0 ≤ t) :
    1 + t/4 - 3*t^2/32 ≤ (1+t)^((1:ℝ)/4) := by
  let r : ℝ := (1+t)^((1:ℝ)/4)
  have hbase : 0 ≤ 1+t := by linarith
  have hr4 : r^4 = 1+t := by
    dsimp [r]
    calc
      ((1+t)^((1:ℝ)/4))^4 =
          ((1+t)^((1:ℝ)/4))^(4:ℝ) := by
            exact (Real.rpow_natCast ((1+t)^((1:ℝ)/4)) 4).symm
      _ = (1+t)^(((1:ℝ)/4)*(4:ℝ)) :=
        (Real.rpow_mul hbase ((1:ℝ)/4) (4:ℝ)).symm
      _ = 1+t := by norm_num
  have hr1 : 1 ≤ r := by
    dsimp [r]
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow (show (0:ℝ) ≤ 1 by norm_num)
        (show (1:ℝ) ≤ 1+t by linarith)
        (show (0:ℝ) ≤ 1/4 by norm_num))
  have hm : 0 ≤ r-1 := sub_nonneg.mpr hr1
  have hfactor :
      0 ≤ (r-1)^3 *
        (3*r^5 + 9*r^4 + 18*r^3 + 30*r^2 + 31*r + 21) := by
    positivity
  have ht4 : t = r^4 - 1 := by linarith [hr4]
  change 1 + t/4 - 3*t^2/32 ≤ r
  rw [ht4]
  nlinarith [hfactor]

/-- Actual weighted theta moment: a lower bound from second-order
fourth-root calculus, not merely its unweighted Gamma value k!.
The existing three Mathlib factorial integrals are reused. -/
theorem thetaAuditedOneWeightedMoment_gamma_lower_quadratic
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (Nat.factorial k : ℝ) +
      (x^2/4) * (Nat.factorial (k+1) : ℝ) -
      (3*x^4/32) * (Nat.factorial (k+2) : ℝ) ≤
        thetaAuditedOneWeightedMoment x k := by
  have hf : IntegrableOn
      (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k)
      (Set.Ici (0 : ℝ)) volume :=
    thetaAuditedOneWeightedMoment_integrable_nonneg x hx hx1 k
  have hΓ0 : IntegrableOn
      (fun w : ℝ => w^k * Real.exp (-w))
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable k)
  have hΓ1 : IntegrableOn
      (fun w : ℝ => w^(k+1) * Real.exp (-w))
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+1))
  have hΓ2 : IntegrableOn
      (fun w : ℝ => w^(k+2) * Real.exp (-w))
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+2))
  have hG : IntegrableOn
      (fun w : ℝ =>
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)))
      (Set.Ici (0 : ℝ)) volume :=
    (hΓ0.add (hΓ1.const_mul (x^2/4))).sub
      (hΓ2.const_mul (3*x^4/32))
  have hΓ0eval :
      (∫ w in Set.Ici (0 : ℝ),
        w^k * Real.exp (-w) ∂volume) =
        (Nat.factorial k : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment k
  have hΓ1eval :
      (∫ w in Set.Ici (0 : ℝ),
        w^(k+1) * Real.exp (-w) ∂volume) =
        (Nat.factorial (k+1) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+1)
  have hΓ2eval :
      (∫ w in Set.Ici (0 : ℝ),
        w^(k+2) * Real.exp (-w) ∂volume) =
        (Nat.factorial (k+2) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+2)
  have hpoint : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici (0 : ℝ))),
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ≤
          (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hw0 : 0 ≤ w := hw
    have hroot :
        1 + (w*x^2)/4 - 3*(w*x^2)^2/32 ≤
          (1+w*x^2)^((1:ℝ)/4) :=
      thetaFourthRoot_one_add_quadratic_lower (w*x^2)
        (mul_nonneg hw0 (sq_nonneg x))
    calc
      (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) =
        (Real.exp (-w) *
          (1 + (w*x^2)/4 - 3*(w*x^2)^2/32)) * w^k := by
            simp only [pow_add, pow_one, pow_two]
            ring
      _ ≤ (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot (Real.exp_nonneg _))
          (pow_nonneg hw0 k)
  have hInt :
      (∫ w in Set.Ici (0 : ℝ),
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ∂volume) =
      (∫ w in Set.Ici (0 : ℝ),
          w^k * Real.exp (-w) ∂volume) +
        (x^2/4) * (∫ w in Set.Ici (0 : ℝ),
          w^(k+1) * Real.exp (-w) ∂volume) -
        (3*x^4/32) * (∫ w in Set.Ici (0 : ℝ),
          w^(k+2) * Real.exp (-w) ∂volume) := by
    calc
      _ =
          (∫ w in Set.Ici (0 : ℝ),
            w^k * Real.exp (-w) +
              (x^2/4) * (w^(k+1) * Real.exp (-w)) ∂volume) -
          (∫ w in Set.Ici (0 : ℝ),
            (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ∂volume) := by
              simpa only [Pi.add_apply, Pi.sub_apply] using
                (integral_sub
                  (hΓ0.add (hΓ1.const_mul (x^2/4)))
                  (hΓ2.const_mul (3*x^4/32)))
      _ = _ := by
        rw [integral_add hΓ0 (hΓ1.const_mul (x^2/4))]
        rw [integral_const_mul, integral_const_mul]
  calc
    (Nat.factorial k : ℝ) +
        (x^2/4) * (Nat.factorial (k+1) : ℝ) -
        (3*x^4/32) * (Nat.factorial (k+2) : ℝ) =
      (∫ w in Set.Ici (0 : ℝ),
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ∂volume) := by
            rw [hInt, hΓ0eval, hΓ1eval, hΓ2eval]
    _ ≤ thetaAuditedOneWeightedMoment x k := by
      unfold thetaAuditedOneWeightedMoment
      exact integral_mono_ae hG hf hpoint

/-- A finite rational test: second-order analytic moment bounds
WOULD fit the existing 768-bit (0,0) cell-2 interval for n=1.
This exact arithmetic comparison does NOT by itself establish
the real theta-term enclosure or control the n≥2 terms. -/
def thetaSecondCellOneSquareZeroZeroQuadraticBox : QInterval :=
  ⟨1 - (((177 : ℚ) / 512)^2 / 4) *
      (1 + ((177 : ℚ) / 512)^2 / 4),
   1 - (((1 : ℚ) / 8)^2 / 4) *
      (1 + ((1 : ℚ) / 8)^2 / 4 -
        (3 * ((1 : ℚ) / 8)^4 / 16))⟩

theorem thetaSecondCellOneSquareZeroZeroQuadraticBox_fits_audit :
    (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).lo ≤
        thetaSecondCellOneSquareZeroZeroQuadraticBox.lo ∧
    thetaSecondCellOneSquareZeroZeroQuadraticBox.hi ≤
        (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).hi := by
  native_decide

end W5
