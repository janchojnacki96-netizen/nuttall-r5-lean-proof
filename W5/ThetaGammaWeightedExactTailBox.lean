import W5.ThetaGammaWeightedExactUpperTail
import W5.ThetaGammaAutoRootGrid

/-!
# One exact-rational enclosure for the ORIGINAL weighted Gamma tail

The recentered Gamma grid from PR #167 encloses the true truncated
theta moment, while ThetaGammaWeightedExactUpperTail proves the
sharper real upper bound for the unbounded tail. This module converts
that upper bound to a sound, executable QInterval by reusing the
existing certified exp(-H) evaluator and exact Gamma tail polynomial.

No floating-point calculations or unverified table values enter
the mathematical proof. Positivity of the moment integrand gives
the lower endpoint zero; one rational inequality checks exp(-H).
-/

namespace W5
open MeasureTheory

/-- The incomplete Gamma tail polynomial is nonnegative for every
nonnegative rational endpoint. All coefficients are nonnegative. -/
theorem thetaGammaBinPolyQ_nonneg (k : ℕ) (H : ℚ)
    (hH : 0 ≤ H) : 0 ≤ thetaGammaBinPolyQ k H := by
  induction k with
  | zero =>
      simp [thetaGammaBinPolyQ]
  | succ k ih =>
      change 0 ≤ ((k+1:ℕ):ℚ) * thetaGammaBinPolyQ k H +
        H^(k+1)
      positivity

/-- A completely executable upper interval for the TRUE original
weighted theta Gamma moment beyond H. -/
def thetaGammaWeightedExactTailBox (k : ℕ) (y H : ℚ) : QInterval :=
  ⟨0, (thetaGammaBinExpNegBox H).hi *
    (thetaGammaBinPolyQ k H +
      (y^2/4) * thetaGammaBinPolyQ (k+1) H)⟩

/-- One real-soundness theorem for the genuine infinite weighted
Gamma tail at ANY moment order and ANY rational H in Taylor range. -/
theorem thetaGammaWeightedExactTailBox_containsReal
    (k : ℕ) (y H : ℚ)
    (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hH : 0 ≤ H) (hHmax : H ≤ (1024:ℚ)/3)
    (hExp : 0 <
      (thetaBulkExpTaylorBox
        (QInterval.point (H/1024))).lo) :
    QInterval.ContainsReal
      (thetaGammaWeightedExactTailBox k y H)
      (∫ w in Set.Ici (H:ℝ),
        (Real.exp (-w) *
          (1+w*(y:ℝ)^2)^((1:ℝ)/4)) * w^k ∂volume) := by
  have hyR : 0 ≤ (y:ℝ) := by exact_mod_cast hy
  have hyR1 : (y:ℝ) ≤ 1 := by exact_mod_cast hy1
  have hHR : 0 ≤ (H:ℝ) := by exact_mod_cast hH
  have hTail := thetaGammaWeightedTail_le_exact_exponential
    k (y:ℝ) (H:ℝ) hyR hyR1 hHR
  have hE := thetaGammaBinExpNegBox_containsReal
    H hH hHmax hExp
  let Q : ℚ :=
    thetaGammaBinPolyQ k H + (y^2/4)*thetaGammaBinPolyQ (k+1) H
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    apply add_nonneg (thetaGammaBinPolyQ_nonneg k H hH)
    exact mul_nonneg (by positivity)
      (thetaGammaBinPolyQ_nonneg (k+1) H hH)
  have hQR :
      (Q:ℝ) =
        thetaGammaBinPolyR k (H:ℝ) +
          ((y:ℝ)^2/4)*thetaGammaBinPolyR (k+1) (H:ℝ) := by
    dsimp [Q]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat, thetaGammaBinPolyQ_cast]
  have hUpper :
      (∫ w in Set.Ici (H:ℝ),
        (Real.exp (-w) *
          (1+w*(y:ℝ)^2)^((1:ℝ)/4)) * w^k ∂volume) ≤
      ((thetaGammaBinExpNegBox H).hi:ℝ) * (Q:ℝ) := by
    calc
      _ ≤ Real.exp (-(H:ℝ)) *
          (thetaGammaBinPolyR k (H:ℝ) +
            ((y:ℝ)^2/4) *
              thetaGammaBinPolyR (k+1) (H:ℝ)) := hTail
      _ = Real.exp (-(H:ℝ)) * (Q:ℝ) := by rw [hQR]
      _ ≤ ((thetaGammaBinExpNegBox H).hi:ℝ) * (Q:ℝ) :=
        mul_le_mul_of_nonneg_right hE.2 (by exact_mod_cast hQ)
  have hLower :
      (0:ℝ) ≤
      (∫ w in Set.Ici (H:ℝ),
        (Real.exp (-w) *
          (1+w*(y:ℝ)^2)^((1:ℝ)/4)) * w^k ∂volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hw0 : 0 ≤ w := hHR.trans hw
    have hbase : 0 ≤ 1+w*(y:ℝ)^2 := by positivity
    exact mul_nonneg
      (mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg hbase _))
      (pow_nonneg hw0 k)
  constructor
  · simpa [thetaGammaWeightedExactTailBox] using hLower
  · simpa [thetaGammaWeightedExactTailBox, Q, Rat.cast_mul] using hUpper

end W5
