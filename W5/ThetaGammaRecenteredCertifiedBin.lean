import W5.ThetaGammaSignedShiftedBin
import W5.ThetaGammaRationalFourthRootBounds

/-!
# Certified REAL single-bin recentered theta Gamma integrals

This is the direct numerical soundness bridge between:
* the proven local quadratic/cubic fourth-root envelopes;
* rational fourth-root endpoint enclosures;
* the signed, shifted Gamma moment interval evaluator.

The only hypotheses are exact rational endpoint/eligibility checks and
nonnegativity of the original q and bin origin L. The code reuses the
existing Mathlib integral factorization and QInterval.mul_containsReal.
No floating-point oracle or per-cell / per-moment theorems.
-/

namespace W5

/-- A REAL moment's locally recentered lower-root integral, bounded by
the certified root of A=1+qL and signed quadratic Gamma moments. -/
def thetaGammaLowerRootSignedBinBox
    (k : ℕ) (q L U l u : ℚ) : QInterval :=
  QInterval.mul (⟨l,u⟩ : QInterval)
    (thetaGammaShiftedSignedBinBox k 3
      (thetaGammaRecenteredLowerCoeffs (q/(1+q*L)) L) L U)

/-- Analogue with the signed cubic upper envelope. -/
def thetaGammaUpperRootSignedBinBox
    (k : ℕ) (q L U l u : ℚ) : QInterval :=
  QInterval.mul (⟨l,u⟩ : QInterval)
    (thetaGammaShiftedSignedBinBox k 4
      (thetaGammaRecenteredUpperCoeffs (q/(1+q*L)) L) L U)

/-- Cast the EXACT rational recentered parameter; this is the same
parameter used in the already proved real fourth-root factorization. -/
theorem thetaGammaBinRatio_cast (q L : ℚ) :
    ((q/(1+q*L):ℚ):ℝ) =
      (q:ℝ) / thetaGammaBinBase (q:ℝ) (L:ℝ) := by
  simp [thetaGammaBinBase, Rat.cast_div, Rat.cast_add, Rat.cast_mul]

/-- Uniform real-sound enclosure of the LOWER original theta
recentered Gamma integral. All signed polynomial coefficients
are retained, and the fourth-root factor is a separately certified
rational interval. -/
theorem thetaGammaLowerRootSignedBinBox_containsReal
    (k : ℕ) (q L U l u : ℚ)
    (hq : 0 ≤ q) (hL : 0 ≤ L)
    (hEligible : thetaGammaCertifiedBinEligible L U)
    (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : l^4 ≤ 1+q*L) (hhi : 1+q*L ≤ u^4) :
    QInterval.ContainsReal
      (thetaGammaLowerRootSignedBinBox k q L U l u)
      (∫ w in (L:ℝ)..(U:ℝ),
        thetaGammaBinDensity k w *
          thetaGammaBinLowerRoot (q:ℝ) (L:ℝ) w) := by
  have hbase : 0 ≤ 1+q*L := by
    nlinarith [mul_nonneg hq hL]
  have hRoot :
      QInterval.ContainsReal (⟨l,u⟩:QInterval)
        ((thetaGammaBinBase (q:ℝ) (L:ℝ))^((1:ℝ)/4)) := by
    simpa [thetaGammaBinBase, Rat.cast_add, Rat.cast_mul] using
      (thetaFourthRoot_rational_arg_box_containsReal
        (1+q*L) l u hbase hl hu hlo hhi)
  have hPoly :=
    thetaGammaRecenteredLowerPoly_weighted_containsReal
      k (q/(1+q*L)) L U hEligible
  rw [thetaGammaBinRatio_cast q L] at hPoly
  have hMul := QInterval.mul_containsReal hRoot hPoly
  unfold thetaGammaLowerRootSignedBinBox
  rw [thetaGammaBinLowerWeightedIntegral_eq_signed_poly]
  exact hMul

/-- Same REAL containment result for the UPPER original
theta recentered Gamma integral, with a signed cubic. -/
theorem thetaGammaUpperRootSignedBinBox_containsReal
    (k : ℕ) (q L U l u : ℚ)
    (hq : 0 ≤ q) (hL : 0 ≤ L)
    (hEligible : thetaGammaCertifiedBinEligible L U)
    (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : l^4 ≤ 1+q*L) (hhi : 1+q*L ≤ u^4) :
    QInterval.ContainsReal
      (thetaGammaUpperRootSignedBinBox k q L U l u)
      (∫ w in (L:ℝ)..(U:ℝ),
        thetaGammaBinDensity k w *
          thetaGammaBinUpperRoot (q:ℝ) (L:ℝ) w) := by
  have hbase : 0 ≤ 1+q*L := by
    nlinarith [mul_nonneg hq hL]
  have hRoot :
      QInterval.ContainsReal (⟨l,u⟩:QInterval)
        ((thetaGammaBinBase (q:ℝ) (L:ℝ))^((1:ℝ)/4)) := by
    simpa [thetaGammaBinBase, Rat.cast_add, Rat.cast_mul] using
      (thetaFourthRoot_rational_arg_box_containsReal
        (1+q*L) l u hbase hl hu hlo hhi)
  have hPoly :=
    thetaGammaRecenteredUpperPoly_weighted_containsReal
      k (q/(1+q*L)) L U hEligible
  rw [thetaGammaBinRatio_cast q L] at hPoly
  have hMul := QInterval.mul_containsReal hRoot hPoly
  unfold thetaGammaUpperRootSignedBinBox
  rw [thetaGammaBinUpperWeightedIntegral_eq_signed_poly]
  exact hMul

end W5
