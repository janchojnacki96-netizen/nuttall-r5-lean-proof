import W5.ThetaGammaSignedPolynomialBin
import W5.ThetaGammaRecenteredSignedPolynomial

/-!
# One certified signed-polynomial Gamma evaluator for ALL moment shifts

The recentered fourth-root lower/upper envelopes are degree 2 and 3
polynomials in w, but each actual theta moment carries an additional w^k
with k = 0,...,8. Rather than constructing a separate polynomial or
integration proof for each k, shift the Gamma moments by k once.

This module composes the already verified QInterval signed finite-sum
semantics and the certified real Gamma-bin masses. The only real-analytic
step is Mathlib's intervalIntegral.integral_finsetSum/const_mul.
The formula and enclosure are uniform in k, N, the signs of c, and
the rational integration endpoints. Numerical sharpness remains open.
-/

namespace W5

/-- Exact rational interval for a polynomial with signed coefficients
multiplied by the original gamma density exp(-w) * w^k. -/
def thetaGammaShiftedSignedBinBox
    (k N : ℕ) (c : Fin N → ℚ) (L U : ℚ) : QInterval :=
  QInterval.finsetSum (Finset.univ : Finset (Fin N))
    (fun i => QInterval.mul (QInterval.point (c i))
      (thetaGammaCertifiedBinMassBox (k + i.val) L U))

/-- The corresponding exact real finite sum of genuine Gamma-bin
integrals, preserving all signs of the polynomial coefficients. -/
noncomputable def thetaGammaShiftedSignedBinReal
    (k N : ℕ) (c : Fin N → ℚ) (L U : ℚ) : ℝ :=
  ∑ i : Fin N, (c i : ℝ) *
    (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^(k + i.val))

/-- Reuse existing rational interval multiplication, signed sum and
certified Gamma mass: this is exact for every moment shift. -/
theorem thetaGammaShiftedSignedBinBox_containsReal_sum
    (k N : ℕ) (c : Fin N → ℚ) (L U : ℚ)
    (h : thetaGammaCertifiedBinEligible L U) :
    QInterval.ContainsReal
      (thetaGammaShiftedSignedBinBox k N c L U)
      (thetaGammaShiftedSignedBinReal k N c L U) := by
  unfold thetaGammaShiftedSignedBinBox thetaGammaShiftedSignedBinReal
  apply QInterval.finsetSum_containsReal
    (Finset.univ : Finset (Fin N))
    (fun i => QInterval.mul (QInterval.point (c i))
      (thetaGammaCertifiedBinMassBox (k + i.val) L U))
    (fun i => (c i : ℝ) *
      (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^(k + i.val)))
  intro i _
  exact QInterval.mul_containsReal
    (thetaRationalPoint_containsReal (c i))
    (thetaGammaCertifiedBinMassBox_containsReal (k + i.val) L U h)

/-- Uniform polynomial identity, including the theta w^k weight.
No positivity assumptions are needed: the signed factor is retained. -/
theorem thetaGammaShiftedSignedBin_integrand
    (k N : ℕ) (c : Fin N → ℚ) (w : ℝ) :
    thetaGammaBinDensity k w *
        (∑ i : Fin N, (c i : ℝ) * w^i.val) =
      ∑ i : Fin N, (c i : ℝ) *
        (Real.exp (-w) * w^(k + i.val)) := by
  unfold thetaGammaBinDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

/-- The exact signed moment sum equals the TRUE weighted polynomial
integral, for arbitrary k and polynomial degree N. -/
theorem thetaGammaShiftedSignedBinReal_eq_integral
    (k N : ℕ) (c : Fin N → ℚ) (L U : ℚ) :
    thetaGammaShiftedSignedBinReal k N c L U =
      (∫ w in (L:ℝ)..(U:ℝ),
        thetaGammaBinDensity k w *
          (∑ i : Fin N, (c i : ℝ) * w^i.val)) := by
  have hCont (i : Fin N) :
      Continuous (fun w : ℝ =>
        (c i : ℝ) * (Real.exp (-w) * w^(k + i.val))) := by
    fun_prop
  have hSum :
      (∫ w in (L:ℝ)..(U:ℝ),
         ∑ i : Fin N, (c i : ℝ) *
           (Real.exp (-w) * w^(k + i.val))) =
        thetaGammaShiftedSignedBinReal k N c L U := by
    calc
      (∫ w in (L:ℝ)..(U:ℝ),
         ∑ i : Fin N, (c i : ℝ) *
           (Real.exp (-w) * w^(k + i.val))) =
        ∑ i : Fin N,
          (∫ w in (L:ℝ)..(U:ℝ),
            (c i : ℝ) * (Real.exp (-w) * w^(k + i.val))) := by
        exact intervalIntegral.integral_finsetSum
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
            (hCont i).intervalIntegrable (L:ℝ) (U:ℝ))
      _ = thetaGammaShiftedSignedBinReal k N c L U := by
        unfold thetaGammaShiftedSignedBinReal
        apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_const_mul]
  calc
    thetaGammaShiftedSignedBinReal k N c L U =
        (∫ w in (L:ℝ)..(U:ℝ),
          ∑ i : Fin N, (c i : ℝ) *
            (Real.exp (-w) * w^(k + i.val))) := hSum.symm
    _ = (∫ w in (L:ℝ)..(U:ℝ),
        thetaGammaBinDensity k w *
          (∑ i : Fin N, (c i : ℝ) * w^i.val)) := by
      congr 1
      funext w
      exact (thetaGammaShiftedSignedBin_integrand k N c w).symm

/-- A single REAL containment result for every signed weighted gamma
polynomial on every eligible rational integration bin. -/
theorem thetaGammaShiftedSignedBinBox_containsReal_integral
    (k N : ℕ) (c : Fin N → ℚ) (L U : ℚ)
    (h : thetaGammaCertifiedBinEligible L U) :
    QInterval.ContainsReal
      (thetaGammaShiftedSignedBinBox k N c L U)
      (∫ w in (L:ℝ)..(U:ℝ),
        thetaGammaBinDensity k w *
          (∑ i : Fin N, (c i : ℝ) * w^i.val)) := by
  rw [← thetaGammaShiftedSignedBinReal_eq_integral]
  exact thetaGammaShiftedSignedBinBox_containsReal_sum k N c L U h

end W5
