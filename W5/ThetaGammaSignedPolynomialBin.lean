import W5.ThetaGammaCertifiedBinMass
import W5.ThetaFiniteTermIntervalFold
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# One signed polynomial Γ-bin interval generator, for arbitrary degree

The true theta entry corrections involve degree ≤8 polynomials with
many alternating signs. Earlier positive majorants lost the
cancellation and were too wide; instead retain ALL polynomial
coefficient signs and call the *same* generic certified incomplete
Gamma mass box for every monomial.

This module proves:
* Mathlib's finite-interval integral of any signed rational
  polynomial times exp(-w) is its exact coefficient-weighted Γ sum.
* The executable QInterval obtained by the existing signed
  interval multiplication/sum contains that true real integral.
* All k and bin endpoints share one theorem; only a *single*
  decidable rational bin-eligibility check remains.

Later, apply this to the already CI-green quadratic/cubic recentered
fourth-root envelopes for the original theta weighted moments.
No claim yet that a 48-cell generated LDL checker returns true.
-/

namespace W5

/-- Exact-rational interval evaluation of a signed finite
coefficient vector against the certified Gamma bin moments. -/
def thetaGammaSignedPolynomialBinBox (N : ℕ)
    (c : Fin N → ℚ) (L U : ℚ) : QInterval :=
  QInterval.finsetSum (Finset.univ : Finset (Fin N))
    (fun i => QInterval.mul (QInterval.point (c i))
      (thetaGammaCertifiedBinMassBox i.val L U))

/-- The real finite signed Gamma combination which is exactly
the integral of the corresponding polynomial. -/
noncomputable def thetaGammaSignedPolynomialBinReal (N : ℕ)
    (c : Fin N → ℚ) (L U : ℚ) : ℝ :=
  ∑ i : Fin N, (c i : ℝ) *
    (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^i.val)

/-- Reuse the already-proven real-semantic QInterval multiplication
and finite sum: this handles *all signs*, so cancellation is kept. -/
theorem thetaGammaSignedPolynomialBinBox_containsReal_sum
    (N : ℕ) (c : Fin N → ℚ) (L U : ℚ)
    (h : thetaGammaCertifiedBinEligible L U) :
    QInterval.ContainsReal
      (thetaGammaSignedPolynomialBinBox N c L U)
      (thetaGammaSignedPolynomialBinReal N c L U) := by
  unfold thetaGammaSignedPolynomialBinBox
    thetaGammaSignedPolynomialBinReal
  apply QInterval.finsetSum_containsReal
    (Finset.univ : Finset (Fin N))
    (fun i => QInterval.mul (QInterval.point (c i))
      (thetaGammaCertifiedBinMassBox i.val L U))
    (fun i => (c i : ℝ) *
      (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^i.val))
  intro i _
  exact QInterval.mul_containsReal
    (thetaRationalPoint_containsReal (c i))
    (thetaGammaCertifiedBinMassBox_containsReal i.val L U h)

/-- Exactly the Mathlib intervalIntegral.finsetSum identity for an
ARBITRARY signed polynomial, with no assumption on coefficient
signs and no arbitrary numerical integration. -/
theorem thetaGammaSignedPolynomialBinReal_eq_integral
    (N : ℕ) (c : Fin N → ℚ) (L U : ℚ) :
    thetaGammaSignedPolynomialBinReal N c L U =
    (∫ w in (L:ℝ)..(U:ℝ),
       ∑ i : Fin N, (c i : ℝ) * (Real.exp (-w) * w^i.val)) := by
  have hCont (i : Fin N) :
      Continuous (fun w : ℝ =>
        (c i : ℝ) * (Real.exp (-w) * w^i.val)) := by
    fun_prop
  have hEq :
      (∫ w in (L:ℝ)..(U:ℝ),
        ∑ i : Fin N, (c i : ℝ) * (Real.exp (-w) * w^i.val)) =
      ∑ i : Fin N, (c i : ℝ) *
        (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^i.val) := by
    calc
      (∫ w in (L:ℝ)..(U:ℝ),
        ∑ i : Fin N, (c i : ℝ) * (Real.exp (-w) * w^i.val)) =
          ∑ i : Fin N,
            (∫ w in (L:ℝ)..(U:ℝ),
              (c i : ℝ) * (Real.exp (-w) * w^i.val)) := by
        exact intervalIntegral.integral_finsetSum
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
            (hCont i).intervalIntegrable (L:ℝ) (U:ℝ))
      _ = ∑ i : Fin N, (c i : ℝ) *
          (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^i.val) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_const_mul]
  exact hEq.symm

/-- The ONE computationally certified real enclosure of a true
weighted signed polynomial Gamma integral. Every desired
recentered θ moment polynomial will instantiate c. -/
theorem thetaGammaSignedPolynomialBinBox_containsReal_integral
    (N : ℕ) (c : Fin N → ℚ) (L U : ℚ)
    (h : thetaGammaCertifiedBinEligible L U) :
    QInterval.ContainsReal
      (thetaGammaSignedPolynomialBinBox N c L U)
      (∫ w in (L:ℝ)..(U:ℝ),
         ∑ i : Fin N, (c i : ℝ) * (Real.exp (-w) * w^i.val)) := by
  rw [← thetaGammaSignedPolynomialBinReal_eq_integral]
  exact thetaGammaSignedPolynomialBinBox_containsReal_sum N c L U h

end W5
