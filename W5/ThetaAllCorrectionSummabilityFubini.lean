import W5.ThetaAllCoefficientPolynomialLocalSeparation
import W5.ThetaAllCoefficientGenericSplitting
import W5.ThetaSeparableFubini

/-!
# Separate summability of ALL 25 original numerical theta corrections

The original B_ij integral corrections have, for n≥1, weight

 (x²/4) exp(-(n²-1)/x²) exp(-w) (1+w*x²/n²)^(1/4)
          B_ij((n²-1)/x+wx, n²+wx²).

Our earlier certified zeroth-Gaussian-jet bound and the new
ALL-i,j degree-eight polynomial bound majorize this by ONE
product of a summable n-index factor and an integrable
w-tail factor. We use the EXISTING fully proved generic
separable-bound Fubini theorem to deduce individual
correction summability for EVERY i,j:Fin5 simultaneously.

All operations are actual Bochner/Lebesgue integrals
and summable Mathlib infinite series. In particular this
module does NOT assume a sum/integral exchange, does
NOT introduce a new axiom and does NOT claim determinant
positivity or thetaTransformCorrect.
-/

namespace W5
open MeasureTheory

/-- Original numerical correction integrand, including the
outer x²/4 and n-index Gaussian. Its zero-square-index
contribution is exactly zero. -/
noncomputable def thetaCertificateCorrectionIntegrand
    (x : ℝ) (i j : Fin 5) (n : ℕ) (w : ℝ) : ℝ :=
  if n = 0 then 0 else
    let p : ℝ := (n:ℝ)^2
    let d0 : ℝ := (p-1)/x
    ((x^2/4) * Real.exp (-(p-1)/x^2)) *
      (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
        coefficientPolynomial i j (d0+w*x) (p+w*x^2))

/-- The generic correction integrand is exactly the TRUE
zeroth weighted Gaussian jet times the original coefficient
polynomial (including the zero index). -/
theorem thetaCertificateCorrectionIntegrand_eq_zero_jet
    (x : ℝ) (i j : Fin 5) (n : ℕ) (w : ℝ) :
    thetaCertificateCorrectionIntegrand x i j n w =
      (x^2/4) *
        thetaHigherRightJetSeriesTerm 0 x 0 0 n w *
          coefficientPolynomial i j
            (((n:ℝ)^2-1)/x+w*x) (((n:ℝ)^2)+w*x^2) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionIntegrand, thetaHigherRightJetSeriesTerm]
  · simp only [thetaCertificateCorrectionIntegrand,
      thetaHigherRightJetSeriesTerm, if_neg hn]
    dsimp [thetaWeightedGaussianRightJet,
      thetaWeightedGaussianIntegrand, thetaGaussianModel]
    simp only [pow_zero, one_mul, mul_zero, add_zero,
      zero_add, sub_zero, Real.exp_zero, mul_one]
    ring

/-- The original correction is literally the true Lebesgue
integral of the corresponding weighted coefficient integrand.
In particular we use Mathlib's equality of the Ici and Ioi
integrals at zero, not a heuristic improper-integral rewrite. -/
theorem thetaCertificateCorrectionTerm_eq_integral
    (x : ℝ) (i j : Fin 5) (n : ℕ) :
    thetaCertificateCorrectionTerm x i j n =
      ∫ w : ℝ, thetaCertificateCorrectionIntegrand x i j n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionTerm,
      thetaCertificateCorrectionIntegrand]
  · simp only [thetaCertificateCorrectionTerm,
      thetaCertificateCorrectionIntegrand, if_neg hn]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [integral_const_mul]
    ring

/-- An explicit, entirely summable n-dependent envelope:
the n-factor grows only as (n²+1)^9, dominated by exp(-47 n²/64).
Every i,j coefficient is controlled by the same Gaussian tail. -/
noncomputable def thetaCertificateCorrectionIndexFactor
    (x : ℝ) (i j : Fin 5) (n : ℕ) : ℝ :=
  ((x^2/4) * thetaCoefficientAbsoluteWeight i j *
    (1/x+4)^8 * Real.exp (3/4)) *
      (((n:ℝ)^2+1)^9 *
        Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))

/-- Mathlib's existing polynomial-Gaussian summability
closes the n-side of the separator, uniformly for all 25
coefficient indices. -/
theorem thetaCertificateCorrectionIndexFactor_summable
    (x : ℝ) (i j : Fin 5) :
    Summable (thetaCertificateCorrectionIndexFactor x i j) := by
  change Summable (fun n : ℕ =>
    ((x^2/4) * thetaCoefficientAbsoluteWeight i j *
      (1/x+4)^8 * Real.exp (3/4)) *
        (((n:ℝ)^2+1)^9 *
          Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)))
  exact (thetaHigherJet_shifted_index_summable 9).mul_left _

/-- The original correction integrand has a single separable
Gaussian/exponential envelope, for ALL original indices
i,j:Fin5, all 0<x≤1, n≥0 and w≥0. -/
theorem thetaCertificateCorrectionIntegrand_norm_le
    (x : ℝ) (i j : Fin 5) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hw : 0 ≤ w) :
    ‖thetaCertificateCorrectionIntegrand x i j n w‖ ≤
      thetaCertificateCorrectionIndexFactor x i j n *
        thetaHigherJetTailFactor 8 w := by
  have htail : 0 ≤ thetaHigherJetTailFactor 8 w := by
    unfold thetaHigherJetTailFactor
    positivity
  have hweight : 0 ≤ thetaCoefficientAbsoluteWeight i j :=
    thetaCoefficientAbsoluteWeight_nonneg i j
  have hD : 0 ≤ (1/x+4)^8 := by positivity
  by_cases hn : n = 0
  · subst n
    have hind : 0 ≤ thetaCertificateCorrectionIndexFactor x i j 0 := by
      unfold thetaCertificateCorrectionIndexFactor
      positivity
    simpa [thetaCertificateCorrectionIntegrand] using
      (mul_nonneg hind htail)
  · have hn1 : 1 ≤ n := by omega
    have hnr : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have hp : (1:ℝ) ≤ (n:ℝ)^2 := by nlinarith
    have hz : |(0:ℝ)| ≤ x/8 := by
      simp only [abs_zero]
      positivity
    have hzero := thetaHigherRightJetSeriesTerm_norm_le
      0 x 0 0 n w hx hx1 hz hz hw
    have hcoeff := coefficientPolynomial_theta_arguments_separable
      i j x ((n:ℝ)^2) w hx hx1 hp hw
    have hK : 0 ≤ x^2/4 := by positivity
    have hI : 0 ≤ thetaHigherJetIndexFactor 0 x n := by
      unfold thetaHigherJetIndexFactor
      positivity
    have hT : 0 ≤ thetaHigherJetTailFactor 0 w := by
      unfold thetaHigherJetTailFactor
      positivity
    have hp1 : 0 ≤ ((n:ℝ)^2+1)^8 := by positivity
    have hw1 : 0 ≤ (w+1)^8 := by positivity
    have hpolyR : 0 ≤
        thetaCoefficientAbsoluteWeight i j *
          ((1/x+4)^8 * ((n:ℝ)^2+1)^8 * (w+1)^8) := by
      positivity
    rw [thetaCertificateCorrectionIntegrand_eq_zero_jet]
    calc
      ‖(x^2/4) * thetaHigherRightJetSeriesTerm 0 x 0 0 n w *
          coefficientPolynomial i j
            (((n:ℝ)^2-1)/x+w*x) (((n:ℝ)^2)+w*x^2)‖ =
        (x^2/4) *
          ‖thetaHigherRightJetSeriesTerm 0 x 0 0 n w‖ *
          |coefficientPolynomial i j
            (((n:ℝ)^2-1)/x+w*x) (((n:ℝ)^2)+w*x^2)| := by
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hK]
      _ ≤ (x^2/4) *
          (thetaHigherJetIndexFactor 0 x n *
            thetaHigherJetTailFactor 0 w) *
          (thetaCoefficientAbsoluteWeight i j *
            ((1/x+4)^8 * ((n:ℝ)^2+1)^8 * (w+1)^8)) := by
        gcongr
      _ = thetaCertificateCorrectionIndexFactor x i j n *
            thetaHigherJetTailFactor 8 w := by
        dsimp [thetaCertificateCorrectionIndexFactor,
          thetaHigherJetIndexFactor, thetaHigherJetTailFactor]
        simp only [pow_zero, pow_one, one_mul, zero_add]
        ring

/-- The actual original correction integrand is measurable
as a function of the positive-half-line Lebesgue variable,
using the existing measured zero theta jet and the finite
polynomial coefficient. -/
theorem thetaCertificateCorrectionIntegrand_measurable
    (x : ℝ) (i j : Fin 5) (n : ℕ) :
    Measurable (thetaCertificateCorrectionIntegrand x i j n) := by
  have hpoly : Measurable (fun w : ℝ =>
      coefficientPolynomial i j
        (((n:ℝ)^2-1)/x+w*x) (((n:ℝ)^2)+w*x^2)) := by
    unfold coefficientPolynomial
    fun_prop
  have hjet := thetaHigherRightJetSeriesTerm_measurable 0 x 0 0 n
  have h := (measurable_const.mul hjet).mul hpoly
  convert h using 1
  funext w
  exact thetaCertificateCorrectionIntegrand_eq_zero_jet x i j n w

/-- The EXISTING generic separable-bound Fubini theorem now
applies to the original numerical correction integrands
for ALL 25 entries, with no new Fubini proof. -/
theorem thetaCertificateCorrectionIntegrand_integral_hasSum
    (x : ℝ) (i j : Fin 5) (hx : 0 < x) (hx1 : x ≤ 1) :
    HasSum
      (fun n : ℕ =>
        ∫ w : ℝ, thetaCertificateCorrectionIntegrand x i j n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))
      (∫ w : ℝ, ∑' n : ℕ,
        thetaCertificateCorrectionIntegrand x i j n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let a := thetaCertificateCorrectionIndexFactor x i j
  let b := thetaHigherJetTailFactor 8
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hA : Summable a :=
    thetaCertificateCorrectionIndexFactor_summable x i j
  have hB : Integrable b μ := thetaHigherJet_full_w_factor_integrableOn 8
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable
        (thetaCertificateCorrectionIntegrand x i j n) μ := by
    intro n
    exact (thetaCertificateCorrectionIntegrand_measurable
      x i j n).aestronglyMeasurable
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ∀ n : ℕ,
        ‖thetaCertificateCorrectionIntegrand x i j n w‖ ≤
          a n * b w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw n
    exact thetaCertificateCorrectionIntegrand_norm_le
      x i j n w hx hx1 hw.le
  exact hasSum_integral_of_separable_bound μ
    (thetaCertificateCorrectionIntegrand x i j) a b
    hA hB hmeas hbound

/-- ALL 25 original integral correction series are separately
summable for 0<x≤1: the missing hypothesis in the generic
5x5 theta certificate decomposition from PR #83. -/
theorem thetaCertificateCorrectionTerm_all_summable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (i j : Fin 5) :
    Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x i j n) := by
  have hsum :=
    (thetaCertificateCorrectionIntegrand_integral_hasSum
      x i j hx hx1).summable
  have heq :
      (fun n : ℕ => thetaCertificateCorrectionTerm x i j n) =
      (fun n : ℕ =>
        ∫ w : ℝ, thetaCertificateCorrectionIntegrand x i j n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
    funext n
    exact thetaCertificateCorrectionTerm_eq_integral x i j n
  rw [heq]
  exact hsum

/-- The entire numerical 5x5 theta certificate is unconditionally
the difference of two separately convergent coefficient matrices
for every 0<x≤1. All 25 base series and all 25 correction
series have now been proved summable, rather than assumed. -/
theorem thetaMatrixFive_eq_separately_summable_base_sub_correction
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Matrix.of (fun i j : Fin 5 => thetaCoefficient x i j) =
      Matrix.of (fun i j : Fin 5 =>
        (∑' n : ℕ, thetaCertificateBaseTerm x i j n) -
        (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n)) := by
  exact thetaMatrixFive_eq_base_sub_correction x hx
    (fun i j => thetaCertificateCorrectionTerm_all_summable x hx hx1 i j)

end W5
