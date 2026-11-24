import W5.ThetaActualZeroZeroCoefficientBridge

/-!
# Separate the algebraic square-index term and integral correction

The independent theta coefficient is defined by

  p * exp(-(p-1)/x²) * (B_ij(d0,p) - x²/(4p) * ∫ weight*B_ij)

with p=n², n>0.

For the eventual analytic-coefficient bridge, the cancellation
p * (x²/(4p)) = x²/4 is crucial: the correction factor is
INDEPENDENT of the square index. We formalize this cancellation
unconditionally for all 25 entries i,j:Fin 5.

We prove equality of the original infinite series with the
single infinite sum of base-minus-correction terms, without
splitting the infinite sum into two unless their individual
summability is also established. Thus no illicit tsum
distributivity is used. We do not assert equality with
normalizedKernel or a determinant sign.
-/

namespace W5

open MeasureTheory

/-- Unintegrated elementary n-th theta coefficient contribution. -/
noncomputable def thetaCertificateBaseTerm
    (x : ℝ) (i j : Fin 5) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    let p : ℝ := (n:ℝ)^2
    let d0 : ℝ := (p-1)/x
    p * Real.exp (-(p-1)/x^2) * coefficientPolynomial i j d0 p

/-- Integrated correction, with the cancellation of 1/p explicit.
The integral here matches the original coefficient's measure. -/
noncomputable def thetaCertificateCorrectionTerm
    (x : ℝ) (i j : Fin 5) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    let p : ℝ := (n:ℝ)^2
    let d0 : ℝ := (p-1)/x
    (x^2/4) * Real.exp (-(p-1)/x^2) *
      (∫ w in Set.Ici (0:ℝ),
        Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          coefficientPolynomial i j (d0+w*x) (p+w*x^2)
        ∂volume)

/-- Pure algebra: the n² in front of the original coefficient
exactly cancels the n² in the correction denominator.
No assumption on x or convergence is involved. -/
theorem thetaCoefficient_cancel_square_index
    (x p E B I : ℝ) (hp : p ≠ 0) :
    p*E*(B - x^2/(4*p)*I) =
      p*E*B - (x^2/4)*E*I := by
  have hcancel : p*(x^2/(4*p)) = x^2/4 := by
    field_simp [hp] <;> ring
  calc
    p*E*(B - x^2/(4*p)*I) =
      p*E*B - (p*(x^2/(4*p)))*E*I := by ring
    _ = p*E*B - (x^2/4)*E*I := by rw [hcancel]

/-- Rewriting each ORIGINAL theta coefficient summand as
unintegrated base minus the common-factor integral correction. -/
theorem thetaCoefficient_term_eq_base_sub_correction
    (x : ℝ) (i j : Fin 5) (n : ℕ) :
    (if n = 0 then (0:ℝ) else
      let p : ℝ := (n:ℝ)^2
      let d0 : ℝ := (p-1)/x
      let integral : ℝ :=
        ∫ w in Set.Ici (0:ℝ),
          Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial i j (d0+w*x) (p+w*x^2)
          ∂volume
      p*Real.exp (-(p-1)/x^2) *
        (coefficientPolynomial i j d0 p - x^2/(4*p)*integral)) =
    thetaCertificateBaseTerm x i j n -
      thetaCertificateCorrectionTerm x i j n := by
  by_cases hn : n = 0
  · simp [thetaCertificateBaseTerm, thetaCertificateCorrectionTerm, hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hp : ((n:ℝ)^2) ≠ 0 := by positivity
    simp only [if_neg hn, thetaCertificateBaseTerm,
      thetaCertificateCorrectionTerm]
    exact thetaCoefficient_cancel_square_index x ((n:ℝ)^2)
      (Real.exp (-((n:ℝ)^2-1)/x^2))
      (coefficientPolynomial i j (((n:ℝ)^2-1)/x) ((n:ℝ)^2))
      (∫ w in Set.Ici (0:ℝ),
        Real.exp (-w) * (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
          coefficientPolynomial i j
            ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)
        ∂volume) hp

/-- Exact algebraic decomposition of ALL 25 original theta
coefficients, retaining one infinite sum and hence requiring
no nontrivial convergence or difference-of-tsums assumption. -/
theorem thetaCoefficient_eq_tsum_base_sub_correction
    (x : ℝ) (i j : Fin 5) :
    thetaCoefficient x i j =
      ∑' n : ℕ,
        (thetaCertificateBaseTerm x i j n -
          thetaCertificateCorrectionTerm x i j n) := by
  unfold thetaCoefficient
  apply tsum_congr
  intro n
  exact thetaCoefficient_term_eq_base_sub_correction x i j n

end W5
