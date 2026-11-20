import W5.ThetaB11BaseAndCorrectionSummability

/-!
# Full first off-diagonal theta coefficients: B10 and B01

For the independent theta certificate, both off-diagonal
polynomials are B10(d,q)=B01(d,q)=-d. We prove that the genuine
square-index elementary Gaussian part is summable, and the
numerical integral correction is also summable by its exact
identification with the first left derivative of the full
transformed Gaussian integrated series.

After legitimate separation of the original tsum, coefficient
(1,0) is identified with the elementary base series minus
x²/4 times that genuine derivative. Symmetry of the complete
coefficient matrix and of the elementary base term gives the
same formula for coefficient (0,1), without assuming extra
differentiation or convergence.

The original normalized Nuttall kernel bridge and determinant
signs remain separate proof obligations.
-/

namespace W5
open MeasureTheory

/-- For x>0, the elementary B10 square-index series is
summable by its explicit combination of n² and n⁴ Gaussian
terms, with exponent exp(-n²/x²). -/
theorem thetaCertificateBaseTerm_one_zero_summable
    (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n) := by
  let a : ℝ := (1:ℝ)/x
  let c : ℝ := (1:ℝ)/x^2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have h2 : Summable (fun n : ℕ =>
      (n:ℝ)^2 * Real.exp (-c*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 c hc
  have h4 : Summable (fun n : ℕ =>
      (n:ℝ)^4 * Real.exp (-c*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 4 c hc
  have hpoly : Summable (fun n : ℕ =>
      (a*(n:ℝ)^2-a*(n:ℝ)^4)*
        Real.exp (-c*(n:ℝ)^2)) := by
    have heq :
        (fun n : ℕ =>
          (a*(n:ℝ)^2-a*(n:ℝ)^4)*Real.exp (-c*(n:ℝ)^2)) =
        (fun n : ℕ =>
          a*((n:ℝ)^2*Real.exp (-c*(n:ℝ)^2)) -
          a*((n:ℝ)^4*Real.exp (-c*(n:ℝ)^2))) := by
      funext n
      ring
    rw [heq]
    exact (h2.mul_left a).sub (h4.mul_left a)
  have hfun :
      (fun n : ℕ =>
        thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n) =
      (fun n : ℕ =>
        Real.exp c *
          ((a*(n:ℝ)^2-a*(n:ℝ)^4) *
            Real.exp (-c*(n:ℝ)^2))) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [thetaCertificateBaseTerm]
    · simp only [thetaCertificateBaseTerm, if_neg hn,
        coefficientPolynomial_one_zero]
      have hexp :
          Real.exp (-((n:ℝ)^2-1)/x^2) =
          Real.exp c * Real.exp (-c*(n:ℝ)^2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [c]
        ring
      rw [hexp]
      dsimp [a, c]
      ring
  rw [hfun]
  exact hpoly.mul_left (Real.exp c)

/-- The original B10 correction is exactly x²/4 times the genuine
first-left Gaussian mixed jet, integrated over the positive
Lebesgue half-line, including the zero-index term. -/
theorem thetaCertificateCorrectionTerm_one_zero_eq_mixed_integral
    (x : ℝ) (n : ℕ) :
    thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n =
      (x^2/4) *
        (∫ w : ℝ,
          thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionTerm, thetaMixedOneRightJetSeriesTerm]
  · have hfunc :
        (fun w : ℝ => thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w) =
        (fun w : ℝ =>
          let p : ℝ := (n:ℝ)^2
          let d0 : ℝ := (p-1)/x
          Real.exp (-(p-1)/x^2) *
            (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
              coefficientPolynomial (1:Fin 5) (0:Fin 5)
                (d0+w*x) (p+w*x^2))) := by
      funext w
      simpa only [if_neg hn] using
        (thetaMixedOneRightJetSeriesTerm_zero_zero_eq_B10 x n w)
    simp only [thetaCertificateCorrectionTerm, if_neg hn]
    rw [hfunc]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    rw [integral_const_mul]
    ring

/-- The B10 correction series is independently summable by the
verified mixed-jet Fubini theorem at right order k=0. -/
theorem thetaCertificateCorrectionTerm_one_zero_summable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hjet : Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) :=
    (thetaMixedOneRightJetSeries_integral_hasSum
      0 x 0 0 hx hx1 hz hz).summable
  have hfun :
      (fun n : ℕ =>
        thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n) =
      (fun n : ℕ =>
        (x^2/4) *
          (∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
    funext n
    exact thetaCertificateCorrectionTerm_one_zero_eq_mixed_integral x n
  rw [hfun]
  exact hjet.mul_left (x^2/4)

/-- The full infinite B10 integral correction equals x²/4
times the GENUINE first left derivative of the entire integrated
transformed theta Gaussian square-index series. -/
theorem thetaCertificateCorrectionSeries_one_zero_eq_actual_derivative
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n) =
      (x^2/4) *
        deriv (fun z : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hpatch := thetaGaussianSummableRightPatch_origin x hx
  have hFubini := (thetaMixedOneRightJetSeries_integral_hasSum
    0 x 0 0 hx hx1 hz hz).tsum_eq
  have hderiv := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    0 x 0 0 hx hx1 hpatch hpatch
  simp only [iteratedDeriv_zero] at hderiv
  have hsum :
      (∑' n : ℕ,
        ∫ w : ℝ,
          thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) =
      deriv (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 :=
    hFubini.trans hderiv.symm
  calc
    (∑' n : ℕ,
      thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n) =
      (∑' n : ℕ,
        (x^2/4) *
          (∫ w : ℝ,
            thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
            ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
      apply tsum_congr
      intro n
      exact thetaCertificateCorrectionTerm_one_zero_eq_mixed_integral x n
    _ = (x^2/4) * (∑' n : ℕ,
          ∫ w : ℝ,
            thetaMixedOneRightJetSeriesTerm 0 x 0 0 n w
              ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      rw [tsum_mul_left]
    _ = _ := congrArg (fun z : ℝ => (x^2/4) * z) hsum

/-- The complete B10 coefficient equals the separately summable
elementary Gaussian series minus x²/4 times the actual full
theta series first left derivative at the origin. -/
theorem thetaCoefficient_one_zero_eq_base_minus_actual_left_derivative
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x (1:Fin 5) (0:Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n) -
      (x^2/4) *
        deriv (fun z : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 := by
  have hb := thetaCertificateBaseTerm_one_zero_summable x hx
  have hc := thetaCertificateCorrectionTerm_one_zero_summable x hx hx1
  calc
    thetaCoefficient x (1:Fin 5) (0:Fin 5) =
        ∑' n : ℕ,
          (thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n -
            thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n) :=
      thetaCoefficient_eq_tsum_base_sub_correction x 1 0
    _ = (∑' n : ℕ,
          thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n) -
        (∑' n : ℕ,
          thetaCertificateCorrectionTerm x (1:Fin 5) (0:Fin 5) n) :=
      (hb.hasSum.sub hc.hasSum).tsum_eq
    _ = _ := by
      rw [thetaCertificateCorrectionSeries_one_zero_eq_actual_derivative
        x hx hx1]

/-- B01 and B10 elementary certificate base terms coincide for
every square index, by the exact polynomial symmetry, including
index zero. -/
theorem thetaCertificateBaseTerm_zero_one_eq_one_zero
    (x : ℝ) (n : ℕ) :
    thetaCertificateBaseTerm x (0:Fin 5) (1:Fin 5) n =
      thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateBaseTerm]
  · simp only [thetaCertificateBaseTerm, if_neg hn]
    rw [coefficientPolynomial_symmetric (0:Fin 5) (1:Fin 5)]

/-- The complete B01 coefficient has the same rigorous
base-minus-genuine-derivative decomposition as B10.
No second differentiation-through-series argument is needed:
the proved certificate symmetry handles the other orientation. -/
theorem thetaCoefficient_zero_one_eq_base_minus_actual_left_derivative
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x (0:Fin 5) (1:Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (0:Fin 5) (1:Fin 5) n) -
      (x^2/4) *
        deriv (fun z : ℝ =>
          ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 := by
  have hbase :
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (0:Fin 5) (1:Fin 5) n) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n) := by
    apply tsum_congr
    intro n
    exact thetaCertificateBaseTerm_zero_one_eq_one_zero x n
  calc
    thetaCoefficient x (0:Fin 5) (1:Fin 5) =
        thetaCoefficient x (1:Fin 5) (0:Fin 5) :=
      thetaCoefficient_symmetric x 0 1
    _ = (∑' n : ℕ,
          thetaCertificateBaseTerm x (1:Fin 5) (0:Fin 5) n) -
        (x^2/4) *
          deriv (fun z : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0 :=
      thetaCoefficient_one_zero_eq_base_minus_actual_left_derivative
        x hx hx1
    _ = _ := by rw [← hbase]

end W5
