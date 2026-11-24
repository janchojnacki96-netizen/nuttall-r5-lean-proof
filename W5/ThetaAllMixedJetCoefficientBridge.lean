import W5.ThetaGenericAffineExpMixedJets
import W5.ThetaAllMixedWeightedJetRecurrence
import W5.ThetaAllCorrectionSummabilityFubini
import W5.ThetaOriginalKernelExistingIntegratedSeries

/-!
Exact algebraic bridge between the verified affine exponential
recurrence and all weighted Gaussian mixed jets at the Taylor origin.
The unweighted base is the very same weighted jet evaluated at w=0.
No differentiation through infinite sums or improper integrals here.
-/

namespace W5
open MeasureTheory

theorem thetaAllMixedJetTerm_at_origin_affine
    (x : ℝ) (n : ℕ) (w : ℝ) (hn : n ≠ 0) :
    ∀ i j : ℕ, thetaAllMixedJetTerm x 0 0 n w i j =
      (Real.exp (-((n:ℝ)^2-1)/x^2) *
        (Real.exp (-w) * (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4))) *
        thetaAffineExpJet (-(((n:ℝ)^2-1)/x+w*x))
          (-((n:ℝ)^2+w*x^2)) (-(((n:ℝ)^2-1)/x+w*x)) i j 0 := by
  let p : ℝ := (n:ℝ)^2
  let d : ℝ := (p-1)/x+w*x
  let q : ℝ := p+w*x^2
  let E : ℝ := Real.exp (-(p-1)/x^2) *
    (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4))
  have hm : thetaWeightedGaussianRightMultiplier x p ((p-1)/x) 0 w = -d := by
    dsimp [d, thetaWeightedGaussianRightMultiplier]
    ring
  intro i
  induction i with
  | zero =>
      intro j
      change thetaHigherRightJetSeriesTerm j x 0 0 n w =
        E * thetaAffineExpJet (-d) (-q) (-d) 0 j 0
      simp only [thetaHigherRightJetSeriesTerm, if_neg hn, thetaWeightedGaussianRightJet,
        thetaAffineExpJet, mul_zero, add_zero, Real.exp_zero, mul_one]
      change Real.exp (-(p-1)/x^2) *
        (thetaWeightedGaussianRightMultiplier x p ((p-1)/x) 0 w ^ j *
          thetaWeightedGaussianIntegrand x p ((p-1)/x) 0 0 w) = E * (-d)^j
      rw [hm]
      simp only [thetaWeightedGaussianIntegrand, thetaGaussianModel_zero_zero, mul_one]
      dsimp [E]
      ring
  | succ i ih =>
      intro j
      change (j:ℝ) * (-q) * thetaAllMixedJetTerm x 0 0 n w i (j-1) +
        thetaWeightedGaussianRightMultiplier x p ((p-1)/x) 0 w *
          thetaAllMixedJetTerm x 0 0 n w i j =
        E * thetaAffineExpJet (-d) (-q) (-d) (i+1) j 0
      rw [hm, ih (j-1), ih j]
      change (j:ℝ) * (-q) * (E * thetaAffineExpJet (-d) (-q) (-d) i (j-1) 0) +
        (-d) * (E * thetaAffineExpJet (-d) (-q) (-d) i j 0) =
        E * ((-d) * thetaAffineExpJet (-d) (-q) (-d) i j 0 +
          ((j:ℝ)*(-q)) * thetaAffineExpJet (-d) (-q) (-d) i (j-1) 0)
      ring

theorem thetaAllMixedJetTerm_at_origin_normalized
    (x : ℝ) (n : ℕ) (w : ℝ) (i j : Fin 5) (hn : n ≠ 0) :
    thetaAllMixedJetTerm x 0 0 n w i.val j.val /
      ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ)) =
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        (Real.exp (-w) * (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4)) *
        coefficientPolynomial i j (((n:ℝ)^2-1)/x+w*x) ((n:ℝ)^2+w*x^2) := by
  rw [thetaAllMixedJetTerm_at_origin_affine x n w hn i.val j.val,
    mul_div_assoc, thetaAffineExpJet_zero_eq_coefficientPolynomial]

theorem thetaAllMixedJetTerm_at_zero_index
    (x u v w : ℝ) (i j : ℕ) : thetaAllMixedJetTerm x u v 0 w i j = 0 := by
  induction i generalizing j with
  | zero => simp [thetaAllMixedJetTerm, thetaHigherRightJetSeriesTerm]
  | succ i ih => simp only [thetaAllMixedJetTerm, ih, mul_zero, add_zero]

theorem thetaCertificateCorrectionIntegrand_eq_mixed_jet
    (x : ℝ) (i j : Fin 5) (n : ℕ) (w : ℝ) :
    thetaCertificateCorrectionIntegrand x i j n w =
      (x^2/4) * (thetaAllMixedJetTerm x 0 0 n w i.val j.val /
        ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateCorrectionIntegrand, thetaAllMixedJetTerm_at_zero_index]
  · rw [thetaAllMixedJetTerm_at_origin_normalized x n w i j hn]
    simp only [thetaCertificateCorrectionIntegrand, if_neg hn]
    ring

theorem thetaCertificateCorrectionTerm_eq_all_mixed_integral
    (x : ℝ) (i j : Fin 5) (n : ℕ) :
    thetaCertificateCorrectionTerm x i j n =
      (x^2/4) * ((∫ w : ℝ, thetaAllMixedJetTerm x 0 0 n w i.val j.val
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) /
        ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ))) := by
  rw [thetaCertificateCorrectionTerm_eq_integral]
  have heq :
      thetaCertificateCorrectionIntegrand x i j n =
        (fun w : ℝ => (x^2/4) * (thetaAllMixedJetTerm x 0 0 n w i.val j.val /
          ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ)))) := by
    funext w
    exact thetaCertificateCorrectionIntegrand_eq_mixed_jet x i j n w
  rw [heq, integral_const_mul]
  simp only [div_eq_mul_inv, integral_mul_const]

theorem thetaCertificateBaseTerm_eq_all_mixed_zero_w
    (x : ℝ) (i j : Fin 5) (n : ℕ) :
    thetaCertificateBaseTerm x i j n =
      (n:ℝ)^2 * (thetaAllMixedJetTerm x 0 0 n 0 i.val j.val /
        ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateBaseTerm]
  · rw [thetaAllMixedJetTerm_at_origin_normalized x n 0 i j hn]
    simp [thetaCertificateBaseTerm, hn, Real.one_rpow, mul_assoc]

/-- Before differentiation the actual base term is exactly p times
the same zero-order weighted jet evaluated at w=0. -/
theorem thetaCertificateGaussianBaseTerm_eq_zero_w
    (x u v : ℝ) (n : ℕ) :
    thetaCertificateGaussianBaseTerm x u v n =
      (n:ℝ)^2 * thetaAllMixedJetTerm x u v n 0 0 0 := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateGaussianBaseTerm]
  · simp [thetaCertificateGaussianBaseTerm, thetaAllMixedJetTerm,
      thetaHigherRightJetSeriesTerm, hn, thetaWeightedGaussianRightJet_zero,
      thetaWeightedGaussianIntegrand, Real.one_rpow, mul_assoc]

end W5
