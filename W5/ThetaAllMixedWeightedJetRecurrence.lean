import W5.ThetaMixedJetNeighborMajorant
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Arbitrary left/right jets of the actual weighted Gaussian summands

Use the already verified one-left derivative and neighbor identity
as the base case. For fixed v,n,w the two coefficients of the
recurrence are independent of u. Thus induction handles every left
order, not just one. No differentiation under an integral is used.
-/

namespace W5

noncomputable def thetaAllMixedJetTerm (x u v : ℝ) (n : ℕ) (w : ℝ) :
    ℕ → ℕ → ℝ
  | 0, j => thetaHigherRightJetSeriesTerm j x u v n w
  | i+1, j =>
      (j:ℝ) * (-((n:ℝ)^2+w*x^2)) *
        thetaAllMixedJetTerm x u v n w i (j-1) +
      thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) v w *
        thetaAllMixedJetTerm x u v n w i j

theorem thetaAllMixedJetTerm_hasDerivAt_left
    (x v : ℝ) (n : ℕ) (w : ℝ) :
    ∀ (i j : ℕ) (u : ℝ),
      HasDerivAt (fun z : ℝ => thetaAllMixedJetTerm x z v n w i j)
        (thetaAllMixedJetTerm x u v n w (i+1) j) u := by
  intro i
  induction i with
  | zero =>
      intro j u
      have h := thetaHigherRightJetSeriesTerm_hasDerivAt_left j x u v n w
      rw [thetaMixedOneRightJetSeriesTerm_eq_neighbors] at h
      exact h
  | succ i ih =>
      intro j u
      have h := ((ih (j-1) u).const_mul
        ((j:ℝ) * (-((n:ℝ)^2+w*x^2)))).add
        ((ih j u).const_mul
          (thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) v w))
      exact h

/-- The symbolic recurrence is an actual ordinary iterated derivative
of the already established weighted right-jet integrand. -/
theorem thetaAllMixedJetTerm_eq_iteratedDeriv
    (x v : ℝ) (n : ℕ) (w : ℝ) (i j : ℕ) (u : ℝ) :
    iteratedDeriv i (fun z : ℝ =>
      thetaHigherRightJetSeriesTerm j x z v n w) u =
      thetaAllMixedJetTerm x u v n w i j := by
  induction i generalizing u with
  | zero => rfl
  | succ i ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv i
          (fun z : ℝ => thetaHigherRightJetSeriesTerm j x z v n w) =
          (fun z : ℝ => thetaAllMixedJetTerm x z v n w i j) := by
        funext z
        exact ih z
      rw [hfun]
      exact (thetaAllMixedJetTerm_hasDerivAt_left x v n w i j u).deriv

theorem thetaAllMixedJetTerm_one
    (x u v : ℝ) (n : ℕ) (w : ℝ) (j : ℕ) :
    thetaAllMixedJetTerm x u v n w 1 j =
      thetaMixedOneRightJetSeriesTerm j x u v n w := by
  exact (thetaMixedOneRightJetSeriesTerm_eq_neighbors j x u v n w).symm

theorem thetaAllMixedJetTerm_measurable
    (x u v : ℝ) (n : ℕ) :
    ∀ (i j : ℕ), Measurable
      (fun w : ℝ => thetaAllMixedJetTerm x u v n w i j) := by
  intro i
  induction i with
  | zero =>
      intro j
      exact thetaHigherRightJetSeriesTerm_measurable j x u v n
  | succ i ih =>
      intro j
      have h1 : Measurable (fun w : ℝ =>
          (j:ℝ) * (-((n:ℝ)^2+w*x^2))) := by fun_prop
      have h2 : Measurable (fun w : ℝ =>
          thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) v w) := by
        unfold thetaWeightedGaussianRightMultiplier
        fun_prop
      exact (h1.mul (ih (j-1))).add (h2.mul (ih j))

/-- The exact same two neighbor coefficients admit a uniform bound
on the original small parameter patch, independently of the left order. -/
theorem thetaAllMixedJetTerm_coefficients_bound
    (x v : ℝ) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hv : |v| ≤ x/8)
    (hw : 0 ≤ w) (hn : n ≠ 0) :
    |(n:ℝ)^2+w*x^2| ≤ ((n:ℝ)^2+1)*(w+1) ∧
    |thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
        (((n:ℝ)^2-1)/x) v w| ≤
      (1/x+2)*(((n:ℝ)^2+1)*(w+1)) := by
  let p : ℝ := (n:ℝ)^2
  have hp0 : 0 ≤ p := sq_nonneg _
  have hnR : (1:ℝ) ≤ (n:ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hp : 1 ≤ p := by dsimp [p]; nlinarith
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]
  have hsep : p+w ≤ (p+1)*(w+1) := by
    nlinarith [mul_nonneg hp0 hw]
  have hq : |p+w*x^2| ≤ p+w := by
    rw [abs_of_nonneg (add_nonneg hp0 (mul_nonneg hw (sq_nonneg x)))]
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hx2)]
  have hmabs :
      |thetaWeightedGaussianRightMultiplier x p ((p-1)/x) v w| ≤
        |(p-1)/x+p*v| + w*|x*(1+x*v)| := by
    simpa only [thetaWeightedGaussianRightMultiplier] using
      thetaGaussian_right_multiplier_abs_le x p ((p-1)/x) v w hw
  have hm := hmabs.trans
    (thetaGaussian_small_box_right_multiplier_le x p v w hx hx1 hp hw hv)
  exact ⟨hq.trans hsep,
    hm.trans (mul_le_mul_of_nonneg_left hsep (by positivity))⟩

end W5
