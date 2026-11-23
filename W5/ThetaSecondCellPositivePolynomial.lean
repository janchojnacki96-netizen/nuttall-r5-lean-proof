import W5.ThetaAllCoefficientPolynomialEnvelope

/-!
# Exact positive finite envelope for ALL original B_ij coefficients

The pre-existing uniform eighth-power envelope is excellent for
summability, but too coarse for the first two omitted square
indices. Reuse its original factorial definition, the Mathlib
triangle inequality for finite sums, and positivity of real powers.

The resulting envelope keeps EACH factorial coefficient and EACH
individual power; it is the exact algebraic positive polynomial
behind the new finite rational n=2,3 cell majorants.

No separate i,j proof, polynomial expansion, integral evaluation,
or numerical input is introduced here.
-/

namespace W5

/-- Exact positive finite polynomial obtained by dropping ONLY
the signs from the original alternating theta coefficient. -/
noncomputable def thetaCoefficientPositivePolynomial
    (i j : Fin 5) (d p : ℝ) : ℝ :=
  ∑ t ∈ Finset.range (min i.val j.val + 1),
    (1 / ((Nat.factorial t : ℝ) *
      (Nat.factorial (i.val-t) : ℝ) *
      (Nat.factorial (j.val-t) : ℝ))) *
      d^(i.val+j.val-2*t) * p^t

/-- This keeps all exact original factorial weights. It is
sharper than the already-verified common eighth-power envelope. -/
theorem thetaCoefficientPolynomial_abs_le_positive
    (i j : Fin 5) (d p : ℝ) (hd : 0 ≤ d) (hp : 0 ≤ p) :
    |coefficientPolynomial i j d p| ≤
      thetaCoefficientPositivePolynomial i j d p := by
  unfold coefficientPolynomial thetaCoefficientPositivePolynomial
  calc
    |∑ t ∈ Finset.range (min i.val j.val + 1),
      ((-1:ℝ)^(i.val+j.val-t) *
        d^(i.val+j.val-2*t) * p^t) /
      ((Nat.factorial t : ℝ) *
       (Nat.factorial (i.val-t) : ℝ) *
       (Nat.factorial (j.val-t) : ℝ))| ≤
      ∑ t ∈ Finset.range (min i.val j.val + 1),
        |((-1:ℝ)^(i.val+j.val-t) *
          d^(i.val+j.val-2*t) * p^t) /
          ((Nat.factorial t : ℝ) *
           (Nat.factorial (i.val-t) : ℝ) *
           (Nat.factorial (j.val-t) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      have hden :
          0 ≤ (Nat.factorial t : ℝ) *
            (Nat.factorial (i.val-t) : ℝ) *
            (Nat.factorial (j.val-t) : ℝ) := by positivity
      simp only [abs_div, abs_mul, abs_pow, abs_neg,
        abs_one, one_pow, one_mul,
        abs_of_nonneg (pow_nonneg hd _),
        abs_of_nonneg (pow_nonneg hp _),
        abs_of_nonneg hden]
      ring

/-- Monotonicity in both nonnegative arguments, for EVERY
original theta polynomial entry at once. -/
theorem thetaCoefficientPositivePolynomial_mono
    (i j : Fin 5) (d₁ d₂ p₁ p₂ : ℝ)
    (hd₁ : 0 ≤ d₁) (hdd : d₁ ≤ d₂)
    (hp₁ : 0 ≤ p₁) (hpp : p₁ ≤ p₂) :
    thetaCoefficientPositivePolynomial i j d₁ p₁ ≤
      thetaCoefficientPositivePolynomial i j d₂ p₂ := by
  unfold thetaCoefficientPositivePolynomial
  apply Finset.sum_le_sum
  intro t _
  have hdPow :
      d₁^(i.val+j.val-2*t) ≤
        d₂^(i.val+j.val-2*t) :=
    pow_le_pow_left₀ hd₁ hdd _
  have hpPow : p₁^t ≤ p₂^t :=
    pow_le_pow_left₀ hp₁ hpp _
  have hc : 0 ≤
      (1 / ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) := by positivity
  have hd₂ : 0 ≤ d₂ := hd₁.trans hdd
  calc
    (1 / ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) *
          d₁^(i.val+j.val-2*t) * p₁^t ≤
      (1 / ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) *
          d₂^(i.val+j.val-2*t) * p₁^t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdPow hc) (pow_nonneg hp₁ t)
    _ ≤
      (1 / ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) *
          d₂^(i.val+j.val-2*t) * p₂^t := by
      exact mul_le_mul_of_nonneg_left hpPow
        (mul_nonneg hc (pow_nonneg hd₂ _))

end W5
