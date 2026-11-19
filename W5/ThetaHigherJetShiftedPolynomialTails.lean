import W5.ThetaHigherJetSeparableEnvelope

/-!
# Summability and integrability of the two separated higher-jet factors

The pointwise factorization proved in the previous module produces

  (n²+1)^(k+1) * exp(-47*n²/64)

and

  (w+1)^k * (w²+w+1) * exp(-w/4).

We prove that the first is summable in n, and the second is
Lebesgue integrable over w>0, for every fixed k.  The proof
expands the shifted polynomial by the finite binomial theorem
and applies the already formalized monomial Gaussian/exponential
convergence, without postulating any new analytic convergence.

These are components of a dominated-convergence argument, not
yet an interchange of higher derivatives with the n-sum or w-integral.
-/

namespace W5
open MeasureTheory

/-- Each fixed-degree polynomial in 1+n² is summable under
the surviving Gaussian square-index decay. -/
theorem thetaHigherJet_shifted_index_summable (k : ℕ) :
    Summable (fun n : ℕ =>
      (((n:ℝ)^2+1)^k) * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) := by
  have hterms (j : ℕ) :
      Summable (fun n : ℕ =>
        (((n:ℝ)^2)^j * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) *
          (k.choose j : ℝ)) :=
    Summable.mul_right (k.choose j : ℝ)
      (thetaHigherJet_even_index_monomial_summable j)
  have hsum : Summable (fun n : ℕ =>
      ∑ j ∈ Finset.range (k+1),
        (((n:ℝ)^2)^j * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) *
          (k.choose j : ℝ)) := by
    simpa only [Finset.sum_apply] using
      (summable_sum (s := Finset.range (k+1))
        (fun j _ => hterms j))
  have hfun :
      (fun n : ℕ =>
        (((n:ℝ)^2+1)^k) * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) =
      (fun n : ℕ =>
        ∑ j ∈ Finset.range (k+1),
          (((n:ℝ)^2)^j * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) *
            (k.choose j : ℝ)) := by
    funext n
    rw [add_pow, Finset.sum_mul]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun]
  exact hsum

/-- The shifted polynomial w+1 also remains integrable to
every finite order under exp(-w/4) on the positive half-line. -/
theorem thetaHigherJet_shifted_w_integrableOn (k : ℕ) :
    IntegrableOn (fun w : ℝ =>
      (w+1)^k * Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hterms (j : ℕ) : Integrable
      (fun w : ℝ =>
        (w^j * Real.exp (-((1:ℝ)/4)*w)) * (k.choose j : ℝ)) μ :=
    (thetaHigherJet_w_monomial_integrableOn j).mul_const (k.choose j : ℝ)
  have hsum : Integrable
      (fun w : ℝ =>
        ∑ j ∈ Finset.range (k+1),
          (w^j * Real.exp (-((1:ℝ)/4)*w)) * (k.choose j : ℝ)) μ := by
    have hraw : Integrable
        (∑ j ∈ Finset.range (k+1),
          (fun w : ℝ =>
            (w^j * Real.exp (-((1:ℝ)/4)*w)) * (k.choose j : ℝ))) μ :=
      integrable_finsetSum' (Finset.range (k+1))
        (fun j _ => hterms j)
    convert hraw using 1
    funext w
    simp only [Finset.sum_apply]
  have hfun :
      (fun w : ℝ => (w+1)^k * Real.exp (-((1:ℝ)/4)*w)) =
      (fun w : ℝ =>
        ∑ j ∈ Finset.range (k+1),
          (w^j * Real.exp (-((1:ℝ)/4)*w)) * (k.choose j : ℝ)) := by
    funext w
    rw [add_pow, Finset.sum_mul]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change Integrable
    (fun w : ℝ => (w+1)^k * Real.exp (-((1:ℝ)/4)*w)) μ
  rw [hfun]
  exact hsum

/-- The full separated w-factor from the higher theta-jet
bound is integrable. We dominate its quadratic factor by
(w+1)^2 for w>0, reducing the claim to the preceding theorem. -/
theorem thetaHigherJet_full_w_factor_integrableOn (k : ℕ) :
    IntegrableOn (fun w : ℝ =>
      ((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hbig : Integrable
      (fun w : ℝ => (w+1)^(k+2) * Real.exp (-((1:ℝ)/4)*w)) μ :=
    thetaHigherJet_shifted_w_integrableOn (k+2)
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ =>
        ((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w)) μ := by
    fun_prop
  have hbound : ∀ᵐ w : ℝ ∂μ,
      ‖((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w)‖ ≤
        (w+1)^(k+2) * Real.exp (-((1:ℝ)/4)*w) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : 0 ≤ w := le_of_lt hw
    have hw1 : 0 ≤ w+1 := by linarith
    have hq : w^2+w+1 ≤ (w+1)^2 := by nlinarith
    have hmul : (w+1)^k * (w^2+w+1) ≤ (w+1)^(k+2) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_left hq (pow_nonneg hw1 k)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (by positivity :
        0 ≤ ((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w))]
    exact mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg _)
  change Integrable
    (fun w : ℝ =>
      ((w+1)^k*(w^2+w+1)) * Real.exp (-((1:ℝ)/4)*w)) μ
  exact hbig.mono' hmeas hbound

end W5
