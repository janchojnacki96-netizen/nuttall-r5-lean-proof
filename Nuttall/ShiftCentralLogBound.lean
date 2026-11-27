import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Nuttall

/-- A uniform second-order upper bound for the logarithm on the interval
arising from the moduli on the unit circle. -/
theorem log_one_add_le_sub_sq {x : ℝ} (hx₀ : -1 < x) (hx₁ : x ≤ 1) :
    Real.log (1+x) ≤ x-x^2/4 := by
  let F (t : ℝ) := t-t^2/4-Real.log (1+t)
  have hderiv (t : ℝ) (ht : -1 < t) :
      HasDerivAt F (t*(1-t)/(2*(1+t))) t := by
    have ht' : 1+t ≠ 0 := by linarith
    have hp := (hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 4)
    have hl := (Real.hasDerivAt_log ht').comp t ((hasDerivAt_id t).const_add 1)
    convert hp.sub hl using 1
    · funext y
      simp [F, add_comm]
    · simp [add_comm, pow_one]
      field_simp [ht', show t+1 ≠ 0 by linarith]
      ring
  have hnonneg : 0 ≤ F x := by
    by_cases hx : 0 ≤ x
    · have hm : MonotoneOn F (Set.Icc (0:ℝ) 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        · intro t ht
          exact (hderiv t (by have := ht.1; linarith)).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : t ∈ Set.Icc (0:ℝ) 1 := interior_subset ht
          exact (hderiv t (by have := ht'.1; linarith)).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : t ∈ Set.Icc (0:ℝ) 1 := interior_subset ht
          rw [(hderiv t (by have := ht'.1; linarith)).deriv]
          exact div_nonneg (mul_nonneg ht'.1 (sub_nonneg.2 ht'.2)) (by have := ht'.1; linarith)
      have h := hm (show 0 ∈ Set.Icc (0:ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
        (show x ∈ Set.Icc (0:ℝ) 1 from ⟨hx, hx₁⟩) hx
      simpa [F] using h
    · have hm : AntitoneOn F (Set.Ioc (-1:ℝ) 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioc (-1) 0)
        · intro t ht
          exact (hderiv t ht.1).continuousAt.continuousWithinAt
        · intro t ht
          have ht' : t ∈ Set.Ioc (-1:ℝ) 0 := interior_subset ht
          exact (hderiv t ht'.1).differentiableAt.differentiableWithinAt
        · intro t ht
          have ht' : t ∈ Set.Ioc (-1:ℝ) 0 := interior_subset ht
          rw [(hderiv t ht'.1).deriv]
          exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg ht'.2 (by have := ht'.2; linarith))
            (by have := ht'.1; linarith)
      have hx' : x ≤ 0 := le_of_not_ge hx
      have h := hm (show x ∈ Set.Ioc (-1:ℝ) 0 from ⟨hx₀, hx'⟩)
        (show 0 ∈ Set.Ioc (-1:ℝ) 0 from ⟨by norm_num, le_rfl⟩) hx'
      simpa [F] using h
  exact sub_nonneg.1 hnonneg

/-- The two factors on the circle have squared moduli (1+x) and (1-x).
The combined log-modulus is bounded by the Gaussian exponent in Section 4.2. -/
theorem shiftCentralLogBound {M j x : ℝ} (hM : 0 < M) (hj₀ : 0 ≤ j) (hjM : j ≤ M)
    (hx₀ : -1 < x) (hx₁ : x < 1) :
    ((M-j)*Real.log (1+x)+j*Real.log (1-x))/2 ≤
      4*(M/2-j)^2/M-M*x^2/16 := by
  have hp := mul_le_mul_of_nonneg_left (log_one_add_le_sub_sq hx₀ hx₁.le) (sub_nonneg.2 hjM)
  have hn := mul_le_mul_of_nonneg_left (log_one_add_le_sub_sq (x := -x) (by linarith) (by linarith)) hj₀
  rw [show 1 + -x = 1-x by ring] at hn
  have hsq : (M/2-j)*x - M*x^2/16 ≤ 4*(M/2-j)^2/M := by
    apply (le_div_iff₀ hM).2
    nlinarith only [sq_nonneg (M*x-8*(M/2-j))]
  nlinarith only [hp, hn, hsq]

#print axioms log_one_add_le_sub_sq
#print axioms shiftCentralLogBound

end Nuttall
