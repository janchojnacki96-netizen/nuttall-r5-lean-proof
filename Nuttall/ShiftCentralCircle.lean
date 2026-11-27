import Nuttall.ShiftCentralLogBound
import Mathlib.Analysis.Complex.Trigonometric

namespace Nuttall

open Complex

private theorem real_sqrt_eq_exp_half_log {a : ℝ} (ha : 0 < a) :
    Real.sqrt a = Real.exp (Real.log a/2) := by
  apply (Real.sqrt_eq_iff_eq_sq ha.le (Real.exp_nonneg _)).2
  rw [← Real.exp_nat_mul, show (↑(2:ℕ) : ℝ)*(Real.log a/2) = Real.log a by push_cast; ring,
    Real.exp_log ha]

/-- The pointwise Gaussian bound extends to the two endpoints, including
the vanishing factors of the integrand. -/
theorem shiftCentralSqrtBound {M j : ℕ} (hM : 0 < M) (hj : j ≤ M) {x : ℝ}
    (hx₀ : -1 ≤ x) (hx₁ : x ≤ 1) :
    Real.sqrt (1+x)^(M-j) * Real.sqrt (1-x)^j ≤
      Real.exp (4*((M:ℝ)/2-j)^2/M-M*x^2/16) := by
  let S := {x : ℝ | Real.sqrt (1+x)^(M-j) * Real.sqrt (1-x)^j ≤
      Real.exp (4*((M:ℝ)/2-j)^2/M-M*x^2/16)}
  have hc : IsClosed S := isClosed_le (by fun_prop) (by fun_prop)
  have hsub : Set.Ioo (-1:ℝ) 1 ⊆ S := by
    intro t ht
    dsimp [S]
    rw [real_sqrt_eq_exp_half_log (by have := ht.1; linarith),
      real_sqrt_eq_exp_half_log (by have := ht.2; linarith),
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp,
      Nat.cast_sub hj]
    have h := shiftCentralLogBound (show (0:ℝ) < M by exact_mod_cast hM)
      (show (0:ℝ) ≤ j by positivity) (show (j:ℝ) ≤ M by exact_mod_cast hj) ht.1 ht.2
    linarith only [h]
  apply hc.closure_subset_iff.mpr hsub
  rw [closure_Ioo (by norm_num : (-1:ℝ) ≠ 1)]
  exact ⟨hx₀, hx₁⟩

/-- The two affine factors have complementary squared moduli on the circle. -/
theorem shiftCentral_factor_norm_sq {c d : ℝ} (hunit : c^2+d^2 = 1) (θ : ℝ) :
    ‖(c:ℂ)+(d:ℂ)*Complex.exp ((θ:ℂ)*I)‖^2 = 1+2*c*d*Real.cos θ ∧
    ‖(d:ℂ)-(c:ℂ)*Complex.exp ((θ:ℂ)*I)‖^2 = 1-2*c*d*Real.cos θ := by
  have h := Real.sin_sq_add_cos_sq θ
  constructor
  · simp only [Complex.sq_norm, normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re,
      ofReal_im, zero_mul, zero_add, sub_zero, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    linear_combination (d^2)*h + hunit
  · simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, mul_re, mul_im, ofReal_re,
      ofReal_im, zero_mul, zero_add, sub_zero, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    linear_combination (c^2)*h + hunit

/-- The product which defines the central coefficients has a pointwise
Gaussian majorant all around the circle. -/
theorem shiftCentral_circle_product_bound {M j : ℕ} (hM : 0 < M) (hj : j ≤ M)
    {c d : ℝ} (hunit : c^2+d^2 = 1) (θ : ℝ) :
    let z := Complex.exp ((θ:ℂ)*I)
    let x := 2*c*d*Real.cos θ
    ‖((c:ℂ)+(d:ℂ)*z)^(M-j) * ((d:ℂ)-(c:ℂ)*z)^j‖ ≤
      Real.exp (4*((M:ℝ)/2-j)^2/M-M*x^2/16) := by
  let z := Complex.exp ((θ:ℂ)*I)
  let x := 2*c*d*Real.cos θ
  obtain ⟨hp, hn⟩ := shiftCentral_factor_norm_sq hunit θ
  change ‖(c:ℂ)+(d:ℂ)*z‖^2 = 1+x at hp
  change ‖(d:ℂ)-(c:ℂ)*z‖^2 = 1-x at hn
  have h₀ : -1 ≤ x := by linarith only [hp, sq_nonneg ‖(c:ℂ)+(d:ℂ)*z‖]
  have h₁ : x ≤ 1 := by linarith only [hn, sq_nonneg ‖(d:ℂ)-(c:ℂ)*z‖]
  have hs₀ : ‖(c:ℂ)+(d:ℂ)*z‖ = Real.sqrt (1+x) := by
    rw [← hp, Real.sqrt_sq (norm_nonneg _)]
  have hs₁ : ‖(d:ℂ)-(c:ℂ)*z‖ = Real.sqrt (1-x) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  dsimp only
  rw [norm_mul, norm_pow, norm_pow, hs₀, hs₁]
  exact shiftCentralSqrtBound hM hj h₀ h₁

#print axioms shiftCentralSqrtBound
#print axioms shiftCentral_circle_product_bound

end Nuttall
