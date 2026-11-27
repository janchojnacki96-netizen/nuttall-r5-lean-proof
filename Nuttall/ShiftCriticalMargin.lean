import Nuttall.ShiftCriticalAsymptotic
import Nuttall.ShiftDeterminantMargin

namespace Nuttall

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

private theorem eventually_shiftCorrection_budget_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      shiftCriticalCutoff r*(1/(r:ℝ)+Real.sqrt (Real.pi/(r:ℝ))) ≤ ε := by
  have hpow := tendsto_rpow_neg_atTop (show (0:ℝ) < 15/32 by norm_num)
  have hlim : Tendsto (fun r : ℝ => (1+Real.sqrt Real.pi)*r^(-(15/32):ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul _
  have hsmall := (tendsto_order.1 hlim).2 ε hε
  have hel := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hel.eventually eventually_shiftCriticalCutoff_bounds, hel.eventually hsmall] with r hr hsm
  let x : ℝ := r
  have hx : 0 < x := by have : 2 ≤ x := hr.1; linarith
  have hx₁ : 1 ≤ x := by have : 2 ≤ x := hr.1; linarith
  have hroot : Real.sqrt x ≤ x := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hx₁ (show (1/2:ℝ) ≤ 1 by norm_num))
  have hinv : 1/x ≤ 1/Real.sqrt x := one_div_le_one_div_of_le (Real.sqrt_pos.2 hx) hroot
  have hB : 0 < shiftCriticalCutoff x := hr.2.1
  change shiftCriticalCutoff x*(1/x+Real.sqrt (Real.pi/x)) ≤ ε
  calc
    _ ≤ x^(1/32:ℝ)*((1+Real.sqrt Real.pi)/Real.sqrt x) := by
      apply mul_le_mul hr.2.2.1 _ (by positivity) (Real.rpow_nonneg hx.le _)
      rw [Real.sqrt_div Real.pi_nonneg, add_div]
      exact add_le_add hinv le_rfl
    _ = (1+Real.sqrt Real.pi)*x^(-(15/32):ℝ) := by
      rw [Real.sqrt_eq_rpow x,
        show x^(1/32:ℝ)*((1+Real.sqrt Real.pi)/(x^(1/2:ℝ))) =
          (1+Real.sqrt Real.pi)*(x^(1/32:ℝ)/(x^(1/2:ℝ))) by ring,
        ← Real.rpow_sub hx]
      norm_num
    _ ≤ _ := hsm.le

/-- The margin from the alternating sign matrix is uniformly (2^{-1/2}+o(1)),
with the exact cutoff of the preprint. -/
theorem eventually_shiftCriticalMargin (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ M k : ℕ, r-1 ≤ M → k ≤ r → 2*(k-1) ≤ M →
      ∀ u : ℝ, 0 < u → u ≤ shiftCriticalCutoff r →
      ‖summedCorrectedShiftCore M k u-shiftSignMatrix k‖ ≤ 1/Real.sqrt 2+ε := by
  let δ : ℝ := min 1 (ε/4)
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ₁ : δ ≤ 1 := min_le_left ..
  have hδε : 4*δ ≤ ε := by
    have h : δ ≤ ε/4 := min_le_right ..
    linarith
  have hroot : 1/Real.sqrt 2 ≤ 1 := by
    have h : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
    rw [Real.sqrt_one] at h
    exact (div_le_one (Real.sqrt_pos.2 (by norm_num))).2 h
  filter_upwards [eventually_ge_atTop (2:ℕ), eventually_earlier_shift_sum_le δ hδ,
    eventually_shiftCorrection_budget_le δ hδ] with r hr hearlier hbud M k hM hk hdim u hu huB
  let B := shiftCriticalCutoff r
  let E := B*(1/(r:ℝ)+Real.sqrt (Real.pi/(r:ℝ)))
  have hr' : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrM : (r:ℝ) ≤ (M:ℝ)+1 := by exact_mod_cast (show r ≤ M+1 by omega)
  have hB := hu.le.trans huB
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEδ : E ≤ δ := hbud
  have hS := hearlier M k hM hk hdim u hu huB
  have h := norm_summedCorrectedShiftCore_sub_le_split hdim hr' hrM hu huB
  change _ ≤ E+(1+E)*(1/Real.sqrt 2+∑ n ∈ Finset.Ico 2 (lastActiveTheta u),
    (Real.sqrt (n:ℝ))⁻¹ * ‖shiftCore M k (thetaKnot n/u)‖) at h
  apply h.trans
  calc
    _ ≤ E+(1+E)*(1/Real.sqrt 2+δ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hS) (by positivity))
    _ ≤ δ+(1+δ)*(1/Real.sqrt 2+δ) := by
      apply add_le_add hEδ
      exact mul_le_mul_of_nonneg_right (add_le_add le_rfl hEδ) (by positivity)
    _ ≤ 1/Real.sqrt 2+ε := by
      have h₁ := mul_le_mul_of_nonneg_left hroot hδ.le
      have h₂ := mul_le_mul_of_nonneg_left hδ₁ hδ.le
      nlinarith only [h₁, h₂, hδε]

/-- The verified critical-block margin yields positivity of all the initial
moment Wronskians off the knots for sufficiently large orders. -/
theorem eventually_shiftedMomentWronskian_pos :
    ∀ᶠ r : ℕ in atTop, ∀ p k : ℕ, 1 ≤ k → k ≤ p → p ≤ r →
      ∀ u : ℝ, 0 < u → u ≤ shiftCriticalCutoff r →
        (∀ n : ℕ, 0 < n → u ≠ thetaKnot n) →
        0 < shiftedMomentWronskian (2*r-p) k u := by
  have hroot : 1/Real.sqrt 2 ≤ 3/4 := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : 0 < (2:ℝ)))).2
    have hsq := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
    have hb : (4/3:ℝ) ≤ Real.sqrt 2 := by
      apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
      rw [hsq]
      norm_num
    linarith
  filter_upwards [eventually_shiftCriticalMargin (1/8) (by norm_num)] with
    r hr p k hk hkp hpr u hu huB hkn
  let M := 2*r-p+k-2
  have hMr : r-1 ≤ M := by dsimp [M]; omega
  have hdim : 2*(k-1) ≤ M := by dsimp [M]; omega
  have h := hr M k hMr (hkp.trans hpr) hdim u hu huB
  apply shiftedMomentWronskian_pos_of_norm_margin (L := 2*r-p) (by omega) hu hkn
  change ‖summedCorrectedShiftCore M k u-shiftSignMatrix k‖ < 1
  linarith only [h, hroot]

#print axioms eventually_shiftCriticalMargin
#print axioms eventually_shiftedMomentWronskian_pos

end Nuttall
