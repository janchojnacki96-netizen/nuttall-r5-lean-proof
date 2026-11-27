import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Nuttall

open Filter
open scoped Topology

/-- The cutoff of Section 4.1 after substituting (m=2r). -/
noncomputable def shiftCriticalCutoff (r : ℝ) : ℝ :=
  Real.log (8*r*Real.log (384*r))/4

/-- The logarithmic cutoff and its exponential are controlled by small
powers of the order, with enough room for all the uniform estimates. -/
theorem eventually_shiftCriticalCutoff_bounds :
    ∀ᶠ r : ℝ in atTop, 2 ≤ r ∧ 0 < shiftCriticalCutoff r ∧
      shiftCriticalCutoff r ≤ r^(1/32:ℝ) ∧ Real.exp (shiftCriticalCutoff r) ≤ r^(3/8:ℝ) := by
  have hsmall := (isLittleO_log_rpow_atTop (r := (1/2:ℝ)) (by norm_num)).bound
    (show (0:ℝ) < 1/16 by norm_num)
  have hsmall' := (isLittleO_log_rpow_atTop (r := (1/32:ℝ)) (by norm_num)).bound
    (show (0:ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (384:ℝ), eventually_ge_atTop (1/Real.log 2), hsmall, hsmall'] with
    r hr hlog hr₁ hr₂
  have hp : 0 < r := by linarith
  have htwo : 2 ≤ r := by linarith
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (384*r) := Real.log_le_log (by norm_num) (by linarith)
  have hbase : 1 < 8*r*Real.log (384*r) := by
    have hlr := (div_le_iff₀ hlog₂).1 hlog
    have h := mul_le_mul_of_nonneg_left hl hp.le
    nlinarith only [hlr, h]
  have hcn : 0 < shiftCriticalCutoff r := by
    unfold shiftCriticalCutoff
    exact div_pos (Real.log_pos hbase) (by norm_num)
  have hlog_small : Real.log (384*r) ≤ r^(1/2:ℝ)/8 := by
    have hh : Real.log 384 ≤ Real.log r := Real.log_le_log (by norm_num) hr
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _)] at hr₁
    rw [Real.log_mul (by norm_num) hp.ne']
    linarith only [hh, hr₁, le_abs_self (Real.log r)]
  have hex : Real.exp (shiftCriticalCutoff r) ≤ r^(3/8:ℝ) := by
    have hquarter : Real.exp (shiftCriticalCutoff r) = (8*r*Real.log (384*r))^(1/4:ℝ) := by
      unfold shiftCriticalCutoff
      rw [Real.rpow_def_of_pos (by linarith : 0 < 8*r*Real.log (384*r))]
      congr 1
      ring
    rw [hquarter, show (3/8:ℝ)=(3/2)*(1/4) by norm_num, Real.rpow_mul hp.le]
    apply Real.rpow_le_rpow (by linarith) _ (by norm_num)
    have h := mul_le_mul_of_nonneg_left hlog_small (show 0 ≤ 8*r by positivity)
    calc
      _ ≤ r * r^(1/2:ℝ) := by nlinarith only [h]
      _ = _ := by rw [show (3/2:ℝ) = 1+1/2 by norm_num, Real.rpow_add hp, Real.rpow_one]
  refine ⟨htwo, hcn, ?_, hex⟩
  have hh : shiftCriticalCutoff r ≤ Real.log r*(3/8:ℝ) := by
    apply Real.exp_le_exp.1
    rwa [← Real.rpow_def_of_pos hp]
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), one_mul] at hr₂
  have hrpow : 0 ≤ r^(1/32:ℝ) := Real.rpow_nonneg hp.le _
  have h := mul_le_mul_of_nonneg_right ((le_abs_self (Real.log r)).trans hr₂) (by norm_num : 0 ≤ (3/8:ℝ))
  linarith only [hh, h, hrpow]

#print axioms eventually_shiftCriticalCutoff_bounds

end Nuttall
