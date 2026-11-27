import Nuttall.ShiftEarlierSum
import Nuttall.ShiftCriticalCutoff

namespace Nuttall

open Filter
open scoped Topology BigOperators Matrix.Norms.L2Operator

private theorem sqrt_order_le {r : ℝ} (hr : 2 ≤ r) {M : ℕ} (hM : r-1 ≤ M) :
    Real.sqrt r/2 ≤ Real.sqrt M := by
  have hp : 0 ≤ r := by linarith
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt hp, Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num
  linarith

private noncomputable def shiftErrorEnvelope (r : ℝ) : ℝ :=
  (32/(thetaKnot 2)^2)*r^(-(1/32):ℝ) +
    2*r^2*Real.exp (-(thetaKnot 2/32)*r^(15/32:ℝ))

/-- The powers bounding the cutoff make both terms of the earlier-shift error
small compared with an order-dependent envelope. -/
private theorem shiftEarlierError_le_envelope {r B : ℝ} {M k : ℕ}
    (hr : 2 ≤ r) (hM : r-1 ≤ M) (hk : (k:ℝ) ≤ r)
    (hB : 0 < B) (hBa : B ≤ r^(1/32:ℝ)) (hBe : Real.exp B ≤ r^(3/8:ℝ)) :
    shiftEarlierError M k B ≤ shiftErrorEnvelope r := by
  let a := thetaKnot 2
  let s := r^(1/32:ℝ)
  let t := r^(3/8:ℝ)
  have ha : 0 < a := thetaKnot_two_pos
  have hrp : 0 < r := by linarith
  have hr₁ : 1 ≤ r := by linarith
  have hs : 0 < s := Real.rpow_pos_of_pos hrp _
  have ht : 0 < t := Real.rpow_pos_of_pos hrp _
  have hs₁ : 1 ≤ s := Real.one_le_rpow hr₁ (by norm_num)
  have hsr : Real.sqrt r/2 ≤ Real.sqrt M := sqrt_order_le hr hM
  have hsqrt : Real.sqrt (2*B) ≤ 2*s := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hBs : B ≤ s := hBa
    nlinarith only [hBs, hs₁, sq_nonneg (s-1)]
  have had : a/s ≤ a/B := div_le_div_of_nonneg_left ha.le hB hBa
  have hexp : Real.exp (-a/B*Real.sqrt M/16) ≤
      Real.exp (-(a/32)*r^(15/32:ℝ)) := by
    apply Real.exp_le_exp.2
    have hh := mul_le_mul had hsr (by positivity : 0 ≤ Real.sqrt r/2) (by positivity : 0 ≤ a/B)
    have hrw : Real.sqrt r/s = r^(15/32:ℝ) := by
      dsimp [s]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hrp]
      norm_num
    have heq : a/s*(Real.sqrt r/2) = (a/2)*r^(15/32:ℝ) := by
      rw [← hrw]
      ring
    rw [heq] at hh
    calc
      _ = -(a/B*Real.sqrt M)/16 := by ring
      _ ≤ -((a/2)*r^(15/32:ℝ))/16 :=
        div_le_div_of_nonneg_right (neg_le_neg hh) (by norm_num)
      _ = _ := by ring
  have hcentral :
      4*(2*Real.sqrt (2*B)*Real.exp B/((a/B)^2*Real.sqrt M)) ≤
        (32/a^2)*r^(-(1/32):ℝ) := by
    calc
      _ ≤ 4*(2*(2*s)*t/((a/s)^2*(Real.sqrt r/2))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have hnum : 2*Real.sqrt (2*B)*Real.exp B ≤ 2*(2*s)*t :=
          mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hBe (Real.exp_nonneg _) (by positivity)
        have hden : (a/s)^2*(Real.sqrt r/2) ≤ (a/B)^2*Real.sqrt M :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) had _) hsr (by positivity) (by positivity)
        exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)
      _ = (32/a^2)*(s^3*t/Real.sqrt r) := by
        field_simp [ha.ne', hs.ne', (Real.sqrt_pos.2 hrp).ne'] <;> ring
      _ = _ := by
        congr 1
        dsimp [s, t]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hrp.le, ← Real.rpow_add hrp,
          Real.sqrt_eq_rpow, ← Real.rpow_sub hrp]
        norm_num
  have ht' : t ≤ r := by
    dsimp [t]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hr₁ (show (3/8:ℝ) ≤ 1 by norm_num))
  have houter :
      2*Real.exp B*((k:ℝ)*Real.exp (-(a/B)*Real.sqrt M/16)) ≤
        2*r^2*Real.exp (-(a/32)*r^(15/32:ℝ)) := by
    have hke : Real.exp B*(k:ℝ) ≤ r*r :=
      mul_le_mul (hBe.trans ht') hk (Nat.cast_nonneg _) hrp.le
    rw [show -(a/B) = -a/B by ring]
    rw [show 2*Real.exp B*((k:ℝ)*Real.exp (-a/B*Real.sqrt M/16)) =
      2*(Real.exp B*(k:ℝ))*Real.exp (-a/B*Real.sqrt M/16) by ring, sq]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hke (by norm_num)) hexp
      (Real.exp_nonneg _) (by positivity)
  exact add_le_add hcentral houter

private theorem tendsto_shiftErrorEnvelope :
    Tendsto shiftErrorEnvelope atTop (𝓝 0) := by
  have ha : 0 < thetaKnot 2/32 := by linarith [thetaKnot_two_pos]
  have hpow := tendsto_rpow_neg_atTop (show (0:ℝ) < 1/32 by norm_num)
  have hcentral : Tendsto (fun r : ℝ => (32/(thetaKnot 2)^2)*r^(-(1/32):ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul _
  have htail := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (64/15:ℝ) (thetaKnot 2/32) ha).comp
    (tendsto_rpow_atTop (show (0:ℝ) < 15/32 by norm_num))
  have htail' : Tendsto (fun r : ℝ => r^2*Real.exp (-(thetaKnot 2/32)*r^(15/32:ℝ))) atTop (𝓝 0) := by
    apply htail.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hr, show (15/32:ℝ)*(64/15)=2 by norm_num]
    simp only [Real.rpow_two]
  unfold shiftErrorEnvelope
  simpa only [mul_assoc, mul_zero, add_zero] using hcentral.add (htail'.const_mul 2)

/-- For all large orders the same vanishing envelope controls every earlier
shift sum in every lower-order block. -/
theorem eventually_earlier_shift_sum_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ M k : ℕ, r-1 ≤ M → k ≤ r → 2*(k-1) ≤ M →
      ∀ u : ℝ, 0 < u → u ≤ shiftCriticalCutoff r →
        (∑ n ∈ Finset.Ico 2 (lastActiveTheta u),
          (Real.sqrt (n:ℝ))⁻¹ * ‖shiftCore M k (thetaKnot n/u)‖) ≤ ε := by
  have hsmall := (tendsto_order.1 tendsto_shiftErrorEnvelope).2 ε hε
  have hel := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hel.eventually eventually_shiftCriticalCutoff_bounds, hel.eventually hsmall] with
    r hr hsmall M k hM hk hdim u hu huB
  have hr₂ : 2 ≤ r := by exact_mod_cast hr.1
  have hM' : (r:ℝ)-1 ≤ M := by
    have h : (r:ℝ) ≤ (M:ℝ)+1 := by exact_mod_cast (show r ≤ M+1 by omega)
    linarith
  exact (norm_earlier_shift_sum_le (by omega) hdim hu huB).trans
    ((shiftEarlierError_le_envelope hr.1 hM' (by exact_mod_cast hk) hr.2.1 hr.2.2.1 hr.2.2.2).trans hsmall.le)

#print axioms eventually_earlier_shift_sum_le

end Nuttall
