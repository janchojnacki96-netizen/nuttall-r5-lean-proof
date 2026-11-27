import Nuttall.ShiftOperatorBound
import Nuttall.ShiftedThetaAlgebra

namespace Nuttall

open scoped Matrix.Norms.L2Operator

/-- A simpler positive denominator for summing the central part of eq:shift. -/
theorem shiftCentral_denominator_le {d : ℝ} (hd : 0 < d) (hd₁ : d < 1) :
    d^2*Real.sqrt (1-d) ≤ (1-(shiftScale d)^2)*shiftCosine d*d := by
  have hp : 0 < 1+d := by linarith
  have hm : 0 < 1-d := by linarith
  have hs : 1-(shiftScale d)^2 = 2*d/(1+d) := by
    unfold shiftScale
    rw [Real.sq_sqrt (div_nonneg hm.le hp.le)]
    field_simp
    ring
  have hc : shiftCosine d = Real.sqrt (1-d)*Real.sqrt (1+d) := by
    unfold shiftCosine
    rw [show 1-d^2 = (1-d)*(1+d) by ring, Real.sqrt_mul hm.le]
  have hg : Real.sqrt (1+d) ≤ 2 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> linarith
  have hmul : ((1-(shiftScale d)^2)*shiftCosine d*d)*Real.sqrt (1+d) =
      2*(d^2*Real.sqrt (1-d)) := by
    rw [hs, hc]
    have hsqrt := Real.sq_sqrt hp.le
    calc
      _ = (2*d^2*Real.sqrt (1-d))*((Real.sqrt (1+d))^2/(1+d)) := by ring
      _ = _ := by rw [hsqrt, div_self hp.ne', mul_one, mul_assoc]
  have hpos : 0 < Real.sqrt (1+d) := Real.sqrt_pos.2 hp
  apply (le_of_mul_le_mul_right _ hpos)
  rw [hmul]
  exact (mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (by ring)

/-- The version of eq:shift used for the sum of earlier positive shifts. -/
theorem norm_shiftCore_le_earlierTerms {M k : ℕ} {d : ℝ}
    (hM : 0 < M) (hd : 0 < d) (hd₁ : d < 1) (hk : 2*(k-1) ≤ M) :
    ‖shiftCore M k d‖ ≤ 2/(d^2*Real.sqrt (1-d)*Real.sqrt M) +
      (k:ℝ)*Real.exp (-d*Real.sqrt M/16) := by
  apply (norm_shiftCore_le_eq_shift hM hd hd₁ hk).trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_left (by norm_num)
  · have hm : 0 < 1-d := sub_pos.2 hd₁
    have hMr : (0:ℝ) < M := by exact_mod_cast hM
    positivity
  · exact mul_le_mul_of_nonneg_right (shiftCentral_denominator_le hd hd₁) (Real.sqrt_nonneg _)

/-- The distance to a knot is at least the difference in the integer indices
divided by the upper scale, including when the endpoint is itself a knot. -/
theorem shiftKnot_gap_lower {B u : ℝ} {n K : ℕ} (hu : 0 < u) (huB : u ≤ B)
    (hn : 0 < n) (hnK : n ≤ K) (hK : (K:ℝ) ≤ Real.exp (2*u)) :
    ((K:ℝ)-n)/(2*B*Real.exp (2*B)) ≤ 1-thetaKnot n/u := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hx : 0 < Real.exp (2*u) := Real.exp_pos _
  have hB := hu.trans_le huB
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn' hx)
  rw [Real.log_div hn'.ne' hx.ne', Real.log_exp] at hlog
  have hnum : (K:ℝ)-n ≤ (2*u-Real.log (n:ℝ))*Real.exp (2*u) := by
    have h := mul_le_mul_of_nonneg_right hlog hx.le
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hx.ne', one_mul] at h
    linarith
  have hden : 0 < 2*u*Real.exp (2*u) := by positivity
  have hden' : 0 < 2*B*Real.exp (2*B) := by positivity
  have hratio : ((K:ℝ)-n)/(2*u*Real.exp (2*u)) ≤ 1-thetaKnot n/u := by
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ (2*u-Real.log (n:ℝ))*Real.exp (2*u) := hnum
      _ = _ := by
        unfold thetaKnot
        field_simp
  apply le_trans _ hratio
  apply div_le_div_of_nonneg_left (sub_nonneg.2 (by exact_mod_cast hnK)) hden
  exact mul_le_mul (by linarith) (Real.exp_le_exp.2 (by linarith)) hx.le (by positivity)

#print axioms shiftCentral_denominator_le
#print axioms norm_shiftCore_le_earlierTerms
#print axioms shiftKnot_gap_lower

end Nuttall
