import Nuttall.PsiCompactPrecisionSeed
import Nuttall.PsiCompactRemainder
import Nuttall.PsiOneTailBound

namespace Nuttall

open MeasureTheory Set
open scoped ContDiff

/-- A panel advances Ψ₂ using its right endpoint, the right value of Ψ₁,
and a weighted integral of Φ. -/
theorem psi_two_eq_panel (a b : ℝ) :
    psi 2 a = psi 2 b + (b-a) * psi 1 b +
      ∫ x in a..b, (x-a) * W5.Phi x := by
  let f (x : ℝ) := psi 2 x + (x-a) * psi 1 x
  have hd (x : ℝ) : HasDerivAt f (-((x-a) * psi 0 x)) x := by
    have h := (psi_succ_hasDerivAt 1 x).add
      (((hasDerivAt_id x).sub_const a).mul (psi_succ_hasDerivAt 0 x))
    convert h using 1
    · rfl
    · change -((x-a) * psi 0 x) =
        -psi 1 x + (1 * psi 1 x + (x-a) * -psi 0 x)
      ring
  have hc : Continuous fun x : ℝ => -((x-a) * psi 0 x) :=
    ((continuous_id.sub continuous_const).mul (psi_continuous 0)).neg
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hc.intervalIntegrable a b)
  rw [intervalIntegral.integral_neg] at h
  change -(∫ x in a..b, (x-a) * W5.Phi x) = f b - f a at h
  unfold f at h
  linarith only [h, show (a-a) * psi 1 a = 0 by ring]

/-- The seed for Ψ₁ is also an upper bound for Ψ₂ at the right boundary. -/
theorem psi_two_precise_compact_seed_bounds :
    0 ≤ psi 2 (11/16) ∧ psi 2 (11/16) ≤ 1/10^16 := by
  let t : ℝ := 11/16
  have ht : 0 ≤ t := by norm_num [t]
  have he : 1 ≤ Real.exp (4*t) := Real.one_le_exp (by positivity)
  have hcoord := mul_le_mul Real.pi_gt_three.le he (by norm_num) Real.pi_pos.le
  have hl := psi_one_ge_auxiliary_mul_rate t 2 ht (by norm_num)
    (by linarith only [hcoord])
  have h₁ := twice_psi_one_eq_auxiliary_sub_tail t ht
  have h₂ := twice_psi_succ_eq_auxiliary_iterate_sub 1 t ht
  change 2 * psi 2 t = tailIntegral auxiliaryTheta t -
    tailIntegral (tailIntegral auxiliaryTheta) t at h₂
  have hnonneg : 0 ≤ tailIntegral (tailIntegral auxiliaryTheta) t :=
    integral_nonneg (fun _ => integral_nonneg auxiliaryTheta_nonneg)
  have hc : psi 2 t ≤ psi 1 t := by linarith only [h₁, h₂, hl, hnonneg]
  exact ⟨(psi_pos 2 t ht).le, hc.trans
    (psi_one_precise_compact_seed_bounds (t := t) le_rfl (by norm_num [t])).2⟩

/-- Uniform Taylor error for all entries of the scaled rank-eight Hankel matrix. -/
theorem psi_two_compact_scaled_error_le (l : ℕ) (hl : l ≤ 14) {c h v : ℝ}
    (ha : 0 ≤ c-h) (hb : c+h ≤ 2) (hh : 0 ≤ h) (hh' : h ≤ 1/256) (hv : |v| ≤ 1) :
    |(1/16:ℝ)^l * (iteratedDeriv l (psi 2) (c+h*v) -
      cellTaylor (iteratedDeriv l (psi 2)) 23 c h v)| ≤ (1:ℝ)/10^18 := by
  obtain ⟨hcont, hdiff⟩ := contDiff_iff_iteratedDeriv.mp (contDiff_psi 2)
  have hjet : ContDiff ℝ (24:ℕ) (iteratedDeriv l (psi 2)) := by
    apply contDiff_iff_iteratedDeriv.mpr
    constructor
    · intro k _
      rw [iteratedDeriv_iteratedDeriv_eq]
      exact hcont _ (by simp)
    · intro k _
      rw [iteratedDeriv_iteratedDeriv_eq]
      exact hdiff _ (by simp)
  have hD (x : ℝ) (hx : x ∈ Icc (c-h) (c+h)) :
      |iteratedDeriv (23+1) (iteratedDeriv l (psi 2)) x| ≤
      (((22+l).factorial : ℝ) * 8^(22+l)) * 10^6 := by
    rw [iteratedDeriv_iteratedDeriv_eq, show 23+1+l = (22+l)+1+1 by omega,
      show (2:ℕ) = (0+1)+1 by rfl, iteratedDeriv_succ_psi_succ,
      iteratedDeriv_succ_psi_succ, neg_neg]
    simpa only [Real.norm_eq_abs, psi] using iteratedDeriv_phi_compact_norm_le (22+l)
      (ha.trans hx.1) (hx.2.trans hb)
  have herr := cellTaylor_error_le hjet hh hv (by positivity) hD
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1/16:ℝ)^l)]
  refine (mul_le_mul_of_nonneg_left herr (by positivity)).trans ?_
  have hp : h^24 ≤ (1/256:ℝ)^24 := pow_le_pow_left₀ hh hh' 24
  refine (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)) (by positivity)).trans ?_
  interval_cases l <;> norm_num [Nat.factorial]

#print axioms psi_two_eq_panel
#print axioms psi_two_precise_compact_seed_bounds
#print axioms psi_two_compact_scaled_error_le

end Nuttall
