import Nuttall.PhiRankEightTransfer
import Nuttall.TailWronskianPersistence

namespace Nuttall

open scoped Nat

private theorem phiThetaCoordinate_strictMono : StrictMono phiThetaCoordinate := by
  intro t s hts
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith only [hts])) Real.pi_pos

/-- At points strictly beyond the normalized tail cutoff, the original
kernel and every successive tail integral have the signed Wronskians. -/
theorem psi_signed_wronskian_pos_of_thetaCoordinate_gt (m : ℕ) {p : ℕ}
    (hp : p ≤ 8) {t : ℝ} (ht : 16 < phiThetaCoordinate t) :
    0 < kernelMinorSign p * wronskian (psi m) p t := by
  let a := Real.log (16/Real.pi)/4
  have ha : phiThetaCoordinate a = 16 := by
    have he : 4*a = Real.log (16/Real.pi) := by dsimp [a]; ring
    rw [phiThetaCoordinate, he, Real.exp_log (by positivity : 0 < 16/Real.pi)]
    field_simp [Real.pi_ne_zero]
  have hbase : a < t := phiThetaCoordinate_strictMono.lt_iff_lt.mp (by rwa [ha])
  have htail (k : ℕ) : ∀ (r : ℕ), r ≤ 8 → ∀ s > a,
      0 < kernelMinorSign r * wronskian (psi k) r s := by
    induction k with
    | zero =>
      intro r hr s hs
      have hc := (phiThetaCoordinate_strictMono hs).le
      rw [ha] at hc
      exact phiRankEightFarWronskian_pos hr s hc
    | succ k ih =>
      intro r hr s hs
      cases r with
      | zero => simp [kernelMinorSign, wronskian]
      | succ n =>
        exact psi_succ_signed_wronskian_pos_on_tail k n hs
          (fun p hp t ht => ih p (hp.trans hr) t ht)
  exact htail m p hp t hbase

/-- The first compact-grid endpoint strictly beyond the analytic cutoff. -/
theorem sixteen_lt_phiThetaCoordinate_at_compact_endpoint :
    16 < phiThetaCoordinate (53/128) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 53/32) 6
  have he' : (51:ℝ)/10 ≤ Real.exp (53/32) := by
    refine le_trans ?_ he
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  unfold phiThetaCoordinate
  rw [show (4:ℝ)*(53/128) = 53/32 by norm_num]
  calc
    _ < (3.14:ℝ)*(51/10) := by norm_num
    _ ≤ Real.pi * Real.exp (53/32) :=
      mul_le_mul Real.pi_gt_d2.le he' (by norm_num) Real.pi_pos.le

/-- Beyond 53/128, sign certification needs no compact grid calculations. -/
theorem psi_signed_wronskian_pos_on_compact_tail (m : ℕ) {p : ℕ} (hp : p ≤ 8)
    {t : ℝ} (ht : 53/128 ≤ t) : 0 < kernelMinorSign p * wronskian (psi m) p t :=
  psi_signed_wronskian_pos_of_thetaCoordinate_gt m hp
    (sixteen_lt_phiThetaCoordinate_at_compact_endpoint.trans_le
      (phiThetaCoordinate_strictMono.monotone ht))

theorem psi_signed_wronskian_pos_on_half_tail (m : ℕ) {p : ℕ} (hp : p ≤ 8)
    {t : ℝ} (ht : 1/2 ≤ t) : 0 < kernelMinorSign p * wronskian (psi m) p t :=
  psi_signed_wronskian_pos_on_compact_tail m hp ((by norm_num : (53:ℝ)/128 ≤ 1/2).trans ht)

/-- Attach any compact certificate of rank at most eight to the analytic tail. -/
theorem signRegularWronskians_of_compact_le_eight (m r : ℕ) (hr : r ≤ 8)
    (hcompact : ∀ p ≤ r, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi m) p t) :
    signRegularWronskians m r := by
  intro p _ hp t ht
  by_cases h : t ≤ 53/128
  · exact hcompact p hp t ht h
  · exact psi_signed_wronskian_pos_on_compact_tail m (hp.trans hr) (le_of_lt (lt_of_not_ge h))

#print axioms psi_signed_wronskian_pos_on_half_tail

end Nuttall
