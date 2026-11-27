import Nuttall.ForwardDifferenceKernel
import Nuttall.ForwardDifferenceLimit
import Nuttall.KernelTailPersistence

namespace Nuttall

open Filter Set
open scoped BigOperators ContDiff Topology

private theorem kernelGrid_signed_nonneg {f : ℝ → ℝ} {p r : ℕ}
    (hRR : reverseSignRegular f r) (hp : 1 ≤ p) (hpr : p ≤ r)
    {t h : ℝ} (ht : 0 < t) (hh : 0 < h) :
    0 ≤ kernelMinorSign p *
      (Matrix.of (fun (i j : Fin p) => (fwdDiff h)^[i.val+j.val] f t / h^(i.val+j.val))).det := by
  let u (i : Fin p) : ℝ := t/2+(i.val:ℝ)*h
  have hu : StrictMono u := by
    intro i j hij
    have hij' : (i.val:ℝ) < (j.val:ℝ) := by exact_mod_cast (Fin.lt_def.1 hij)
    dsimp [u]
    linarith only [mul_lt_mul_of_pos_right hij' hh]
  have hu₀ (i : Fin p) : 0 < u i := by dsimp [u]; positivity
  have hRRGrid := hRR p hp hpr u u hu hu hu₀ hu₀
  have hmat : (Matrix.of (fun (i j : Fin p) => f (u i+u j))) =
      Matrix.of (fun (i j : Fin p) => f (t+i.val • h+j.val • h)) := by
    ext i j
    simp only [Matrix.of_apply, u, nsmul_eq_mul]
    congr 1
    ring
  rw [hmat, det_kernelGrid_eq_det_forwardDiff, det_forwardDiff_eq_scaled p f t hh.ne',
    mul_left_comm (kernelMinorSign p)] at hRRGrid
  have hc : 0 < (∏ i : Fin p, h^i.val)^2 :=
    pow_pos (Finset.prod_pos (fun _ _ => pow_pos hh _)) _
  exact (mul_nonneg_iff_of_pos_left hc).1 hRRGrid

private theorem signed_wronskian_nonneg_at_pos {f : ℝ → ℝ} {p r : ℕ}
    (hf : ContDiff ℝ (↑(2*(p-1)) : ℕ∞ω) f)
    (hRR : reverseSignRegular f r) (hp : 1 ≤ p) (hpr : p ≤ r)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ kernelMinorSign p * wronskian f p t := by
  let A (h : ℝ) := Matrix.of (fun (i j : Fin p) => (fwdDiff h)^[i.val+j.val] f t / h^(i.val+j.val))
  let W := Matrix.of (fun (i j : Fin p) => iteratedDeriv (i.val+j.val) f t)
  have hA : Tendsto A (𝓝[>] (0:ℝ)) (𝓝 W) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    have hb : i.val+j.val ≤ 2*(p-1) := by have := i.isLt; have := j.isLt; omega
    exact tendsto_normalized_fwdDiff (hf.of_le (by exact_mod_cast hb)) t
  have hdet : Continuous (fun M : Matrix (Fin p) (Fin p) ℝ => M.det) := continuous_id.matrix_det
  have hh := (hdet.continuousAt (x := W)).tendsto.comp hA
  change 0 ≤ kernelMinorSign p * W.det
  apply ge_of_tendsto (hh.const_mul (kernelMinorSign p))
  filter_upwards [self_mem_nhdsWithin] with h hpos
  exact kernelGrid_signed_nonneg hRR hp hpr ht (mem_Ioi.1 hpos)

/-- Weak reverse sign regularity forces the corresponding signed
Wronskians to be nonnegative, including at the boundary (t=0). -/
theorem signed_wronskian_nonneg_of_reverseSignRegular {f : ℝ → ℝ} {p r : ℕ}
    (hf : ContDiff ℝ (↑(2*(p-1)) : ℕ∞ω) f)
    (hRR : reverseSignRegular f r) (hp : 1 ≤ p) (hpr : p ≤ r)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ kernelMinorSign p * wronskian f p t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    have hc (i j : Fin p) : Continuous (iteratedDeriv (i.val+j.val) f) := by
      apply hf.continuous_iteratedDeriv
      exact_mod_cast (show i.val+j.val ≤ 2*(p-1) by have := i.isLt; have := j.isLt; omega)
    have hM : Continuous (fun x => Matrix.of (fun (i j : Fin p) => iteratedDeriv (i.val+j.val) f x)) :=
      continuous_pi (fun i => continuous_pi (fun j => hc i j))
    have h : Continuous (fun t => kernelMinorSign p * wronskian f p t) :=
      continuous_const.mul hM.matrix_det
    have hlim : Tendsto (fun t => kernelMinorSign p * wronskian f p t) (𝓝[>] (0:ℝ))
        (𝓝 (kernelMinorSign p * wronskian f p 0)) :=
      h.continuousAt.continuousWithinAt.tendsto
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact signed_wronskian_nonneg_at_pos hf hRR hp hpr (mem_Ioi.1 ht)
  · exact signed_wronskian_nonneg_at_pos hf hRR hp hpr ht

/-- A strictly wrong signed Wronskian is a witness against the weak
reverse sign condition at the specified integration level. -/
theorem not_reverseSignRegular_psi_of_negative_wronskian {m p r : ℕ}
    (hp : 1 ≤ p) (hpr : p ≤ r) {t : ℝ} (ht : 0 ≤ t)
    (hneg : kernelMinorSign p * wronskian (psi m) p t < 0) :
    ¬ reverseSignRegular (psi m) r := by
  intro hRR
  have hs : (↑(2*(p-1)) : ℕ∞ω) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl _
  exact hneg.not_ge (signed_wronskian_nonneg_of_reverseSignRegular
    ((contDiff_psi m).of_le hs) hRR hp hpr ht)

/-- A negative witness at level (m) excludes every level up to (m),
because a successful level would stay successful under tail integration. -/
theorem kernelIntegrationOrder_succ_le_of_negative_wronskian {m p r : ℕ}
    (hp : 1 ≤ p) (hpr : p ≤ r) {t : ℝ} (ht : 0 ≤ t)
    (hneg : kernelMinorSign p * wronskian (psi m) p t < 0) :
    ((m+1 : ℕ):ℕ∞) ≤ kernelIntegrationOrder r := by
  apply le_iInf
  intro l
  have hml : m < l.val := by
    apply lt_of_not_ge
    intro hle
    exact not_reverseSignRegular_psi_of_negative_wronskian hp hpr ht hneg
      (reverseSignRegular.psi_of_le hle l.property)
  exact_mod_cast Nat.succ_le_of_lt hml

theorem kernelIntegrationOrder_gt_of_negative_wronskian {m p r : ℕ}
    (hp : 1 ≤ p) (hpr : p ≤ r) {t : ℝ} (ht : 0 ≤ t)
    (hneg : kernelMinorSign p * wronskian (psi m) p t < 0) :
    (m:ℕ∞) < kernelIntegrationOrder r :=
  lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m)
    (kernelIntegrationOrder_succ_le_of_negative_wronskian hp hpr ht hneg)

/-- The rank-five upper certificate and a negative level-zero witness
at the origin suffice for the exact minimum in the weak convention. -/
theorem kernelIntegrationOrder_five_eq_one_of_witnesses (h₁ : W5.MainClaim)
    (h₀ : wronskian W5.Phi 5 0 < 0) :
    kernelIntegrationOrder 5 = 1 := by
  apply le_antisymm (kernelIntegrationOrder_five_le_one_of_mainClaim h₁)
  exact kernelIntegrationOrder_succ_le_of_negative_wronskian (m := 0) (p := 5) (t := 0)
    (by decide) le_rfl le_rfl (by norm_num [kernelMinorSign, psi]; exact h₀)

#print axioms signed_wronskian_nonneg_of_reverseSignRegular
#print axioms not_reverseSignRegular_psi_of_negative_wronskian
#print axioms kernelIntegrationOrder_succ_le_of_negative_wronskian
#print axioms kernelIntegrationOrder_gt_of_negative_wronskian
#print axioms kernelIntegrationOrder_five_eq_one_of_witnesses

end Nuttall
