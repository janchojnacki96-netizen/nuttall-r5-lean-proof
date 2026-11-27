import Nuttall.SignedKernelCriterion
import Nuttall.PsiSmoothness

namespace Nuttall

open scoped ContDiff

/-- The weak reverse sign condition in the definition of m(r) in §1.
Both sets of nodes are strictly increasing and positive. -/
def reverseSignRegular (f : ℝ → ℝ) (r : ℕ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → p ≤ r → ∀ x y : Fin p → ℝ,
    StrictMono x → StrictMono y → (∀ i, 0 < x i) → (∀ j, 0 < y j) →
    0 ≤ kernelMinorSign p * (Matrix.of (fun (i j : Fin p) => f (x i+y j))).det

/-- The strict variant of the kernel minor test. -/
def strictReverseSignRegular (f : ℝ → ℝ) (r : ℕ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → p ≤ r → ∀ x y : Fin p → ℝ,
    StrictMono x → StrictMono y → (∀ i, 0 < x i) → (∀ j, 0 < y j) →
    0 < kernelMinorSign p * (Matrix.of (fun (i j : Fin p) => f (x i+y j))).det

theorem strictReverseSignRegular.reverseSignRegular {f : ℝ → ℝ} {r : ℕ}
    (h : strictReverseSignRegular f r) : reverseSignRegular f r :=
  fun p hp hpr x y hx hy hx₀ hy₀ => (h p hp hpr x y hx hy hx₀ hy₀).le

theorem reverseSignRegular.mono {f : ℝ → ℝ} {r R : ℕ}
    (h : reverseSignRegular f R) (hr : r ≤ R) : reverseSignRegular f r :=
  fun p hp hpr => h p hp (hpr.trans hr)

/-- The strict Hankel Wronskian condition implies the strict sign of
every addition-kernel minor of the same rank. -/
theorem signRegularWronskians.strictReverseSignRegular {m r : ℕ}
    (h : signRegularWronskians m r) : strictReverseSignRegular (psi m) r := by
  intro p hp hpr x y hx hy hx₀ hy₀
  cases p with
  | zero => omega
  | succ n =>
    have hs : (↑(2*n) : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl (2*n)
    exact signed_kernel_evaluation_pos ((contDiff_psi m).of_le hs)
      (fun p hp hpn t ht => h p hp (hpn.trans hpr) t ht.le) x y hx hy hx₀ hy₀

/-- The least integration level with weak reverse sign regularity, with
value infinity if the set of successful levels is empty. -/
noncomputable def kernelIntegrationOrder (r : ℕ) : ℕ∞ :=
  ⨅ m : {m : ℕ // reverseSignRegular (psi m) r}, (m.val : ℕ∞)

theorem kernelIntegrationOrder_le_of_reverseSignRegular {m r : ℕ}
    (h : reverseSignRegular (psi m) r) : kernelIntegrationOrder r ≤ m :=
  iInf_le (fun m : {m : ℕ // reverseSignRegular (psi m) r} => (m.val : ℕ∞)) ⟨m,h⟩

theorem kernelIntegrationOrder_mono : Monotone kernelIntegrationOrder := by
  intro r R hr
  unfold kernelIntegrationOrder
  apply le_iInf
  intro m
  exact kernelIntegrationOrder_le_of_reverseSignRegular (m.property.mono hr)

/-- When there is a successful level, the infimum is achieved by the least one. -/
theorem kernelIntegrationOrder_attained_of_exists {r : ℕ}
    (h : ∃ m : ℕ, reverseSignRegular (psi m) r) :
    ∃ m : ℕ, kernelIntegrationOrder r = m ∧ reverseSignRegular (psi m) r := by
  classical
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  apply le_antisymm (kernelIntegrationOrder_le_of_reverseSignRegular (Nat.find_spec h))
  apply le_iInf
  intro m
  exact_mod_cast (Nat.find_min' h m.property)

/-- The existing finite rank-five Wronskian certificate supplies the
weak kernel condition at level one. Kept as a bridge so importing the
analytic upper bound does not trigger a replay of the finite certificate. -/
theorem reverseSignRegular_psi_one_of_mainClaim (h : W5.MainClaim) :
    reverseSignRegular (psi 1) 5 := by
  apply strictReverseSignRegular.reverseSignRegular
  apply signRegularWronskians.strictReverseSignRegular
  intro p hp hpr t ht
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h t ht
  rw [wronskian_psi_one]
  interval_cases p <;> norm_num <;> linarith only [h₁, h₂, h₃, h₄, h₅]

theorem kernelIntegrationOrder_five_le_one_of_mainClaim (h : W5.MainClaim) :
    kernelIntegrationOrder 5 ≤ 1 :=
  kernelIntegrationOrder_le_of_reverseSignRegular (reverseSignRegular_psi_one_of_mainClaim h)

#print axioms signRegularWronskians.strictReverseSignRegular
#print axioms kernelIntegrationOrder_attained_of_exists
#print axioms kernelIntegrationOrder_five_le_one_of_mainClaim

end Nuttall
