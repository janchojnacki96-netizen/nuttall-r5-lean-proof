import W5.Statement

namespace Nuttall

open MeasureTheory

noncomputable def tailIntegral (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Set.Ici t, f s ∂volume

noncomputable def psi : ℕ → ℝ → ℝ
  | 0 => W5.Phi
  | m + 1 => tailIntegral (psi m)

theorem psi_one : psi 1 = W5.Psi1 := rfl

noncomputable def wronskian (f : ℝ → ℝ) (p : ℕ) (t : ℝ) : ℝ :=
  (Matrix.of (fun (i j : Fin p) => iteratedDeriv (i.val + j.val) f t)).det

theorem wronskian_psi_one (p : ℕ) (t : ℝ) :
    wronskian (psi 1) p t = W5.W p t := rfl

def signRegularWronskians (m r : ℕ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → p ≤ r → ∀ t : ℝ, 0 ≤ t →
    0 < (-1 : ℝ) ^ (p * (p - 1) / 2) * wronskian (psi m) p t

/-- The last step of Theorem 1.2. The analytic estimate from Section 4.1
is an explicit hypothesis. -/
theorem exists_level_of_eventual_two_mul
    (h : ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ R →
      signRegularWronskians (2 * R) R)
    (r : ℕ) (hr : 1 ≤ r) :
    ∃ m : ℕ, signRegularWronskians m r := by
  obtain ⟨R₀, hR₀⟩ := h
  let R := max r R₀
  have hrR : r ≤ R := le_max_left _ _
  have hR : signRegularWronskians (2 * R) R :=
    hR₀ R (le_max_right _ _) (hr.trans hrR)
  exact ⟨2 * R, fun p hp hpr t ht => hR p hp (hpr.trans hrR) t ht⟩

#print axioms exists_level_of_eventual_two_mul

end Nuttall
