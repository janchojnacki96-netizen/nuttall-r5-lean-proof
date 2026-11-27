import Nuttall.PsiCompactGridPrefix
import Nuttall.SmallIntegrationOrdersFromCompact

namespace Nuttall

/-- Each uniform prefix cell uses the same endpoint convention as the analytic certificate. -/
theorem psiOneCompactPrefix_cell_index {ab : ℚ × ℚ} (hab : ab ∈ psiOneCompactPrefix) :
    ∃ i : Fin 53, ab = ((i.val:ℚ)/128, ((i.val+1:ℕ):ℚ)/128) := by
  have h : psiOneCompactPrefix = List.ofFn (fun i : Fin 53 =>
      ((i.val:ℚ)/128, ((i.val+1:ℕ):ℚ)/128)) := by decide +kernel
  rw [h, List.mem_ofFn'] at hab
  obtain ⟨i, hi⟩ := hab
  exact ⟨i, hi.symm⟩

/-- The final assembly can consume one theorem for each numerical cell. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_prefix_replay {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ i : Fin 53, ∀ p ≤ 7, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 := by
  apply kernelIntegrationOrder_eq_one_of_psiOne_compact_prefix hr₅ hr₇
  intro ab hab
  obtain ⟨i, rfl⟩ := psiOneCompactPrefix_cell_index hab
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hcell i

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_prefix_replay

end Nuttall
