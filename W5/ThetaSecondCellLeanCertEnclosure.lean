import W5.LeanCertSmoke
import W5.ThetaSecondCellHeadFiniteMajorants

/-!
# The actual second-cell theta head: LeanCert scalar enclosure test

The exact-rational bound for all (i,j) is already native_decide-checked
in ThetaSecondCellHeadFiniteMajorants. This module tests whether LeanCert
can prove the TRANSENDENTAL scalar interval bound that then combines
with that rational coefficient majorant. It does NOT by itself prove
the bound for the original integral or original series term; that
separate semantic link is under development in PR #139.
-/

namespace W5

/-- Harder parameter-dependent exponential inequality on an actual
part of the second audited x-cell. The interval is not a sampled grid. -/
theorem leanCert_second_cell_n2_exp_bound :
    ∀ x : ℝ, x ∈ Set.Icc ((1 : ℝ)/4) (177/512) →
      (5000000 : ℝ) * Real.exp (-(3/x^2)) ≤ (1 : ℝ)/200 := by
  leancert

/-- Reuse an EXISTING native_decide rational cap for all 25
matrix positions, with the numerical real bound proved by LeanCert. -/
theorem leanCert_second_cell_n2_head_majorant
    (x : ℝ) (hx : x ∈ Set.Icc ((1 : ℝ)/4) (177/512))
    (i j : Fin 5) :
    (thetaHeadPositiveMajorant (1/4) (177/512) 2 i j : ℝ) *
      Real.exp (-(3/x^2)) ≤ (1 : ℝ)/200 := by
  have hrat := (thetaSecondCellHeadPositiveMajorants_checked i j).2.1
  have hcap :
      (thetaHeadPositiveMajorant (1/4) (177/512) 2 i j : ℝ) ≤ 5000000 := by
    exact_mod_cast hrat
  calc
    _ ≤ (5000000 : ℝ) * Real.exp (-(3/x^2)) :=
      mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
    _ ≤ (1 : ℝ)/200 := leanCert_second_cell_n2_exp_bound x hx

#print axioms W5.leanCert_second_cell_n2_exp_bound
#print axioms W5.leanCert_second_cell_n2_head_majorant

end W5
