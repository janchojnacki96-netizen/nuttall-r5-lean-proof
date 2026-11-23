import LeanCert.Tactic

/-!
Small proof-carrying compatibility check for LeanCert on the same
Lean 4.35.0 / Mathlib v4.35.0 as the Nuttall R5 repository.
No R5 sign claim is made by this test.
-/

namespace W5

/-- A basic transcendental inequality checked by LeanCert. -/
theorem leanCert_exp_one_lt_three : Real.exp 1 < 3 := by
  leancert

#print axioms W5.leanCert_exp_one_lt_three

end W5
