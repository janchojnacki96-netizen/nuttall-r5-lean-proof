import Mathlib

/-!
A first formal theorem for outward rounding on an integer lattice.

For D>0, integer Euclidean division computes the floor of a/D.
Using the floor of -a gives a corresponding ceiling.

These lemmas are genuine Lean proofs; they do not yet validate the
full 768-bit interval evaluator, its exponential routine, or the
255 certified theta inequalities.
-/

namespace W5

theorem int_ediv_le_rat_div (a D : ℤ) (hD : 0 < D) :
    (((a / D : ℤ) : ℚ)) ≤ (a : ℚ) / (D : ℚ) := by
  have hbound := Int.ediv_mul_le a (ne_of_gt hD)
  have hq : (((a / D : ℤ) : ℚ)) * (D : ℚ) ≤ (a : ℚ) := by
    exact_mod_cast hbound
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  exact (le_div_iff₀ hDq).mpr hq

theorem rat_div_le_int_ceil (a D : ℤ) (hD : 0 < D) :
    (a : ℚ) / (D : ℚ) ≤
      ((-((-a) / D : ℤ) : ℤ) : ℚ) := by
  let q : ℤ := (-a) / D
  have hbound := Int.ediv_mul_le (-a) (ne_of_gt hD)
  have hq : (q : ℚ) * (D : ℚ) ≤ -(a : ℚ) := by
    dsimp [q]
    exact_mod_cast hbound
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hq' : (a : ℚ) ≤ (-(q : ℚ)) * (D : ℚ) := by
    nlinarith
  have hres := (div_le_iff₀ hDq).mpr hq'
  simpa [q] using hres

end W5
