import W5.FiniteCore
namespace W5
noncomputable def boundaryPivot (k : Fin 5) : ℝ :=
  if k.val % 2 = 0 then 1 / (Nat.factorial k.val : ℝ)
  else -(1 / (Nat.factorial k.val : ℝ))
theorem boundaryPivot_signs :
    PivotSigns (boundaryPivot 0) (boundaryPivot 1)
      (boundaryPivot 2) (boundaryPivot 3) (boundaryPivot 4) := by
  norm_num [PivotSigns, boundaryPivot, Nat.factorial]
end W5
