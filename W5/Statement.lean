import Mathlib

/-! Riemann theta kernel and Wronskian sign target. -/
namespace W5
open MeasureTheory

noncomputable def phiSummand (n : ℕ) (t : ℝ) : ℝ :=
  (2 * (n : ℝ)^4 * Real.pi^2 * Real.exp (9*t) -
    3 * (n : ℝ)^2 * Real.pi * Real.exp (5*t)) *
    Real.exp (-(n : ℝ)^2 * Real.pi * Real.exp (4*t))

noncomputable def Phi (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else phiSummand n t

noncomputable def Psi1 (t : ℝ) : ℝ :=
  ∫ s in Set.Ici t, Phi s ∂MeasureTheory.volume

noncomputable def W (r : ℕ) (t : ℝ) : ℝ :=
  (Matrix.of (fun (i j : Fin r) =>
    iteratedDeriv (i.val + j.val) Psi1 t)).det

def MainClaim : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    0 < W 1 t ∧ W 2 t < 0 ∧ W 3 t < 0 ∧
    0 < W 4 t ∧ 0 < W 5 t

noncomputable def xOfT (t : ℝ) : ℝ :=
  1 / Real.sqrt (Real.pi * Real.exp (4*t))
end W5
