import W5.ThetaIteratedChainRule
import W5.Statement

/-!
# Actual Wronskian determinant in the theta x-coordinate

Unlike a pointwise derivative identity, this theorem identifies the
determinant of the ORIGINAL Psi1 with a determinant built from the
theta-coordinate differential operator. The equality is conditional
only on a genuine representation Psi1 = f ∘ xOfT and the explicitly
listed smoothness assumptions on f. No sign assumption is inserted.
-/

namespace W5

/-- Theta-coordinate determinant of a candidate representation f. -/
noncomputable def thetaWronskian (r : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Matrix.of (fun (i j : Fin r) =>
    ((thetaDerivOp^[i.val + j.val]) f) x)).det

/-- For any matrix size, the ORIGINAL Wronskian is exactly the
theta-coordinate determinant, provided Psi1 has the specified
representation and enough intermediate derivatives exist. -/
theorem W_eq_thetaWronskian_of_representation
    (r : ℕ) (f : ℝ → ℝ)
    (hrep : ∀ t : ℝ, Psi1 t = f (xOfT t))
    (hf : ∀ k < 2*r, Differentiable ℝ ((thetaDerivOp^[k]) f))
    (t : ℝ) :
    W r t = thetaWronskian r f (xOfT t) := by
  unfold W thetaWronskian
  congr 1
  apply Matrix.ext
  intro i j
  have hsmall :
      ∀ k < i.val + j.val,
        Differentiable ℝ ((thetaDerivOp^[k]) f) := by
    intro k hk
    exact hf k (by omega)
  have hfun : Psi1 = fun s : ℝ => f (xOfT s) := by
    funext s
    exact hrep s
  simpa only [hfun, Matrix.of_apply] using
    (congrFun (iteratedDeriv_comp_xOfT f
      (i.val + j.val) hsmall) t)

/-- Specialized order-five identity: no derivatives beyond order
eight are needed. The k<9 smoothness assumption is explicit. -/
theorem W_five_eq_thetaWronskian
    (f : ℝ → ℝ)
    (hrep : ∀ t : ℝ, Psi1 t = f (xOfT t))
    (hf : ∀ k < 9, Differentiable ℝ ((thetaDerivOp^[k]) f))
    (t : ℝ) :
    W 5 t = thetaWronskian 5 f (xOfT t) := by
  unfold W thetaWronskian
  congr 1
  apply Matrix.ext
  intro i j
  have hfun : Psi1 = fun s : ℝ => f (xOfT s) := by
    funext s
    exact hrep s
  simpa only [hfun, Matrix.of_apply] using
    (wronskian_five_entry_comp_xOfT f hf i j t)

end W5
