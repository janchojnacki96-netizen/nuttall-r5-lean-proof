import W5.ThetaClosedKernelAllJets

/-!
# Equality of every leading matrix minor of the genuine analytic
theta-jet matrix and the exact closed-series jet matrix

The previous local-germ theorem transfers every mixed derivative
at the origin. This module packages those entrywise identities into
literal matrix equalities and determinant identities for all sizes
1 <= r <= 5 (also valid for r=0).

The new matrices are comprised of genuine iterated derivatives of
the exact closed theta series. They are NOT the separately defined
numerical `thetaCoefficient` matrices: differentiation through the
infinite theta sum and improper integral remains to be established.
-/

namespace W5

/-- The mixed jet of the exact closed theta series kernel, normalized
by factorials to match the original `analyticCoeff` definition. -/
noncomputable def closedThetaJetCoeff (t : ℝ) (i j : Fin 5) : ℝ :=
  (iteratedDeriv i.val
    (fun u : ℝ => iteratedDeriv j.val
      (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) 0) 0) /
    ((Nat.factorial i.val : ℝ) * (Nat.factorial j.val : ℝ))

theorem analyticCoeff_eq_closedThetaJetCoeff
    (t : ℝ) (ht : 0 ≤ t) (i j : Fin 5) :
    analyticCoeff (xOfT t) i j = closedThetaJetCoeff t i j := by
  exact analyticCoeff_eq_closedThetaKernel_jet t ht i j

/-- Exact matrix identity for each leading principal r x r block,
for every r <= 5. -/
theorem analyticMatrix_eq_closedThetaMatrix
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : r ≤ 5) :
    (Matrix.of (fun (i j : Fin r) =>
      analyticCoeff (xOfT t)
        ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) =
    (Matrix.of (fun (i j : Fin r) =>
      closedThetaJetCoeff t
        ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)) := by
  ext i j
  exact analyticCoeff_eq_closedThetaJetCoeff t ht
    ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- Every leading determinant of the ORIGINAL normalized analytic
kernel equals that of the exact closed theta series jet kernel.
No sign, numerical certificate, or limit-interchange assumption. -/
theorem analyticDet_eq_closedThetaDet
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : r ≤ 5) :
    (Matrix.of (fun (i j : Fin r) =>
      analyticCoeff (xOfT t)
        ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det =
    (Matrix.of (fun (i j : Fin r) =>
      closedThetaJetCoeff t
        ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det := by
  exact congrArg Matrix.det
    (analyticMatrix_eq_closedThetaMatrix t ht r hr)

end W5
