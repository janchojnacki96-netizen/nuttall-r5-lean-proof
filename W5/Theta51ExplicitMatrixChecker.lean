import W5.ThetaFiniteDecidableLDLChecker

/-!
# A single executable checker for 51 concrete theta interval matrices

The verified 51-cell covering theorem uses `endpoints`, but the
earlier compact certificate is existential in each cell. Here we
make the numerical inputs EXPLICIT: a list of 51 rational interval
matrices, each containing only 15 independent upper-triangle bounds.

A single Boolean test traverses the list and evaluates all five
exact-rational LDL pivot tests for each matrix. The recursive
soundness proof reuses `intervalLDL5Alternating_of_check`,
`thetaUpperRealCellCertificate_of_checked`, and the already
verified 51-cell coverage theorem.

No numerical matrices are invented. In particular, the remaining
analytic bounds are kept as an explicit, separately auditable
hypothesis, rather than silently assuming them as a Boolean result.
-/

namespace W5

abbrev ThetaIntervalMatrix :=
  Matrix (Fin 5) (Fin 5) QInterval

/-- A Boolean checker for an explicit list of interval matrices
against an explicit list of rational x-cell right endpoints.
Length mismatches are rejected, rather than silently ignored. -/
def thetaCellMatricesCheck :
    List ℚ → List ThetaIntervalMatrix → Bool
  | [], [] => true
  | _ :: bs, C :: Cs =>
      intervalLDL5AlternatingCheck (thetaSymmetricIntervals C) &&
        thetaCellMatricesCheck bs Cs
  | _, _ => false

/-- Real soundness of all upper-triangle interval enclosures
on each x-cell. This is a distinct analytic obligation; the
rational LDL Boolean checker cannot prove transcendental bounds. -/
def ThetaCellMatricesEnclose :
    ℚ → List ℚ → List ThetaIntervalMatrix → Prop
  | _, [], [] => True
  | a, b :: bs, C :: Cs =>
      (∀ x : ℝ, 0 < x →
        (a : ℝ) ≤ x → x ≤ (b : ℝ) →
          ∀ i j : Fin 5, i ≤ j →
            QInterval.ContainsReal (C i j) (thetaCoefficient x i j)) ∧
      ThetaCellMatricesEnclose b bs Cs
  | _, _, _ => False

/-- Soundness of the explicit finite Boolean checker and the
independent real-theta enclosures: together they produce the
already verified compact 15-entry certificate chain. -/
theorem thetaUpperRealCellCertificateChain_of_matrices :
    ∀ (a : ℚ) (bs : List ℚ) (Cs : List ThetaIntervalMatrix),
      thetaCellMatricesCheck bs Cs = true →
      ThetaCellMatricesEnclose a bs Cs →
      ThetaUpperRealCellCertificateChain a bs := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      intro Cs hcheck _
      cases Cs with
      | nil =>
          trivial
      | cons C Cs =>
          simp [thetaCellMatricesCheck] at hcheck
  | cons b bs ih =>
      intro Cs hcheck hbounds
      cases Cs with
      | nil =>
          simp [thetaCellMatricesCheck] at hcheck
      | cons C Cs =>
          have hchecks :
              intervalLDL5AlternatingCheck
                (thetaSymmetricIntervals C) = true ∧
                thetaCellMatricesCheck bs Cs = true := by
            simpa only [thetaCellMatricesCheck, Bool.and_eq_true] using hcheck
          change (∀ x : ℝ, 0 < x →
            (a : ℝ) ≤ x → x ≤ (b : ℝ) →
              ∀ i j : Fin 5, i ≤ j →
                QInterval.ContainsReal (C i j) (thetaCoefficient x i j)) ∧
              ThetaCellMatricesEnclose b bs Cs at hbounds
          change ThetaUpperRealCellCertificate a b ∧
            ThetaUpperRealCellCertificateChain b bs
          exact ⟨thetaUpperRealCellCertificate_of_checked
            a b C hchecks.1 hbounds.1,
            ih b Cs hchecks.2 hbounds.2⟩

/-- THE single finite computational target for the 51 x-cells.
The exact 51 matrices can be emitted as Lean literals by an
independent certificate generator, then verified by reduction
of this Boolean value. -/
def theta51MatricesCheck (Cs : List ThetaIntervalMatrix) : Bool :=
  thetaCellMatricesCheck endpoints Cs

/-- The original analytic theta-matrix leading-minor signs follow
from (1) ONE successful exact-rational Boolean check of all 255
pivots and (2) 51 independently verified uniform analytic
enclosures of the actual theta coefficients.

This does not assume `thetaTransformCorrect` or imply the full
Wronskian conjecture. -/
theorem analyticMatrixPositive_of_51_checked_matrices
    (Cs : List ThetaIntervalMatrix)
    (hcheck : theta51MatricesCheck Cs = true)
    (hreal : ThetaCellMatricesEnclose 0 endpoints Cs) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_51_upper_cell_certificates
  exact thetaUpperRealCellCertificateChain_of_matrices
    0 endpoints Cs hcheck hreal

end W5
