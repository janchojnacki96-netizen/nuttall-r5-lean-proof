import W5.Theta51ExplicitMatrixChecker
import W5.ThetaAuditedAll255FinitePivotChecks

/-!
# Connect the actual 768-bit interval matrices to the 51-cell real-theta theorem

This module combines two previously separate formal developments:
* the 51 imported upper-triangular interval matrices from the independent
  integer auditor, whose 255 finite rational LDL pivot signs are checked by
  `thetaAuditAll51PivotTests_true`;
* the generic 51-cell real enclosure / matrix-sign reduction from
  `Theta51ExplicitMatrixChecker`.

The bridge performs NO new rational pivot computations. It merely proves
that the imported upper-triangle matrices reconstruct exactly the same
symmetric matrices on which the existing verified Boolean test was run.

The remaining `ThetaCellMatricesEnclose` hypothesis is explicit and
substantial: proving that these fixed rational intervals uniformly enclose
the actual transcendental theta coefficients is still required. This
module does NOT prove the unconditional Nuttall R5 claim.
-/

namespace W5

/-- Upper-triangle inputs in the precise original audit cell order.
The underlying 51 constants are imported; none are copied or recomputed. -/
def thetaAuditUpperCellMatrices : List ThetaIntervalMatrix := [
  thetaAuditUpperCell_01,
  thetaAuditUpperCell_02,
  thetaAuditUpperCell_03,
  thetaAuditUpperCell_04,
  thetaAuditUpperCell_05,
  thetaAuditUpperCell_06,
  thetaAuditUpperCell_07,
  thetaAuditUpperCell_08,
  thetaAuditUpperCell_09,
  thetaAuditUpperCell_10,
  thetaAuditUpperCell_11,
  thetaAuditUpperCell_12,
  thetaAuditUpperCell_13,
  thetaAuditUpperCell_14,
  thetaAuditUpperCell_15,
  thetaAuditUpperCell_16,
  thetaAuditUpperCell_17,
  thetaAuditUpperCell_18,
  thetaAuditUpperCell_19,
  thetaAuditUpperCell_20,
  thetaAuditUpperCell_21,
  thetaAuditUpperCell_22,
  thetaAuditUpperCell_23,
  thetaAuditUpperCell_24,
  thetaAuditUpperCell_25,
  thetaAuditUpperCell_26,
  thetaAuditUpperCell_27,
  thetaAuditUpperCell_28,
  thetaAuditUpperCell_29,
  thetaAuditUpperCell_30,
  thetaAuditUpperCell_31,
  thetaAuditUpperCell_32,
  thetaAuditUpperCell_33,
  thetaAuditUpperCell_34,
  thetaAuditUpperCell_35,
  thetaAuditUpperCell_36,
  thetaAuditUpperCell_37,
  thetaAuditUpperCell_38,
  thetaAuditUpperCell_39,
  thetaAuditUpperCell_40,
  thetaAuditUpperCell_41,
  thetaAuditUpperCell_42,
  thetaAuditUpperCell_43,
  thetaAuditUpperCell_44,
  thetaAuditUpperCell_45,
  thetaAuditUpperCell_46,
  thetaAuditUpperCell_47,
  thetaAuditUpperCell_48,
  thetaAuditUpperCell_49,
  thetaAuditUpperCell_50,
  thetaAuditUpperCell_51
]

/-- The two existing representations of the same 51 matrices coincide
by definition. No matrix entries or numerical constants are duplicated. -/
theorem thetaAuditUpperCellMatrices_map :
    thetaAuditUpperCellMatrices.map thetaSymmetricIntervals =
      thetaAuditCellMatrices := by
  rfl

/-- A length-matched cell-wise Boolean test is the ordinary list
`all` of those same 51 pivot tests. This is generic and independent
of the size or precision of the imported rational matrices. -/
theorem thetaCellMatricesCheck_eq_all_of_length (bs : List ℚ) :
    ∀ (Cs : List ThetaIntervalMatrix),
      bs.length = Cs.length →
        thetaCellMatricesCheck bs Cs =
          (Cs.map thetaSymmetricIntervals).all
            intervalLDL5AlternatingCheck := by
  induction bs with
  | nil =>
      intro Cs hlen
      cases Cs with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons _ bs ih =>
      intro Cs hlen
      cases Cs with
      | nil => simp at hlen
      | cons C Cs =>
          have htail : bs.length = Cs.length := by
            simpa using Nat.succ.inj hlen
          simp [thetaCellMatricesCheck, ih Cs htail]

/-- The actual imported upper-triangle inputs pass the generic
51-cell checker, using ONLY the previously verified 255-pivot result.
In particular, this does not run the expensive test twice. -/
theorem thetaAuditUpperCellMatrices_checked :
    theta51MatricesCheck thetaAuditUpperCellMatrices = true := by
  have hlen : endpoints.length = thetaAuditUpperCellMatrices.length := by
    decide
  calc
    theta51MatricesCheck thetaAuditUpperCellMatrices =
        (thetaAuditUpperCellMatrices.map thetaSymmetricIntervals).all
          intervalLDL5AlternatingCheck :=
      thetaCellMatricesCheck_eq_all_of_length
        endpoints thetaAuditUpperCellMatrices hlen
    _ = thetaAuditAll51PivotTests := by
      rw [thetaAuditUpperCellMatrices_map]
      rfl
    _ = true := thetaAuditAll51PivotTests_true

/-- Concrete rational 768-bit finite-pivot signs are now fully
discharged. The single remaining hypothesis for this particular
matrix-positivity statement is the UNIFORM analytic enclosure of
the 15 genuine theta coefficients on each of the 51 cells. -/
theorem analyticMatrixPositive_of_audited_768bit_enclosures
    (hreal : ThetaCellMatricesEnclose 0 endpoints
      thetaAuditUpperCellMatrices) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_51_checked_matrices
    thetaAuditUpperCellMatrices
    thetaAuditUpperCellMatrices_checked hreal

end W5
