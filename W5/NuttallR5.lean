import W5.ThetaCompactReplayBulkComplete
import W5.ThetaAllMixedFullTransform
import W5.ThetaNormalizationFinalSignTransfer

/-! Final assembly of the analytic and certified interval proof. -/
namespace W5

theorem nuttall_r5 : MainClaim :=
  mainClaim_of_transform_and_matrix
    thetaTransformCorrect_allMixed analyticMatrixPositive_compactReplay

#print axioms nuttall_r5

end W5
