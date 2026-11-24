import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith10
import W5.ThetaCompactReplayBulkGamma10

namespace W5

theorem thetaOriginalCell10_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[9]!) (endpoints[9]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell10
    ((0::endpoints)[9]!) (endpoints[9]!)
    thetaCompactReplayCell10_arithmetic thetaCompactReplayCell10_gamma
    (by native_decide) (by native_decide)

end W5
