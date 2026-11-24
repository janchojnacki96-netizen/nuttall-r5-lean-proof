import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith22
import W5.ThetaCompactReplayBulkGamma22

namespace W5

theorem thetaOriginalCell22_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[21]!) (endpoints[21]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell22
    ((0::endpoints)[21]!) (endpoints[21]!)
    thetaCompactReplayCell22_arithmetic thetaCompactReplayCell22_gamma
    (by native_decide) (by native_decide)

end W5
