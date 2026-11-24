import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith05
import W5.ThetaCompactReplayBulkGamma05

namespace W5

theorem thetaOriginalCell05_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[4]!) (endpoints[4]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell05
    ((0::endpoints)[4]!) (endpoints[4]!)
    thetaCompactReplayCell05_arithmetic thetaCompactReplayCell05_gamma
    (by native_decide) (by native_decide)

end W5
