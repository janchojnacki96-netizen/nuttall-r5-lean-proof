import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith26
import W5.ThetaCompactReplayBulkGamma26

namespace W5

theorem thetaOriginalCell26_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[25]!) (endpoints[25]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell26
    ((0::endpoints)[25]!) (endpoints[25]!)
    thetaCompactReplayCell26_arithmetic thetaCompactReplayCell26_gamma
    (by native_decide) (by native_decide)

end W5
