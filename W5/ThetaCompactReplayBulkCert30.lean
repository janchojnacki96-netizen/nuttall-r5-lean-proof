import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith30
import W5.ThetaCompactReplayBulkGamma30

namespace W5

theorem thetaOriginalCell30_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[29]!) (endpoints[29]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell30
    ((0::endpoints)[29]!) (endpoints[29]!)
    thetaCompactReplayCell30_arithmetic thetaCompactReplayCell30_gamma
    (by native_decide) (by native_decide)

end W5
