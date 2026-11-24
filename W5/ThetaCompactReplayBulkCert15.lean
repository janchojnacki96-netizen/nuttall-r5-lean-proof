import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith15
import W5.ThetaCompactReplayBulkGamma15

namespace W5

theorem thetaOriginalCell15_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[14]!) (endpoints[14]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell15
    ((0::endpoints)[14]!) (endpoints[14]!)
    thetaCompactReplayCell15_arithmetic thetaCompactReplayCell15_gamma
    (by native_decide) (by native_decide)

end W5
