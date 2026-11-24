import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith12
import W5.ThetaCompactReplayBulkGamma12

namespace W5

theorem thetaOriginalCell12_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[11]!) (endpoints[11]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell12
    ((0::endpoints)[11]!) (endpoints[11]!)
    thetaCompactReplayCell12_arithmetic thetaCompactReplayCell12_gamma
    (by native_decide) (by native_decide)

end W5
