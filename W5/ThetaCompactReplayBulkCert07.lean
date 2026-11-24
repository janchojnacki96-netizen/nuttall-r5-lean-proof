import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith07
import W5.ThetaCompactReplayBulkGamma07

namespace W5

theorem thetaOriginalCell07_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[6]!) (endpoints[6]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell07
    ((0::endpoints)[6]!) (endpoints[6]!)
    thetaCompactReplayCell07_arithmetic thetaCompactReplayCell07_gamma
    (by native_decide) (by native_decide)

end W5
