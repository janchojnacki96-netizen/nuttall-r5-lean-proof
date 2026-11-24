import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith09
import W5.ThetaCompactReplayBulkGamma09

namespace W5

theorem thetaOriginalCell09_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[8]!) (endpoints[8]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell09
    ((0::endpoints)[8]!) (endpoints[8]!)
    thetaCompactReplayCell09_arithmetic thetaCompactReplayCell09_gamma
    (by native_decide) (by native_decide)

end W5
