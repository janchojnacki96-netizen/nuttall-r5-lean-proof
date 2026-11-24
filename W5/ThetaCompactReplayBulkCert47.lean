import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith47
import W5.ThetaCompactReplayBulkGamma47

namespace W5

theorem thetaOriginalCell47_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[46]!) (endpoints[46]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell47
    ((0::endpoints)[46]!) (endpoints[46]!)
    thetaCompactReplayCell47_arithmetic thetaCompactReplayCell47_gamma
    (by native_decide) (by native_decide)

end W5
