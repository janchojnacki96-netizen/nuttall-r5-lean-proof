import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith29
import W5.ThetaCompactReplayBulkGamma29

namespace W5

theorem thetaOriginalCell29_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[28]!) (endpoints[28]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell29
    ((0::endpoints)[28]!) (endpoints[28]!)
    thetaCompactReplayCell29_arithmetic thetaCompactReplayCell29_gamma
    (by native_decide) (by native_decide)

end W5
