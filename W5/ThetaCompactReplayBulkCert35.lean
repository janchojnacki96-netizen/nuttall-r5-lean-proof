import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith35
import W5.ThetaCompactReplayBulkGamma35

namespace W5

theorem thetaOriginalCell35_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[34]!) (endpoints[34]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell35
    ((0::endpoints)[34]!) (endpoints[34]!)
    thetaCompactReplayCell35_arithmetic thetaCompactReplayCell35_gamma
    (by native_decide) (by native_decide)

end W5
