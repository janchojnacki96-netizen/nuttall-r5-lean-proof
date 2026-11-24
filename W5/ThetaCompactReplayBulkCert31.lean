import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith31
import W5.ThetaCompactReplayBulkGamma31

namespace W5

theorem thetaOriginalCell31_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[30]!) (endpoints[30]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell31
    ((0::endpoints)[30]!) (endpoints[30]!)
    thetaCompactReplayCell31_arithmetic thetaCompactReplayCell31_gamma
    (by native_decide) (by native_decide)

end W5
