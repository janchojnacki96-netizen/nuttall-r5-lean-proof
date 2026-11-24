import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith16
import W5.ThetaCompactReplayBulkGamma16

namespace W5

theorem thetaOriginalCell16_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[15]!) (endpoints[15]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell16
    ((0::endpoints)[15]!) (endpoints[15]!)
    thetaCompactReplayCell16_arithmetic thetaCompactReplayCell16_gamma
    (by native_decide) (by native_decide)

end W5
