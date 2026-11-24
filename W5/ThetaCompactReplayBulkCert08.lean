import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith08
import W5.ThetaCompactReplayBulkGamma08

namespace W5

theorem thetaOriginalCell08_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[7]!) (endpoints[7]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell08
    ((0::endpoints)[7]!) (endpoints[7]!)
    thetaCompactReplayCell08_arithmetic thetaCompactReplayCell08_gamma
    (by native_decide) (by native_decide)

end W5
