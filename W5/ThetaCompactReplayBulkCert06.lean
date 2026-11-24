import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith06
import W5.ThetaCompactReplayBulkGamma06

namespace W5

theorem thetaOriginalCell06_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[5]!) (endpoints[5]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell06
    ((0::endpoints)[5]!) (endpoints[5]!)
    thetaCompactReplayCell06_arithmetic thetaCompactReplayCell06_gamma
    (by native_decide) (by native_decide)

end W5
