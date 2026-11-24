import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith14
import W5.ThetaCompactReplayBulkGamma14

namespace W5

theorem thetaOriginalCell14_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[13]!) (endpoints[13]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell14
    ((0::endpoints)[13]!) (endpoints[13]!)
    thetaCompactReplayCell14_arithmetic thetaCompactReplayCell14_gamma
    (by native_decide) (by native_decide)

end W5
