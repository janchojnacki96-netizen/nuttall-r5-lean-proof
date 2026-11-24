import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith19
import W5.ThetaCompactReplayBulkGamma19

namespace W5

theorem thetaOriginalCell19_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[18]!) (endpoints[18]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell19
    ((0::endpoints)[18]!) (endpoints[18]!)
    thetaCompactReplayCell19_arithmetic thetaCompactReplayCell19_gamma
    (by native_decide) (by native_decide)

end W5
