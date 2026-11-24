import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith40
import W5.ThetaCompactReplayBulkGamma40

namespace W5

theorem thetaOriginalCell40_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[39]!) (endpoints[39]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell40
    ((0::endpoints)[39]!) (endpoints[39]!)
    thetaCompactReplayCell40_arithmetic thetaCompactReplayCell40_gamma
    (by native_decide) (by native_decide)

end W5
