import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith17
import W5.ThetaCompactReplayBulkGamma17

namespace W5

theorem thetaOriginalCell17_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[16]!) (endpoints[16]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell17
    ((0::endpoints)[16]!) (endpoints[16]!)
    thetaCompactReplayCell17_arithmetic thetaCompactReplayCell17_gamma
    (by native_decide) (by native_decide)

end W5
