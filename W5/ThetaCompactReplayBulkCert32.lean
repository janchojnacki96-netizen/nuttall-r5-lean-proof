import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith32
import W5.ThetaCompactReplayBulkGamma32

namespace W5

theorem thetaOriginalCell32_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[31]!) (endpoints[31]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell32
    ((0::endpoints)[31]!) (endpoints[31]!)
    thetaCompactReplayCell32_arithmetic thetaCompactReplayCell32_gamma
    (by native_decide) (by native_decide)

end W5
