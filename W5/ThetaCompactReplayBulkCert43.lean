import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith43
import W5.ThetaCompactReplayBulkGamma43

namespace W5

theorem thetaOriginalCell43_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[42]!) (endpoints[42]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell43
    ((0::endpoints)[42]!) (endpoints[42]!)
    thetaCompactReplayCell43_arithmetic thetaCompactReplayCell43_gamma
    (by native_decide) (by native_decide)

end W5
