import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith42
import W5.ThetaCompactReplayBulkGamma42

namespace W5

theorem thetaOriginalCell42_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[41]!) (endpoints[41]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell42
    ((0::endpoints)[41]!) (endpoints[41]!)
    thetaCompactReplayCell42_arithmetic thetaCompactReplayCell42_gamma
    (by native_decide) (by native_decide)

end W5
