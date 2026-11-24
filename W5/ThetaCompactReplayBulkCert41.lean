import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith41
import W5.ThetaCompactReplayBulkGamma41

namespace W5

theorem thetaOriginalCell41_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[40]!) (endpoints[40]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell41
    ((0::endpoints)[40]!) (endpoints[40]!)
    thetaCompactReplayCell41_arithmetic thetaCompactReplayCell41_gamma
    (by native_decide) (by native_decide)

end W5
