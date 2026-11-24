import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith20
import W5.ThetaCompactReplayBulkGamma20

namespace W5

theorem thetaOriginalCell20_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[19]!) (endpoints[19]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell20
    ((0::endpoints)[19]!) (endpoints[19]!)
    thetaCompactReplayCell20_arithmetic thetaCompactReplayCell20_gamma
    (by native_decide) (by native_decide)

end W5
