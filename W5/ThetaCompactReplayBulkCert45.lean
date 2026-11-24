import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith45
import W5.ThetaCompactReplayBulkGamma45

namespace W5

theorem thetaOriginalCell45_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[44]!) (endpoints[44]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell45
    ((0::endpoints)[44]!) (endpoints[44]!)
    thetaCompactReplayCell45_arithmetic thetaCompactReplayCell45_gamma
    (by native_decide) (by native_decide)

end W5
