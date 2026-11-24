import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith28
import W5.ThetaCompactReplayBulkGamma28

namespace W5

theorem thetaOriginalCell28_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[27]!) (endpoints[27]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell28
    ((0::endpoints)[27]!) (endpoints[27]!)
    thetaCompactReplayCell28_arithmetic thetaCompactReplayCell28_gamma
    (by native_decide) (by native_decide)

end W5
