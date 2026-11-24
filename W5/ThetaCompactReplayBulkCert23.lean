import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith23
import W5.ThetaCompactReplayBulkGamma23

namespace W5

theorem thetaOriginalCell23_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[22]!) (endpoints[22]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell23
    ((0::endpoints)[22]!) (endpoints[22]!)
    thetaCompactReplayCell23_arithmetic thetaCompactReplayCell23_gamma
    (by native_decide) (by native_decide)

end W5
