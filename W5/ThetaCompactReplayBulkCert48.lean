import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith48
import W5.ThetaCompactReplayBulkGamma48

namespace W5

theorem thetaOriginalCell48_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[47]!) (endpoints[47]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell48
    ((0::endpoints)[47]!) (endpoints[47]!)
    thetaCompactReplayCell48_arithmetic thetaCompactReplayCell48_gamma
    (by native_decide) (by native_decide)

end W5
