import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith37
import W5.ThetaCompactReplayBulkGamma37

namespace W5

theorem thetaOriginalCell37_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[36]!) (endpoints[36]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell37
    ((0::endpoints)[36]!) (endpoints[36]!)
    thetaCompactReplayCell37_arithmetic thetaCompactReplayCell37_gamma
    (by native_decide) (by native_decide)

end W5
