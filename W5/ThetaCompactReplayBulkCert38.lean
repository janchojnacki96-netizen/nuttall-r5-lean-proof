import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith38
import W5.ThetaCompactReplayBulkGamma38

namespace W5

theorem thetaOriginalCell38_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[37]!) (endpoints[37]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell38
    ((0::endpoints)[37]!) (endpoints[37]!)
    thetaCompactReplayCell38_arithmetic thetaCompactReplayCell38_gamma
    (by native_decide) (by native_decide)

end W5
