import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith13
import W5.ThetaCompactReplayBulkGamma13

namespace W5

theorem thetaOriginalCell13_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[12]!) (endpoints[12]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell13
    ((0::endpoints)[12]!) (endpoints[12]!)
    thetaCompactReplayCell13_arithmetic thetaCompactReplayCell13_gamma
    (by native_decide) (by native_decide)

end W5
