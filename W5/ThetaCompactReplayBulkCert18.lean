import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith18
import W5.ThetaCompactReplayBulkGamma18

namespace W5

theorem thetaOriginalCell18_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[17]!) (endpoints[17]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell18
    ((0::endpoints)[17]!) (endpoints[17]!)
    thetaCompactReplayCell18_arithmetic thetaCompactReplayCell18_gamma
    (by native_decide) (by native_decide)

end W5
