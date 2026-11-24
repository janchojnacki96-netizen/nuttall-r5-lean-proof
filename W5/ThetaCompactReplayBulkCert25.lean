import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith25
import W5.ThetaCompactReplayBulkGamma25

namespace W5

theorem thetaOriginalCell25_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[24]!) (endpoints[24]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell25
    ((0::endpoints)[24]!) (endpoints[24]!)
    thetaCompactReplayCell25_arithmetic thetaCompactReplayCell25_gamma
    (by native_decide) (by native_decide)

end W5
