import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith46
import W5.ThetaCompactReplayBulkGamma46

namespace W5

theorem thetaOriginalCell46_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[45]!) (endpoints[45]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell46
    ((0::endpoints)[45]!) (endpoints[45]!)
    thetaCompactReplayCell46_arithmetic thetaCompactReplayCell46_gamma
    (by native_decide) (by native_decide)

end W5
