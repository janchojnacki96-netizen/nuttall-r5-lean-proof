import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith21
import W5.ThetaCompactReplayBulkGamma21

namespace W5

theorem thetaOriginalCell21_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[20]!) (endpoints[20]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell21
    ((0::endpoints)[20]!) (endpoints[20]!)
    thetaCompactReplayCell21_arithmetic thetaCompactReplayCell21_gamma
    (by native_decide) (by native_decide)

end W5
