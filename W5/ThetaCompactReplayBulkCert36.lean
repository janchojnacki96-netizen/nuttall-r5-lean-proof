import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith36
import W5.ThetaCompactReplayBulkGamma36

namespace W5

theorem thetaOriginalCell36_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[35]!) (endpoints[35]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell36
    ((0::endpoints)[35]!) (endpoints[35]!)
    thetaCompactReplayCell36_arithmetic thetaCompactReplayCell36_gamma
    (by native_decide) (by native_decide)

end W5
