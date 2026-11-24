import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith44
import W5.ThetaCompactReplayBulkGamma44

namespace W5

theorem thetaOriginalCell44_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[43]!) (endpoints[43]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell44
    ((0::endpoints)[43]!) (endpoints[43]!)
    thetaCompactReplayCell44_arithmetic thetaCompactReplayCell44_gamma
    (by native_decide) (by native_decide)

end W5
