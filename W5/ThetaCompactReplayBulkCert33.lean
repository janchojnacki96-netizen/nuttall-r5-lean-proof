import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith33
import W5.ThetaCompactReplayBulkGamma33

namespace W5

theorem thetaOriginalCell33_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[32]!) (endpoints[32]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell33
    ((0::endpoints)[32]!) (endpoints[32]!)
    thetaCompactReplayCell33_arithmetic thetaCompactReplayCell33_gamma
    (by native_decide) (by native_decide)

end W5
