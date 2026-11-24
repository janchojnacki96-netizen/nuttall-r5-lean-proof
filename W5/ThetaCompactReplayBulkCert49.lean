import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith49
import W5.ThetaCompactReplayBulkGamma49

namespace W5

theorem thetaOriginalCell49_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[48]!) (endpoints[48]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell49
    ((0::endpoints)[48]!) (endpoints[48]!)
    thetaCompactReplayCell49_arithmetic thetaCompactReplayCell49_gamma
    (by native_decide) (by native_decide)

end W5
