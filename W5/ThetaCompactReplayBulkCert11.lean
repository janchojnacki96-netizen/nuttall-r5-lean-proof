import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith11
import W5.ThetaCompactReplayBulkGamma11

namespace W5

theorem thetaOriginalCell11_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[10]!) (endpoints[10]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell11
    ((0::endpoints)[10]!) (endpoints[10]!)
    thetaCompactReplayCell11_arithmetic thetaCompactReplayCell11_gamma
    (by native_decide) (by native_decide)

end W5
