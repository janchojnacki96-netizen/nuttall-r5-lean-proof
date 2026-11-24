import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith24
import W5.ThetaCompactReplayBulkGamma24

namespace W5

theorem thetaOriginalCell24_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[23]!) (endpoints[23]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell24
    ((0::endpoints)[23]!) (endpoints[23]!)
    thetaCompactReplayCell24_arithmetic thetaCompactReplayCell24_gamma
    (by native_decide) (by native_decide)

end W5
