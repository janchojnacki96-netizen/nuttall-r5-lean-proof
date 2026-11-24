import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayBulkArith34
import W5.ThetaCompactReplayBulkGamma34

namespace W5

theorem thetaOriginalCell34_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[33]!) (endpoints[33]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell34
    ((0::endpoints)[33]!) (endpoints[33]!)
    thetaCompactReplayCell34_arithmetic thetaCompactReplayCell34_gamma
    (by native_decide) (by native_decide)

end W5
