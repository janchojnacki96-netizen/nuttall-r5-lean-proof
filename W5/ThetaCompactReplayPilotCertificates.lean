import W5.ThetaRemaining47Reduction
import W5.ThetaCompactReplayPilotArith04
import W5.ThetaCompactReplayPilotGamma04
import W5.ThetaCompactReplayPilotArith27
import W5.ThetaCompactReplayPilotGamma27
import W5.ThetaCompactReplayPilotArith39
import W5.ThetaCompactReplayPilotGamma39
import W5.ThetaCompactReplayPilotArith50
import W5.ThetaCompactReplayPilotGamma50

namespace W5

/-- Reuse the generic checked compact replay proof on audited cell 4. -/
theorem thetaOriginalCell04_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[3]!) (endpoints[3]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell04
    ((0::endpoints)[3]!) (endpoints[3]!)
    thetaCompactReplayCell04_arithmetic thetaCompactReplayCell04_gamma
    (by native_decide) (by native_decide)

/-- Reuse the generic checked compact replay proof on audited cell 27. -/
theorem thetaOriginalCell27_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[26]!) (endpoints[26]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell27
    ((0::endpoints)[26]!) (endpoints[26]!)
    thetaCompactReplayCell27_arithmetic thetaCompactReplayCell27_gamma
    (by native_decide) (by native_decide)

/-- Reuse the generic checked compact replay proof on audited cell 39. -/
theorem thetaOriginalCell39_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[38]!) (endpoints[38]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell39
    ((0::endpoints)[38]!) (endpoints[38]!)
    thetaCompactReplayCell39_arithmetic thetaCompactReplayCell39_gamma
    (by native_decide) (by native_decide)

/-- Reuse the generic checked compact replay proof on audited cell 50. -/
theorem thetaOriginalCell50_compactReplay :
    ThetaUpperRealCellCertificate ((0::endpoints)[49]!) (endpoints[49]!) := by
  exact thetaCompactReplayCertificate_restrict thetaCompactReplayCell50
    ((0::endpoints)[49]!) (endpoints[49]!)
    thetaCompactReplayCell50_arithmetic thetaCompactReplayCell50_gamma
    (by native_decide) (by native_decide)

end W5
