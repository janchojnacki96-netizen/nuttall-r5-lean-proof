import W5.ThetaGammaBinExpNegBox
import Nuttall.CompactIntervalRounding

namespace Nuttall

open W5

/-- The exponential is decreasing in its negated argument, so only the
outer endpoint of each certified point enclosure is needed. -/
def phiCompactPreciseExpBox (a b : ℚ) : QInterval :=
  compactRoundInterval (10^23)
    ⟨(thetaGammaBinExpNegBox b).lo, (thetaGammaBinExpNegBox a).hi⟩

def phiCompactPreciseExpChecks (a b : ℚ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b ≤ 1024/3 ∧
    0 < (thetaBulkExpTaylorBox (QInterval.point (a/1024))).lo ∧
    0 < (thetaBulkExpTaylorBox (QInterval.point (b/1024))).lo

instance (a b : ℚ) : Decidable (phiCompactPreciseExpChecks a b) := by
  unfold phiCompactPreciseExpChecks
  infer_instance

theorem phiCompactPreciseExpBox_containsReal {a b : ℚ} {x : ℝ}
    (hcheck : phiCompactPreciseExpChecks a b) (hlo : (a:ℝ) ≤ x) (hhi : x ≤ (b:ℝ)) :
    (phiCompactPreciseExpBox a b).ContainsReal (Real.exp (-x)) := by
  obtain ⟨ha, hab, hb, hapos, hbpos⟩ := hcheck
  have ha' := thetaGammaBinExpNegBox_containsReal a ha (hab.trans hb) hapos
  have hb' := thetaGammaBinExpNegBox_containsReal b (ha.trans hab) hb hbpos
  unfold phiCompactPreciseExpBox
  apply compactRoundInterval_containsReal (by positivity)
  exact ⟨hb'.1.trans (Real.exp_le_exp.mpr (neg_le_neg hhi)),
    (Real.exp_le_exp.mpr (neg_le_neg hlo)).trans ha'.2⟩

#print axioms phiCompactPreciseExpBox_containsReal

end Nuttall
