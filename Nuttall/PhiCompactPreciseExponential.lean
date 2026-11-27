import W5.ThetaBulkFixedExponential
import Nuttall.CompactFixedPolynomial

namespace Nuttall

open W5
open scoped BigOperators

private def reducedExpCoefficients : List ℚ :=
  List.ofFn fun k : Fin 65 => 1/(k.val.factorial:ℚ)

private theorem reducedExpCoefficients_eval (x : ℝ) :
    compactFixedRealEval reducedExpCoefficients x = thetaExpTaylor65 x := by
  rw [reducedExpCoefficients, compactFixedRealEval_ofFn, thetaExpTaylor65]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun k => (1/(k.factorial:ℝ))*x^k) 65]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private def reducedExpPartial (a : ℚ) : QInterval :=
  (compactFixedHorner thetaAuditScale (compactFixedRound thetaAuditScale (QInterval.point (a/1024)))
    reducedExpCoefficients).asQInterval thetaAuditScale

private def reducedExpPositiveBox (a : ℚ) : QInterval :=
  let P := reducedExpPartial a
  ⟨P.lo, P.hi + 2 / (3^65 * (Nat.factorial 65:ℚ))⟩

private theorem reducedExpPositiveBox_containsReal {a : ℚ} (ha : 0 ≤ a) (hb : a ≤ 1024/3) :
    (reducedExpPositiveBox a).ContainsReal (Real.exp ((a:ℝ)/1024)) := by
  have ha' : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hb' : (a:ℝ) ≤ 1024/3 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) hb)
  have hpoint : (QInterval.point (a/1024)).ContainsReal ((a:ℝ)/1024) := by
    simp [QInterval.point, QInterval.ContainsReal]
  have h := compactFixedHorner_containsReal thetaAuditScale thetaAuditScale_pos
    (compactFixedRound_containsReal thetaAuditScale_pos hpoint) reducedExpCoefficients
  rw [reducedExpCoefficients_eval] at h
  have he := thetaExpTaylor65_interval_contains_real_exp ((a:ℝ)/1024)
    (by positivity) (by linarith only [hb']) (reducedExpPartial a) h
  simpa only [reducedExpPositiveBox, QInterval.ContainsReal, Rat.cast_add, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_div] using he

private def compactExpNegPoint (a : ℚ) : QInterval :=
  (thetaBulkFixedPow2 10
    (compactFixedRound thetaAuditScale (reducedExpPositiveBox a).inversePositive)).asQInterval thetaAuditScale

private theorem compactExpNegPoint_containsReal {a : ℚ} (ha : 0 ≤ a) (hb : a ≤ 1024/3)
    (hpos : 0 < (reducedExpPositiveBox a).lo) :
    (compactExpNegPoint a).ContainsReal (Real.exp (-(a:ℝ))) := by
  have hi := QInterval.inversePositive_containsReal (reducedExpPositiveBox_containsReal ha hb) hpos
  rw [← Real.exp_neg] at hi
  have hs := compactFixedRound_containsReal thetaAuditScale_pos hi
  have hp := thetaBulkFixedPow2_containsReal _ _ hs 10
  have he : (Real.exp (-((a:ℝ)/1024)))^(2^10) = Real.exp (-(a:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num <;> ring
  rw [he] at hp
  exact hp

/-- Evaluate exponential point enclosures using the same integer Horner grid as the jets. -/
def phiCompactPreciseExpBox (a b : ℚ) : QInterval :=
  compactRoundInterval (10^23) ⟨(compactExpNegPoint b).lo, (compactExpNegPoint a).hi⟩

def phiCompactPreciseExpChecks (a b : ℚ) : Prop :=
  0 ≤ a ∧ a ≤ b ∧ b ≤ 1024/3 ∧
    0 < (reducedExpPositiveBox a).lo ∧ 0 < (reducedExpPositiveBox b).lo

instance (a b : ℚ) : Decidable (phiCompactPreciseExpChecks a b) := by
  unfold phiCompactPreciseExpChecks
  infer_instance

theorem phiCompactPreciseExpBox_containsReal {a b : ℚ} {x : ℝ}
    (hcheck : phiCompactPreciseExpChecks a b) (hlo : (a:ℝ) ≤ x) (hhi : x ≤ (b:ℝ)) :
    (phiCompactPreciseExpBox a b).ContainsReal (Real.exp (-x)) := by
  obtain ⟨ha, hab, hb, hapos, hbpos⟩ := hcheck
  have ha' := compactExpNegPoint_containsReal ha (hab.trans hb) hapos
  have hb' := compactExpNegPoint_containsReal (ha.trans hab) hb hbpos
  unfold phiCompactPreciseExpBox
  apply compactRoundInterval_containsReal (by positivity)
  exact ⟨hb'.1.trans (Real.exp_le_exp.mpr (neg_le_neg hhi)),
    (Real.exp_le_exp.mpr (neg_le_neg hlo)).trans ha'.2⟩

#print axioms phiCompactPreciseExpBox_containsReal

end Nuttall
