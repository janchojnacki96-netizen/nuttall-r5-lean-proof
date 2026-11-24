import W5.ThetaLastCellCompactDyadicPivot
import W5.ThetaLastCellCompactDyadicGaussian
import W5.ThetaLastCellCompactDyadicGammaA
import W5.ThetaLastCellCompactDyadicGammaB
import W5.ThetaLastCellCompactDyadicFit
import W5.ThetaLastCellReplaySoundness

namespace W5

theorem thetaLastCellN1Eligible_checked : thetaLastCellN1Eligible = true := by
  unfold thetaLastCellN1Eligible
  apply decide_eq_true
  exact ⟨by norm_num [thetaLastCellA], by norm_num [thetaLastCellA, thetaLastCellB],
    by norm_num [thetaLastCellB], thetaLastCellGaussianEligible_checked,
    thetaLastCellGammaA_checked, thetaLastCellGammaB_checked⟩

theorem thetaLastCellDyadicCertificate :
    ThetaUpperRealCellCertificate thetaLastCellA thetaLastCellB := by
  apply thetaUpperRealCellCertificate_of_checked thetaLastCellA thetaLastCellB
    thetaLastCellWitness thetaLastCellWitnessLDL
  intro x hx hax hxb i j hij
  exact thetaUpperMatrixRefines_containsReal thetaLastCellWitness
    thetaLastCellReplaySource thetaLastCellWitnessFits
    (thetaCoefficient x i j) i j hij
    (thetaLastCellReplaySource_containsReal x hx hax hxb i j)

/-- The dyadic interval contains the slightly rounded original cell. -/
theorem thetaLastCellCertificate :
    ThetaUpperRealCellCertificate (endpoints.reverse.drop 1).head! endpoints.reverse.head! := by
  have ha : thetaLastCellA ≤ (endpoints.reverse.drop 1).head! := by native_decide
  have hb : endpoints.reverse.head! = thetaLastCellB := by native_decide
  obtain ⟨C, hldl, hC⟩ := thetaLastCellDyadicCertificate
  refine ⟨C, hldl, ?_⟩
  intro x hx hax hxb i j hij
  have haR : (thetaLastCellA:ℝ) ≤ (((endpoints.reverse.drop 1).head! : ℚ):ℝ) := by
    exact_mod_cast ha
  exact hC x hx (haR.trans hax) (by simpa only [hb] using hxb) i j hij

end W5
