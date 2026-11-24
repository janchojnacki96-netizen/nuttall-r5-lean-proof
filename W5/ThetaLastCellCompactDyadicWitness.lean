import W5.ThetaLastCellCompactDyadicPivot
import W5.ThetaLastCellCompactDyadicGaussian
import W5.ThetaLastCellCompactDyadicGammaA
import W5.ThetaLastCellCompactDyadicGammaB
import W5.ThetaLastCellCompactDyadicFit

namespace W5

theorem thetaLastCellN1Eligible_checked : thetaLastCellN1Eligible = true := by
  unfold thetaLastCellN1Eligible
  apply decide_eq_true
  exact ⟨by norm_num [thetaLastCellA], by norm_num [thetaLastCellA, thetaLastCellB],
    by norm_num [thetaLastCellB], thetaLastCellGaussianEligible_checked,
    thetaLastCellGammaA_checked, thetaLastCellGammaB_checked⟩

theorem thetaLastCellDyadicCertificate :
    ThetaUpperRealCellCertificate thetaLastCellA thetaLastCellB := by
  have h : (0:ℚ) < thetaLastCellA ∧ thetaLastCellA ≤ thetaLastCellB ∧
      thetaLastCellB ≤ (145:ℚ)/256 ∧
      ThetaBulkGaussianEligibility thetaLastCellA thetaLastCellB ∧
      thetaGammaAutoMomentCheck 8 thetaLastCellA thetaLastCellGrid = true ∧
      thetaGammaAutoMomentCheck 8 thetaLastCellB thetaLastCellGrid = true :=
    of_decide_eq_true thetaLastCellN1Eligible_checked
  rcases h with ⟨ha, _, hb, hExp, hA, hB⟩
  apply thetaUpperRealCellCertificate_of_checked thetaLastCellA thetaLastCellB
    thetaLastCellWitness thetaLastCellWitnessLDL
  intro x hx hax hxb i j hij
  have hbR : (thetaLastCellB:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (thetaLastCellB:ℝ) ≤ (((145:ℚ)/256):ℝ) := by exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  apply thetaUpperMatrixRefines_containsReal thetaLastCellWitness
    thetaLastCellCachedUpperSource
    (thetaUpperMatrixRefinesCheck_sound _ _ thetaLastCellWitnessFits)
    (thetaCoefficient x i j) i j hij
  rw [thetaLastCellCachedUpperSource_apply i j hij]
  exact thetaLastCellN1OnlySource_containsReal 8 thetaLastCellGrid
    thetaLastCellA thetaLastCellB x ha hx hax hxb hbR hExp hA hB i j

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
