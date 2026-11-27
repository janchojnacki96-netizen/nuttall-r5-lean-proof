import Nuttall.PsiCompactQuadrature
import Nuttall.PhiCompactExponential

namespace Nuttall

open W5

private def compactPositiveExpBox (t : ℚ) : QInterval :=
  QInterval.inversePositive (phiCompactExpBox t t)

private theorem compactPositiveExpBox_containsReal {t : ℚ} (ht : 0 ≤ t) (ht₁ : t ≤ 16)
    (hpos : 0 < (phiCompactExpBox t t).lo) :
    (compactPositiveExpBox t).ContainsReal (Real.exp (t:ℝ)) := by
  have h := phiCompactExpBox_containsReal ht ht₁ (le_refl (t:ℝ)) (le_refl (t:ℝ))
  rw [Real.exp_neg] at h
  simpa only [compactPositiveExpBox, inv_inv] using QInterval.inversePositive_containsReal h hpos

private def compactPiBox : QInterval := ⟨3.14159265358979323846, 3.14159265358979323847⟩

private theorem compactPiBox_containsReal : compactPiBox.ContainsReal Real.pi := by
  constructor <;> norm_num [compactPiBox]
  · have h := Real.pi_gt_d20.le
    norm_num at h
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num at h
    exact h

private def compactThetaCoordinateBox (t : ℚ) : QInterval :=
  QInterval.mul compactPiBox (compactPositiveExpBox (4*t))

private def compactThetaGaussianBox (t : ℚ) : QInterval :=
  let X := compactThetaCoordinateBox t
  let B := phiCompactExpBox (X.lo/2) (X.hi/2)
  QInterval.mul B B

/-- All exponential inputs to the compact jet evaluator at a rational time
are evaluated using the existing sound exponential boxes. -/
def psiGridPhiJetBox (t : ℚ) (j N : ℕ) : QInterval :=
  phiCompactJetBox (compactPositiveExpBox t) (compactThetaCoordinateBox t)
    (compactThetaGaussianBox t) j N

/-- The finite conditions on the exponential enclosures are executable
comparisons on rational endpoints. -/
def psiGridExpChecks (t : ℚ) : Prop :=
  0 < (phiCompactExpBox t t).lo ∧
  0 < (phiCompactExpBox (4*t) (4*t)).lo ∧
  0 ≤ (compactThetaCoordinateBox t).lo ∧ (compactThetaCoordinateBox t).hi ≤ 32 ∧
  0 ≤ (compactThetaGaussianBox t).lo

instance (t : ℚ) : Decidable (psiGridExpChecks t) := by
  unfold psiGridExpChecks
  infer_instance

theorem psiGridPhiJetBox_containsReal {t : ℚ} (h₀ : 0 ≤ t) (h₂ : t ≤ 2)
    (hcheck : psiGridExpChecks t) (j N : ℕ) (hN : 1 ≤ N) :
    (psiGridPhiJetBox t j N).ContainsReal (iteratedDeriv j Phi (t:ℝ)) := by
  obtain ⟨hEpos, hTpos, hXlo, hXhi, hGlo⟩ := hcheck
  have hE := compactPositiveExpBox_containsReal h₀ (by linarith) hEpos
  have hT := compactPositiveExpBox_containsReal (t := 4*t) (by positivity) (by linarith) hTpos
  let X := compactThetaCoordinateBox t
  let x := Real.pi * Real.exp (4*(t:ℝ))
  have hX : X.ContainsReal x := by
    simpa only [X, x, compactThetaCoordinateBox, Rat.cast_mul, Rat.cast_ofNat] using
      QInterval.mul_containsReal compactPiBox_containsReal hT
  have hlo : ((X.lo/2:ℚ):ℝ) ≤ x/2 := by
    simp only [Rat.cast_div, Rat.cast_ofNat]
    exact div_le_div_of_nonneg_right hX.1 (by norm_num)
  have hhi : x/2 ≤ ((X.hi/2:ℚ):ℝ) := by
    simp only [Rat.cast_div, Rat.cast_ofNat]
    exact div_le_div_of_nonneg_right hX.2 (by norm_num)
  have hqHalf := phiCompactExpBox_containsReal (div_nonneg hXlo (by norm_num))
    (by linarith only [hXhi]) hlo hhi
  have hG : (compactThetaGaussianBox t).ContainsReal (Real.exp (-x)) := by
    have he : Real.exp (-(x/2)) * Real.exp (-(x/2)) = Real.exp (-x) := by
      rw [← Real.exp_add, show -(x/2) + -(x/2) = -x by ring]
    simpa only [compactThetaGaussianBox, X, he] using QInterval.mul_containsReal hqHalf hqHalf
  exact phiCompactJetBox_containsReal (by exact_mod_cast h₀) (by exact_mod_cast h₂)
    hE hX hG hXlo hGlo j N hN

#print axioms psiGridPhiJetBox_containsReal

end Nuttall
