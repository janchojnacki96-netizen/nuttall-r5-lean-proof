import Nuttall.PhiCompactPreciseExponential
import Nuttall.PsiCompactQuadrature

namespace Nuttall

open W5

private def precisePositiveExpBox (t : ℚ) : QInterval :=
  compactRoundInterval (2^90) (QInterval.inversePositive (phiCompactPreciseExpBox t t))

private theorem precisePositiveExpBox_containsReal {t : ℚ}
    (hcheck : phiCompactPreciseExpChecks t t) (hpos : 0 < (phiCompactPreciseExpBox t t).lo) :
    (precisePositiveExpBox t).ContainsReal (Real.exp (t:ℝ)) := by
  have h := phiCompactPreciseExpBox_containsReal hcheck (le_refl (t:ℝ)) (le_refl (t:ℝ))
  rw [Real.exp_neg] at h
  unfold precisePositiveExpBox
  apply compactRoundInterval_containsReal (by positivity)
  simpa only [inv_inv] using QInterval.inversePositive_containsReal h hpos

private def preciseCoordinateBox (t : ℚ) : QInterval :=
  compactRoundInterval (2^90) (QInterval.mul
    ⟨3.14159265358979323846, 3.14159265358979323847⟩ (precisePositiveExpBox (4*t)))

private def preciseGaussianBox (X : QInterval) : QInterval :=
  compactRoundInterval (2^90) (phiCompactPreciseExpBox X.lo X.hi)

def psiPreciseGridChecks (t : ℚ) : Prop :=
  phiCompactPreciseExpChecks t t ∧ 0 < (phiCompactPreciseExpBox t t).lo ∧
  phiCompactPreciseExpChecks (4*t) (4*t) ∧ 0 < (phiCompactPreciseExpBox (4*t) (4*t)).lo ∧
  phiCompactPreciseExpChecks (preciseCoordinateBox t).lo (preciseCoordinateBox t).hi ∧
  0 ≤ (preciseCoordinateBox t).lo ∧ 0 ≤ (preciseGaussianBox (preciseCoordinateBox t)).lo

instance (t : ℚ) : Decidable (psiPreciseGridChecks t) := by
  unfold psiPreciseGridChecks
  infer_instance

/-- Exponential inputs can be checked once at a node and reused for every jet. -/
structure PsiPreciseGridInputs where
  exponential : QInterval
  coordinate : QInterval
  gaussian : QInterval
deriving DecidableEq

def psiPreciseGridInputs (t : ℚ) : PsiPreciseGridInputs :=
  let X := preciseCoordinateBox t
  ⟨precisePositiveExpBox t, X, preciseGaussianBox X⟩

def psiPreciseGridPhiJetBoxOfInputs (inputs : PsiPreciseGridInputs) (j : ℕ) : QInterval :=
  compactRoundInterval (2^90)
    (phiCompactJetBox inputs.exponential inputs.coordinate inputs.gaussian j 8)

/-- Sound high-precision grid jets, for use at both cell centers and quadrature nodes. -/
def psiPreciseGridPhiJetBox (t : ℚ) (j : ℕ) : QInterval :=
  psiPreciseGridPhiJetBoxOfInputs (psiPreciseGridInputs t) j

theorem psiPreciseGridPhiJetBox_containsReal {t : ℚ} (h₀ : 0 ≤ t) (h₂ : t ≤ 2)
    (hcheck : psiPreciseGridChecks t) (j : ℕ) :
    (psiPreciseGridPhiJetBox t j).ContainsReal (iteratedDeriv j Phi (t:ℝ)) := by
  obtain ⟨hE, hEpos, hT, hTpos, hG, hX₀, hG₀⟩ := hcheck
  have hπ : (⟨3.14159265358979323846, 3.14159265358979323847⟩ : QInterval).ContainsReal
      Real.pi := by
    constructor <;> norm_num
    · have h := Real.pi_gt_d20.le
      norm_num at h
      exact h
    · have h := Real.pi_lt_d20.le
      norm_num at h
      exact h
  have hX : (preciseCoordinateBox t).ContainsReal (Real.pi * Real.exp (4*(t:ℝ))) := by
    apply compactRoundInterval_containsReal (by positivity)
    simpa only [Rat.cast_mul, Rat.cast_ofNat] using
      QInterval.mul_containsReal hπ (precisePositiveExpBox_containsReal hT hTpos)
  have hq : (preciseGaussianBox (preciseCoordinateBox t)).ContainsReal
      (Real.exp (-(Real.pi * Real.exp (4*(t:ℝ))))) := by
    exact compactRoundInterval_containsReal (by positivity)
      (phiCompactPreciseExpBox_containsReal hG hX.1 hX.2)
  unfold psiPreciseGridPhiJetBox psiPreciseGridPhiJetBoxOfInputs psiPreciseGridInputs
  apply compactRoundInterval_containsReal (by positivity)
  exact phiCompactJetBox_containsReal (by exact_mod_cast h₀) (by exact_mod_cast h₂)
    (precisePositiveExpBox_containsReal hE hEpos) hX hq hX₀ hG₀ j 8 (by decide)

#print axioms psiPreciseGridPhiJetBox_containsReal

end Nuttall
