import Nuttall.CompactFixedPolynomial
import Nuttall.PsiPreciseGridJets

namespace Nuttall

open W5
open scoped BigOperators

private def thetaJetScale : ℤ := 2^768

private theorem thetaJetScale_pos : 0 < thetaJetScale := by
  unfold thetaJetScale
  positivity

private def fixedJetCoefficients (j : ℕ) : List ℚ :=
  List.ofFn (fun k : Fin (j+2) => (phiJetCoeffRow j)[k.val])

private theorem fixedJetCoefficients_eval (j : ℕ) (x : ℝ) :
    compactFixedRealEval (fixedJetCoefficients j) x = (phiJetPolynomial j).eval x := by
  rw [fixedJetCoefficients, compactFixedRealEval_ofFn,
    eval_phiJetPolynomial_of_lt (show j+1 < j+2 by omega)]
  simp only [phiJetCoeffRow_getElem]
  exact Fin.sum_univ_eq_sum_range (fun k => (phiJetCoeff j k:ℝ)*x^k) (j+2)

private def fixedJetTerm (X q : FixedIntInterval) (coeffs : List ℚ) (n : ℕ) :
    FixedIntInterval :=
  let s : ℤ := (n:ℤ)^2
  let Y : FixedIntInterval := ⟨s*X.lo, s*X.hi⟩
  ((Y.mul thetaJetScale (compactFixedHorner thetaJetScale Y coeffs)).mul thetaJetScale
    (compactFixedPow thetaJetScale q (n^2)))

private theorem fixedJetTerm_containsReal {X q : FixedIntInterval} {x z : ℝ}
    (hX : (X.asQInterval thetaJetScale).ContainsReal x)
    (hq : (q.asQInterval thetaJetScale).ContainsReal z) (j n : ℕ) :
    ((fixedJetTerm X q (fixedJetCoefficients j) n).asQInterval thetaJetScale).ContainsReal
      (((n:ℝ)^2*x) * (phiJetPolynomial j).eval ((n:ℝ)^2*x) * z^(n^2)) := by
  let Y : FixedIntInterval := ⟨(n:ℤ)^2*X.lo, (n:ℤ)^2*X.hi⟩
  have hY : (Y.asQInterval thetaJetScale).ContainsReal ((n:ℝ)^2*x) := by
    simpa only [Y, FixedIntInterval.asQInterval, QInterval.ContainsReal, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
      Rat.cast_intCast, mul_div_assoc] using
      And.intro (mul_le_mul_of_nonneg_left hX.1 (sq_nonneg (n:ℝ)))
        (mul_le_mul_of_nonneg_left hX.2 (sq_nonneg (n:ℝ)))
  have hp := compactFixedHorner_containsReal thetaJetScale thetaJetScale_pos hY
    (fixedJetCoefficients j)
  rw [fixedJetCoefficients_eval] at hp
  have hpq := compactFixedPow_containsReal thetaJetScale thetaJetScale_pos hq (n^2)
  exact FixedIntInterval.mul_containsReal _ thetaJetScale_pos _ _ _ _
    (FixedIntInterval.mul_containsReal _ thetaJetScale_pos _ _ _ _ hY hp) hpq

private def fixedGridPrefix (inputs : PsiPreciseGridInputs) (j : ℕ) : QInterval :=
  let E := compactFixedRound thetaJetScale inputs.exponential
  let X := compactFixedRound thetaJetScale inputs.coordinate
  let q := compactFixedRound thetaJetScale inputs.gaussian
  let coeffs := fixedJetCoefficients j
  (E.mul thetaJetScale (compactFixedSum (Finset.range 8) (fixedJetTerm X q coeffs))).asQInterval
    thetaJetScale

private theorem fixedGridPrefix_containsReal {t : ℝ} {inputs : PsiPreciseGridInputs}
    (hE : inputs.exponential.ContainsReal (Real.exp t))
    (hX : inputs.coordinate.ContainsReal (Real.pi * Real.exp (4*t)))
    (hq : inputs.gaussian.ContainsReal (Real.exp (-(Real.pi * Real.exp (4*t))))) (j : ℕ) :
    (fixedGridPrefix inputs j).ContainsReal
      (∑ n ∈ Finset.range 8, auxiliaryWeightedSummand (phiJetPolynomial j) n t) := by
  simp_rw [auxiliaryWeightedSummand_eq_exp_powers]
  rw [← Finset.mul_sum]
  apply FixedIntInterval.mul_containsReal _ thetaJetScale_pos
  · exact compactFixedRound_containsReal thetaJetScale_pos hE
  · apply compactFixedSum_containsReal
    intro n _
    simpa only [auxiliaryCoordinate, mul_assoc] using
      fixedJetTerm_containsReal (compactFixedRound_containsReal thetaJetScale_pos hX)
        (compactFixedRound_containsReal thetaJetScale_pos hq) j n

/-- Evaluate the theta jets on a 768-bit integer grid before enclosing the result
on the grid shared by the compact Taylor certificates. -/
def psiFixedGridPhiJetBoxOfInputs (inputs : PsiPreciseGridInputs) (j : ℕ) : QInterval :=
  compactRoundInterval (2^90) (phiCompactJetBoxOfPrefix (fixedGridPrefix inputs j) j 8)

theorem psiFixedGridPhiJetBoxOfInputs_containsReal {t : ℚ} {inputs : PsiPreciseGridInputs}
    (h₀ : 0 ≤ t) (h₂ : t ≤ 2) (hcheck : psiPreciseGridChecks t)
    (hinputs : psiPreciseGridInputs t = inputs) (j : ℕ) :
    (psiFixedGridPhiJetBoxOfInputs inputs j).ContainsReal (iteratedDeriv j Phi (t:ℝ)) := by
  obtain ⟨hE, hX, hq⟩ := psiPreciseGridInputs_containsReal hcheck
  rw [hinputs] at hE hX hq
  unfold psiFixedGridPhiJetBoxOfInputs
  exact compactRoundInterval_containsReal (by positivity)
    (phiCompactJetBoxOfPrefix_containsReal (by exact_mod_cast h₀) (by exact_mod_cast h₂)
      j 8 (by decide) (fixedGridPrefix_containsReal hE hX hq j))

#print axioms psiFixedGridPhiJetBoxOfInputs_containsReal

end Nuttall
