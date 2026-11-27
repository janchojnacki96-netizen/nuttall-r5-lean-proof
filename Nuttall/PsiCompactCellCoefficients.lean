import Nuttall.PsiPreciseGridJets
import Nuttall.PsiCompactCoefficientScaling

namespace Nuttall

open W5

/-- The zeroth jet uses quadrature. The remaining jets use Ψ₁′ = −Φ. -/
def psiOneCompactJetBox (center : ℚ) (corner : QInterval) : ℕ → QInterval
  | 0 => corner
  | j+1 => (psiPreciseGridPhiJetBox center j).neg

theorem psiOneCompactJetBox_containsReal {center : ℚ} {corner : QInterval}
    (hc₀ : 0 ≤ center) (hc₂ : center ≤ 2) (hgrid : psiPreciseGridChecks center)
    (hcorner : corner.ContainsReal (psi 1 (center:ℝ))) (j : ℕ) :
    (psiOneCompactJetBox center corner j).ContainsReal
      (iteratedDeriv j (psi 1) (center:ℝ)) := by
  cases j with
  | zero => simpa only [psiOneCompactJetBox, iteratedDeriv_zero] using hcorner
  | succ j =>
    rw [show (1:ℕ) = 0+1 by rfl, iteratedDeriv_succ_psi_succ]
    exact QInterval.neg_containsReal (psiPreciseGridPhiJetBox_containsReal hc₀ hc₂ hgrid j)

/-- Compute the scaled Taylor coefficient of the selected Hankel index. -/
def psiOneCompactCoefficientBox (center radius : ℚ) (corner : QInterval) (l k : ℕ) :
    QInterval :=
  psiOneCompactCoefficientBoxOfJet radius (psiOneCompactJetBox center corner (l+k)) l k

theorem psiOneCompactCoefficientBox_containsReal {center radius : ℚ} {corner : QInterval}
    (hc₀ : 0 ≤ center) (hc₂ : center ≤ 2) (hgrid : psiPreciseGridChecks center)
    (hcorner : corner.ContainsReal (psi 1 (center:ℝ))) (l k : ℕ) :
    (psiOneCompactCoefficientBox center radius corner l k).ContainsReal
      ((1/16:ℝ)^l * (radius:ℝ)^k / (k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) (center:ℝ)) :=
  psiOneCompactCoefficientBoxOfJet_containsReal
    (psiOneCompactJetBox_containsReal hc₀ hc₂ hgrid hcorner _) l k

#print axioms psiOneCompactCoefficientBox_containsReal

end Nuttall
