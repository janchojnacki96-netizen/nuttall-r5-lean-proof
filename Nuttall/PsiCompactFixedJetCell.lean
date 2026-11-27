import Nuttall.PsiCompactCoefficientScaling
import Nuttall.PsiCompactFixedCellSigns

namespace Nuttall

open W5

/-- Build all scaled Taylor coefficients from the zeroth Ψ₁ jet and the Φ jets. -/
def psiOneCompactBoxesOfJets (radius : ℚ) (corner : QInterval) (phiJets : ℕ → QInterval)
    (k : ℕ) : Matrix (Fin 7) (Fin 7) QInterval :=
  Matrix.of fun i j =>
    let l := i.val+j.val
    let jet := match l+k with
      | 0 => corner
      | m+1 => (phiJets m).neg
    psiOneCompactCoefficientBoxOfJet radius jet l k

theorem psiOne_compact_fixed_jet_cell_signed_wronskians {p : ℕ} (hp : p ≤ 7)
    (c h : ℚ) {v : ℝ} (ha : 0 ≤ (c:ℝ)-(h:ℝ)) (hb : (c:ℝ)+(h:ℝ) ≤ 2)
    (hh : 0 ≤ (h:ℝ)) (hh' : (h:ℝ) ≤ 1/256) (hv : |v| ≤ 1) (i : Fin 67)
    {corner : QInterval} {phiJets : ℕ → QInterval}
    (hcorner : corner.ContainsReal (psi 1 (c:ℝ)))
    (hjets : ∀ m < 36, (phiJets m).ContainsReal (iteratedDeriv m Phi (c:ℝ)))
    (hcheck : ∀ j, psiOneCompactFixedRow i (psiOneCompactBoxesOfJets h corner phiJets) j <
      psiOneCompactFixedThreshold) :
    0 < kernelMinorSign p * wronskian (psi 1) p ((c:ℝ)+(h:ℝ)*v) := by
  refine psiOne_compact_fixed_cell_signed_wronskians hp ha hb hh hh' hv i
    (psiOneCompactBoxesOfJets h corner phiJets) ?_ hcheck
  intro k hk a b
  let l := a.val+b.val
  have hjet : (match l+k with
      | 0 => corner
      | m+1 => (phiJets m).neg).ContainsReal (iteratedDeriv (l+k) (psi 1) (c:ℝ)) := by
    cases hn : l+k with
    | zero => simpa only [iteratedDeriv_zero] using hcorner
    | succ m =>
      rw [show (1:ℕ) = 0+1 by rfl, iteratedDeriv_succ_psi_succ]
      exact QInterval.neg_containsReal (hjets m (by dsimp [l] at hn; omega))
  exact psiOneCompactCoefficientBoxOfJet_containsReal (radius := h) hjet l k

#print axioms psiOne_compact_fixed_jet_cell_signed_wronskians

end Nuttall
