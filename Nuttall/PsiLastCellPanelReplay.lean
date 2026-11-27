import Nuttall.PsiLastCellPanel0
import Nuttall.PsiLastCellPanel1
import Nuttall.PsiLastCellPanel2
import Nuttall.PsiLastCellPanel3
import Nuttall.PsiLastCellPanel4
import Nuttall.PsiLastCellPanel5
import Nuttall.PsiLastCellPanel6

namespace Nuttall

open W5

/-- Reuse exact, individually checked jet boxes in the quadrature replay. -/
def lastCellPanelJet (i : Fin 7) : ℕ → QInterval :=
  (#v[lastCellPanel0Jet, lastCellPanel1Jet, lastCellPanel2Jet, lastCellPanel3Jet,
    lastCellPanel4Jet, lastCellPanel5Jet, lastCellPanel6Jet] : Vector (ℕ → QInterval) 7).get i

theorem lastCellPanelJet_checked (i : Fin 7) (j : ℕ) (hj : j < 36) :
    lastCellPanelJet i j = psiFixedGridPhiJetBoxOfInputs (psiLastCellGridInputs i) j := by
  fin_cases i
  · exact lastCellPanel0Jet_checked j hj
  · exact lastCellPanel1Jet_checked j hj
  · exact lastCellPanel2Jet_checked j hj
  · exact lastCellPanel3Jet_checked j hj
  · exact lastCellPanel4Jet_checked j hj
  · exact lastCellPanel5Jet_checked j hj
  · exact lastCellPanel6Jet_checked j hj

theorem lastCellPanel_checked (i : Fin 7) : LastCellPanelCheck i (lastCellPanelJet i) := by
  fin_cases i
  · exact lastCellPanel0_checked
  · exact lastCellPanel1_checked
  · exact lastCellPanel2_checked
  · exact lastCellPanel3_checked
  · exact lastCellPanel4_checked
  · exact lastCellPanel5_checked
  · exact lastCellPanel6_checked

#print axioms lastCellPanelJet_checked

#print axioms lastCellPanel_checked

end Nuttall
