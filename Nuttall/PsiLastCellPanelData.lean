import Nuttall.PsiLastCellGridInputs
import Nuttall.PsiFixedGridJets

namespace Nuttall

open W5

def lastCellPanelWidth (i : Fin 7) : ℚ :=
  if i = 0 then 1/512 else 1/32

/-- Read a quadrature jet already rounded onto the common dyadic grid. -/
def lastCellPanelJetOfEndpoints (endpoints : Vector (ℤ × ℤ) 36) (j : ℕ) : QInterval :=
  let bounds := endpoints.toArray[j]!
  ⟨(bounds.1:ℚ)/2^90, (bounds.2:ℚ)/2^90⟩

def LastCellPanelCheck (i : Fin 7) (jets : ℕ → QInterval) : Prop :=
  let raw := psiOnePanelBox (QInterval.point 0) jets 36 (lastCellPanelWidth i)
  (psiLastCellPanelSnapshot i).lo ≤ raw.lo ∧ raw.hi ≤ (psiLastCellPanelSnapshot i).hi

instance (i : Fin 7) (jets : ℕ → QInterval) : Decidable (LastCellPanelCheck i jets) := by
  unfold LastCellPanelCheck
  infer_instance

end Nuttall
