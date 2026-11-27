import Nuttall.PsiEightCornerBound
import Nuttall.PsiEightWitness
import Nuttall.SchurIntervalChain

namespace Nuttall

open W5

/-- The first integrated kernel's eight-by-eight Hankel matrix at the witness. -/
noncomputable def psiEightWitnessHankel : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of (fun i j => iteratedDeriv (i.val + j.val) (psi 1) (5/64))

/-- Two interval Schur certificates suffice to exclude level one at rank eight.
Only the non-corner jets require two-sided enclosures. -/
theorem two_le_kernelIntegrationOrder_of_rankEight_schur
    {B : Matrix (Fin 8) (Fin 8) QInterval} {Db Dc : QInterval}
    (hB : ∀ i j, (B i j).ContainsReal (replaceMatrixCorner psiEightWitnessHankel (29/1000) i j))
    (hb : SchurIntervalChain 8 B Db)
    (hc : SchurIntervalChain 7 (B.submatrix Fin.succ Fin.succ) Dc)
    (hDb : Db.hi < 0) (hDc : Dc.hi ≤ 0) :
    2 ≤ kernelIntegrationOrder 8 := by
  have hBox (i j : Fin 7) : ((B.submatrix Fin.succ Fin.succ) i j).ContainsReal
      ((psiEightWitnessHankel.submatrix Fin.succ Fin.succ) i j) := by
    simpa [replaceMatrixCorner, Matrix.submatrix_apply] using hB i.succ j.succ
  have hDbR : (Db.hi : ℝ) < 0 := by exact_mod_cast hDb
  have hDcR : (Dc.hi : ℝ) ≤ 0 := by exact_mod_cast hDc
  have hbR := hb.det_containsReal _ hB
  have hcR := hc.det_containsReal _ hBox
  exact two_le_kernelIntegrationOrder_of_psiOne_corner (by norm_num : (0:ℝ) ≤ 5/64)
    psi_one_at_rankEight_witness_ge (hcR.2.trans hDcR) (hbR.2.trans_lt hDbR)

#print axioms two_le_kernelIntegrationOrder_of_rankEight_schur

end Nuttall
