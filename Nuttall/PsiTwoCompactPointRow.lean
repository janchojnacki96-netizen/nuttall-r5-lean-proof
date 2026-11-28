import Nuttall.CompactFixedPointCongruence
import Nuttall.PsiTwoCompactCellSigns

namespace Nuttall

open W5

private def phiJetsForSecondIntegral (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval) :
    ℕ → FixedIntInterval
  | 0 => two
  | 1 => ⟨-one.hi, -one.lo⟩
  | j+2 => phi j

/-- Evaluate the rank-eight row using the fixed-point congruence
specialized to the point entries of the triangular basis. -/
def psiTwoCompactPointRow (B : Matrix (Fin 8) (Fin 8) ℤ)
    (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval) (i : Fin 8) : ℤ :=
  let boxes (k : ℕ) : Matrix (Fin 8) (Fin 8) FixedIntInterval :=
    Matrix.of fun j l => compactDyadicCoefficient 8 (j.val+l.val) k
      (phiJetsForSecondIntegral one two phi (j.val+l.val+k))
  compactFixedRowNumerator 24
    (compactFixedPointCenteredCoefficient (2^90) (B.map (· * 2^80)) boxes) i

theorem psiTwoCompactPointRow_eq (B : Matrix (Fin 8) (Fin 8) ℤ)
    (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval) (i : Fin 8) :
    psiTwoCompactPointRow B one two phi i = psiTwoCompactRow B one two phi i := by
  let D : ℤ := 2^90
  let U := B.map (· * 2^80)
  let boxes (k : ℕ) : Matrix (Fin 8) (Fin 8) FixedIntInterval :=
    Matrix.of fun j l => compactDyadicCoefficient 8 (j.val+l.val) k
      (phiJetsForSecondIntegral one two phi (j.val+l.val+k))
  change compactFixedRowNumerator 24 (compactFixedPointCenteredCoefficient D U boxes) i =
    compactFixedRowNumerator 24 (compactFixedCenteredCoefficient D U boxes) i
  exact congrArg (fun c => compactFixedRowNumerator 24 c i)
    (funext (compactFixedPointCenteredCoefficient_eq D U boxes))

#print axioms psiTwoCompactPointRow_eq

end Nuttall
