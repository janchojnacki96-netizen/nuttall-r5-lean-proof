import Nuttall.CompactFixedCongruence

namespace Nuttall

open W5

/-- A point interval has only two distinct corner products. In particular,
a zero point does not require any evaluation of the other factor. -/
private def fixedPointMul (D a : ℤ) (I : FixedIntInterval) : FixedIntInterval :=
  if a = 0 then ⟨0, 0⟩ else
    ⟨min (a * I.lo) (a * I.hi) / D, -(-max (a * I.lo) (a * I.hi) / D)⟩

private theorem fixedPointMul_eq_left (D a : ℤ) (I : FixedIntInterval) :
    fixedPointMul D a I = (⟨a, a⟩ : FixedIntInterval).mul D I := by
  by_cases ha : a = 0 <;>
    simp [fixedPointMul, ha, FixedIntInterval.mul, FixedIntInterval.productMin,
      FixedIntInterval.productMax]

private theorem fixedPointMul_eq_right (D a : ℤ) (I : FixedIntInterval) :
    fixedPointMul D a I = I.mul D ⟨a, a⟩ := by
  by_cases ha : a = 0 <;>
    simp [fixedPointMul, ha, FixedIntInterval.mul, FixedIntInterval.productMin,
      FixedIntInterval.productMax, mul_comm a]

private def compactFixedPointCongruence {ι : Type*} [Fintype ι] (D : ℤ)
    (U : Matrix ι ι ℤ) (A : Matrix ι ι FixedIntInterval) : Matrix ι ι FixedIntInterval :=
  let P := Matrix.of fun i j =>
    compactFixedSum Finset.univ (fun k => fixedPointMul D (U i k) (A k j))
  Matrix.of fun i j =>
    compactFixedSum Finset.univ (fun k => fixedPointMul D (U j k) (P i k))

private theorem compactFixedPointCongruence_eq {ι : Type*} [Fintype ι] (D : ℤ)
    (U : Matrix ι ι ℤ) (A : Matrix ι ι FixedIntInterval) :
    compactFixedPointCongruence D U A = compactFixedCongruence D U A := by
  ext i j
  change compactFixedSum Finset.univ (fun k => fixedPointMul D (U j k)
      (compactFixedSum Finset.univ (fun l => fixedPointMul D (U i l) (A l k)))) = _
  simp only [fixedPointMul_eq_right D (U j _) _, fixedPointMul_eq_left]
  rfl

/-- Use the same enclosure with multiplication specialized to point factors. -/
def compactFixedPointCenteredCoefficient {n : ℕ} (D : ℤ) (U : Matrix (Fin n) (Fin n) ℤ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval) (k : ℕ) :
    Matrix (Fin n) (Fin n) FixedIntInterval :=
  Matrix.of fun i j =>
    let e := if k = 0 ∧ i = j then (-1:ℤ)^i.val*D else 0
    (compactFixedPointCongruence D U (boxes k) i j).sub ⟨e, e⟩

theorem compactFixedPointCenteredCoefficient_eq {n : ℕ} (D : ℤ) (U : Matrix (Fin n) (Fin n) ℤ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval) (k : ℕ) :
    compactFixedPointCenteredCoefficient D U boxes k =
      compactFixedCenteredCoefficient D U boxes k := by
  unfold compactFixedPointCenteredCoefficient
  rw [compactFixedPointCongruence_eq]
  rfl

#print axioms compactFixedPointCenteredCoefficient_eq

end Nuttall
