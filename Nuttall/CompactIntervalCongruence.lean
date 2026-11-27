import Nuttall.OriginWronskianInterval

namespace Nuttall

open W5
open scoped BigOperators

private def intervalMatrixMul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ QInterval) (B : Matrix κ ν QInterval) : Matrix ι ν QInterval :=
  Matrix.of fun i j => QInterval.sumBox Finset.univ (fun k => (A i k).mul (B k j))

private theorem intervalMatrixMul_containsReal {ι κ ν : Type*} [Fintype κ]
    {A : Matrix ι κ QInterval} {B : Matrix κ ν QInterval}
    {X : Matrix ι κ ℝ} {Y : Matrix κ ν ℝ}
    (hA : ∀ i j, (A i j).ContainsReal (X i j))
    (hB : ∀ i j, (B i j).ContainsReal (Y i j)) (i : ι) (j : ν) :
    (intervalMatrixMul A B i j).ContainsReal ((X*Y) i j) := by
  rw [Matrix.mul_apply]
  apply QInterval.sumBox_containsReal
  intro k _
  exact QInterval.mul_containsReal (hA i k) (hB k j)

/-- Exact interval congruence of a coefficient matrix by a rational basis. -/
def compactIntervalCongruence {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℚ) (A : Matrix ι ι QInterval) : Matrix ι ι QInterval :=
  let P := U.map QInterval.point
  intervalMatrixMul (intervalMatrixMul P A) P.transpose

/-- Every interval entry of the rational congruence encloses the matching
entry of the congruence of the underlying real coefficient matrix. -/
theorem compactIntervalCongruence_containsReal {ι : Type*} [Fintype ι]
    (U : Matrix ι ι ℚ) {A : Matrix ι ι QInterval} {X : Matrix ι ι ℝ}
    (hA : ∀ i j, (A i j).ContainsReal (X i j)) (i j : ι) :
    (compactIntervalCongruence U A i j).ContainsReal
      (((U.map (fun r : ℚ => (r:ℝ))) * X * (U.map (fun r : ℚ => (r:ℝ))).transpose) i j) := by
  have hU (a b : ι) :
      ((U.map QInterval.point) a b).ContainsReal ((U.map (fun r : ℚ => (r:ℝ))) a b) :=
    ⟨le_rfl, le_rfl⟩
  exact intervalMatrixMul_containsReal (intervalMatrixMul_containsReal hU hA)
    (fun a b => hU b a) i j

#print axioms compactIntervalCongruence_containsReal

end Nuttall
