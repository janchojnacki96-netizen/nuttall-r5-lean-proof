import W5.ThetaSignedFixedPointMultiplication
import Nuttall.CompactIntervalCongruence
import Nuttall.CompactIntervalRounding
import Nuttall.CompactPolynomialMargin

namespace Nuttall

open W5
open scoped BigOperators

/-- Retain integer endpoints after outward rounding on the common grid. -/
def compactFixedRound (D : ℤ) (I : QInterval) : FixedIntInterval :=
  ⟨⌊I.lo * (D:ℚ)⌋, ⌈I.hi * (D:ℚ)⌉⟩

theorem compactFixedRound_containsReal {D : ℤ} (hD : 0 < D)
    {I : QInterval} {x : ℝ} (h : I.ContainsReal x) :
    ((compactFixedRound D I).asQInterval D).ContainsReal x := by
  have hDq : (0:ℚ) < (D:ℚ) := by exact_mod_cast hD
  exact compactRoundInterval_containsReal hDq h

def compactFixedSum {α : Type*} (s : Finset α) (f : α → FixedIntInterval) :
    FixedIntInterval :=
  ⟨∑ i ∈ s, (f i).lo, ∑ i ∈ s, (f i).hi⟩

theorem compactFixedSum_containsReal {α : Type*} (D : ℤ) (s : Finset α)
    {f : α → FixedIntInterval} {g : α → ℝ}
    (h : ∀ i ∈ s, ((f i).asQInterval D).ContainsReal (g i)) :
    ((compactFixedSum s f).asQInterval D).ContainsReal (∑ i ∈ s, g i) := by
  have hs := QInterval.sumBox_containsReal s (fun i => (f i).asQInterval D) g h
  simpa only [QInterval.ContainsReal, compactFixedSum, FixedIntInterval.asQInterval,
    QInterval.sumBox, Int.cast_sum, Finset.sum_div] using hs

private def fixedMatrixMul {ι κ ν : Type*} [Fintype κ] (D : ℤ)
    (A : Matrix ι κ FixedIntInterval) (B : Matrix κ ν FixedIntInterval) :
    Matrix ι ν FixedIntInterval :=
  Matrix.of fun i j => compactFixedSum Finset.univ (fun k => (A i k).mul D (B k j))

private theorem fixedMatrixMul_containsReal {ι κ ν : Type*} [Fintype κ]
    (D : ℤ) (hD : 0 < D)
    {A : Matrix ι κ FixedIntInterval} {B : Matrix κ ν FixedIntInterval}
    {X : Matrix ι κ ℝ} {Y : Matrix κ ν ℝ}
    (hA : ∀ i j, ((A i j).asQInterval D).ContainsReal (X i j))
    (hB : ∀ i j, ((B i j).asQInterval D).ContainsReal (Y i j)) (i : ι) (j : ν) :
    ((fixedMatrixMul D A B i j).asQInterval D).ContainsReal ((X*Y) i j) := by
  rw [Matrix.mul_apply]
  apply compactFixedSum_containsReal
  intro k _
  exact FixedIntInterval.mul_containsReal D hD (A i k) (B k j) (X i k) (Y k j)
    (hA i k) (hB k j)

/-- Retain fixed-point endpoints through both products of the congruence. -/
def compactFixedCongruence {ι : Type*} [Fintype ι] (D : ℤ)
    (U : Matrix ι ι ℤ) (A : Matrix ι ι FixedIntInterval) : Matrix ι ι FixedIntInterval :=
  let P := U.map (fun x => (⟨x,x⟩ : FixedIntInterval))
  fixedMatrixMul D (fixedMatrixMul D P A) P.transpose

theorem compactFixedCongruence_containsReal {ι : Type*} [Fintype ι] (D : ℤ) (hD : 0 < D)
    (U : Matrix ι ι ℤ) {A : Matrix ι ι FixedIntInterval} {X : Matrix ι ι ℝ}
    (hA : ∀ i j, ((A i j).asQInterval D).ContainsReal (X i j)) (i j : ι) :
    ((compactFixedCongruence D U A i j).asQInterval D).ContainsReal
      (((U.map fun x => (x:ℝ)/D) * X * (U.map fun x => (x:ℝ)/D).transpose) i j) := by
  have hU (a b : ι) :
      (((⟨U a b,U a b⟩ : FixedIntInterval).asQInterval D)).ContainsReal ((U a b:ℝ)/D) := by
    simp [FixedIntInterval.asQInterval, QInterval.ContainsReal]
  exact fixedMatrixMul_containsReal D hD (fixedMatrixMul_containsReal D hD hU hA)
    (fun a b => hU b a) i j

private def compactFixedSign {n : ℕ} (D : ℤ) (k : ℕ) (i j : Fin n) : ℤ :=
  if k = 0 ∧ i = j then (-1:ℤ)^i.val*D else 0

def compactFixedCenteredCoefficient {n : ℕ} (D : ℤ) (U : Matrix (Fin n) (Fin n) ℤ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval) (k : ℕ) :
    Matrix (Fin n) (Fin n) FixedIntInterval :=
  Matrix.of fun i j => (compactFixedCongruence D U (boxes k) i j).sub
    ⟨compactFixedSign D k i j, compactFixedSign D k i j⟩

theorem compactFixedCenteredCoefficient_containsReal {n : ℕ} (D : ℤ) (hD : 0 < D)
    (U : Matrix (Fin n) (Fin n) ℤ)
    {boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval}
    {poly : ℕ → Matrix (Fin n) (Fin n) ℝ}
    (k : ℕ) (hbox : ∀ i j, ((boxes k i j).asQInterval D).ContainsReal (poly k i j))
    (i j : Fin n) :
    ((compactFixedCenteredCoefficient D U boxes k i j).asQInterval D).ContainsReal
      (((U.map fun x => (x:ℝ)/D) * poly k * (U.map fun x => (x:ℝ)/D).transpose -
        (if k = 0 then Matrix.diagonal (fun a : Fin n => (-1:ℝ)^a.val) else 0)) i j) := by
  let e := compactFixedSign D k i j
  have hd : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : (e:ℝ)/D =
      (if k = 0 then Matrix.diagonal (fun a : Fin n => (-1:ℝ)^a.val) else
        (0:Matrix (Fin n) (Fin n) ℝ)) i j := by
    by_cases h₀ : k = 0 <;> by_cases hij : i = j <;>
      simp [e, compactFixedSign, h₀, hij, Matrix.diagonal_apply, hd]
  have hE : ((⟨e,e⟩ : FixedIntInterval).asQInterval D).ContainsReal ((e:ℝ)/D) := by
    simp [FixedIntInterval.asQInterval, QInterval.ContainsReal]
  change ((compactFixedCongruence D U (boxes k) i j).sub ⟨e,e⟩ |>.asQInterval D).ContainsReal _
  rw [FixedIntInterval.asQInterval_sub, Matrix.sub_apply, ← he]
  exact QInterval.sub_containsReal (compactFixedCongruence_containsReal D hD U hbox i j) hE

/-- Compute a polynomial row bound with one common denominator.
All sums and absolute values here act on integers. -/
def compactFixedRowNumerator {n : ℕ} (d : ℕ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval) (i : Fin n) : ℤ :=
  ∑ k ∈ Finset.range d, ∑ j : Fin n, max |(boxes k i j).lo| |(boxes k i j).hi|

theorem compactFixedRowNumerator_eq {n : ℕ} (D : ℤ) (hD : 0 < D) (d : ℕ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval) (i : Fin n) :
    compactPolynomialRowBound d (fun k => (boxes k).map (FixedIntInterval.asQInterval D)) i =
      (compactFixedRowNumerator d boxes i : ℚ)/(D:ℚ) := by
  have hDq : (0:ℚ) < (D:ℚ) := by exact_mod_cast hD
  change (∑ k ∈ Finset.range d, ∑ j : Fin n,
    max |((boxes k i j).lo:ℚ)/(D:ℚ)| |((boxes k i j).hi:ℚ)/(D:ℚ)|) = _
  simp only [compactFixedRowNumerator, Int.cast_sum]
  simp_rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  simp only [abs_div, abs_of_pos hDq, max_div_div_right hDq.le]
  congr 1
  norm_cast

theorem compactFixedRow_lt_one {n : ℕ} (D : ℤ) (hD : 0 < D) (d : ℕ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) FixedIntInterval) (i : Fin n) (δ : ℚ) (cap : ℤ)
    (hcap : compactFixedRowNumerator d boxes i < cap)
    (hmargin : (cap:ℚ)/(D:ℚ) + (n:ℚ)*δ ≤ 1) :
    compactPolynomialRowBound d (fun k => (boxes k).map (FixedIntInterval.asQInterval D)) i
      + (n:ℚ)*δ < 1 := by
  have hDq : (0:ℚ) < (D:ℚ) := by exact_mod_cast hD
  have hcap' : (compactFixedRowNumerator d boxes i:ℚ) < (cap:ℚ) := by exact_mod_cast hcap
  rw [compactFixedRowNumerator_eq D hD]
  exact (add_lt_add_of_lt_of_le (div_lt_div_of_pos_right hcap' hDq) le_rfl).trans_le hmargin

#print axioms compactFixedCongruence_containsReal
#print axioms compactFixedRowNumerator_eq
#print axioms compactFixedRow_lt_one

end Nuttall
