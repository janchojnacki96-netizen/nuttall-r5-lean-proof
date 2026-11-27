import Nuttall.PhiCompactTransfer
import Nuttall.PhiCompactTailBound
import Nuttall.PhiCompactExponential

namespace Nuttall

open W5
open scoped BigOperators

private theorem intervalPow_containsReal {I : QInterval} {x : ℝ}
    (hx : I.ContainsReal x) (k : ℕ) : (I.pow k).ContainsReal (x^k) := by
  induction k with
  | zero => simp [QInterval.pow, QInterval.point, QInterval.ContainsReal]
  | succ k ih =>
    simpa only [QInterval.pow, pow_succ] using QInterval.mul_containsReal ih hx

private theorem intervalPoint_containsReal (q : ℚ) : (QInterval.point q).ContainsReal (q:ℝ) :=
  ⟨le_rfl, le_rfl⟩

private def phiCompactGaussianBox (I : QInterval) (q : ℕ) (i j : ℕ) : QInterval :=
  let L := QInterval.mul (QInterval.point (-(q:ℚ)+1)) I
  let M := QInterval.mul (QInterval.point (-(q:ℚ))) I
  QInterval.sumBox (Finset.range (min i j+1)) (fun k =>
    QInterval.mul
      (QInterval.mul ((L.pow (i-k)).mul (QInterval.point (1/((i-k).factorial:ℚ))))
        ((L.pow (j-k)).mul (QInterval.point (1/((j-k).factorial:ℚ)))))
      ((M.pow k).mul (QInterval.point (1/(k.factorial:ℚ)))))

private theorem phiCompactGaussianBox_containsReal {I : QInterval} {X : ℝ}
    (hX : I.ContainsReal X) (q i j : ℕ) :
    (phiCompactGaussianBox I q i j).ContainsReal (phiCompactGaussian X q i j) := by
  unfold phiCompactGaussianBox phiCompactGaussian
  apply QInterval.sumBox_containsReal
  intro k _
  have hL := QInterval.mul_containsReal (intervalPoint_containsReal (-(q:ℚ)+1)) hX
  have hM := QInterval.mul_containsReal (intervalPoint_containsReal (-(q:ℚ))) hX
  have hL' : (QInterval.mul (QInterval.point (-(q:ℚ)+1)) I).ContainsReal (-((q:ℝ)-1)*X) := by
    convert hL using 1
    push_cast
    ring
  have hM' : (QInterval.mul (QInterval.point (-(q:ℚ))) I).ContainsReal (-(q:ℝ)*X) := by
    simpa only [Rat.cast_neg, Rat.cast_natCast] using hM
  have hfactor (I' : QInterval) (x : ℝ) (hx : I'.ContainsReal x) (m : ℕ) :
      ((I'.pow m).mul (QInterval.point (1/(m.factorial:ℚ)))).ContainsReal
        (x^m / (m.factorial:ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, mul_one_div] using
      QInterval.mul_containsReal (intervalPow_containsReal hx m)
        (intervalPoint_containsReal (1/(m.factorial:ℚ)))
  exact QInterval.mul_containsReal
    (QInterval.mul_containsReal (hfactor _ _ hL' (i-k)) (hfactor _ _ hL' (j-k)))
    (hfactor _ _ hM' k)

private def phiCompactPolynomialBox (I : QInterval) (q i j : ℕ) : QInterval :=
  let T := QInterval.mul (QInterval.point (2*(q:ℚ))) I
  let G := phiCompactGaussianBox I q
  let A := if i = 0 then QInterval.point 0 else G (i-1) j
  let B := if j = 0 then QInterval.point 0 else G i (j-1)
  let C := if i = 0 ∨ j = 0 then QInterval.point 0 else G (i-1) (j-1)
  QInterval.mul (QInterval.point (q:ℚ))
    ((T.sub (QInterval.point 3)).mul (G i j) |>.add (T.mul (A.add B |>.add C)))

private theorem phiCompactPolynomialBox_containsReal {I : QInterval} {X : ℝ}
    (hX : I.ContainsReal X) (q i j : ℕ) :
    (phiCompactPolynomialBox I q i j).ContainsReal (phiCompactPolynomial X q i j) := by
  have hT : (QInterval.mul (QInterval.point (2*(q:ℚ))) I).ContainsReal (2*(q:ℝ)*X) := by
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
      QInterval.mul_containsReal (intervalPoint_containsReal (2*(q:ℚ))) hX
  unfold phiCompactPolynomialBox phiCompactPolynomial
  have hq : (QInterval.point (q:ℚ)).ContainsReal (q:ℝ) := by
    simp [QInterval.ContainsReal, QInterval.point]
  have hthree : (QInterval.point 3).ContainsReal (3:ℝ) := by
    simp [QInterval.ContainsReal, QInterval.point]
  apply QInterval.mul_containsReal hq
  apply QInterval.add_containsReal
  · exact QInterval.mul_containsReal (QInterval.sub_containsReal hT hthree)
      (phiCompactGaussianBox_containsReal hX q i j)
  · apply QInterval.mul_containsReal hT
    apply QInterval.add_containsReal
    · apply QInterval.add_containsReal
      · by_cases h : i = 0
        · simp [h, QInterval.ContainsReal, QInterval.point]
        · simpa only [if_neg h] using phiCompactGaussianBox_containsReal hX q (i-1) j
      · by_cases h : j = 0
        · simp [h, QInterval.ContainsReal, QInterval.point]
        · simpa only [if_neg h] using phiCompactGaussianBox_containsReal hX q i (j-1)
    · by_cases h : i = 0 ∨ j = 0
      · simp [h, QInterval.ContainsReal, QInterval.point]
      · simpa only [if_neg h] using phiCompactGaussianBox_containsReal hX q (i-1) (j-1)

private def phiCompactTermBox (I E : QInterval) (i j n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else (phiCompactPolynomialBox I (n^2) i j).mul (E.pow (n^2-1))

private theorem phiCompactTermBox_containsReal {I E : QInterval} {X : ℝ}
    (hX : I.ContainsReal X) (hE : E.ContainsReal (Real.exp (-X))) (i j n : ℕ) :
    (phiCompactTermBox I E i j n).ContainsReal (phiCompactTerm X i j n) := by
  by_cases hn : n = 0
  · subst n
    simp [phiCompactTermBox, phiCompactTerm, phiCompactPolynomial, QInterval.ContainsReal, QInterval.point]
  · have hn' : 1 ≤ n^2 := Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.mpr hn)
    have hpower : Real.exp (-X)^(n^2-1) = Real.exp (-((n:ℝ)^2-1)*X) := by
      rw [← Real.exp_nat_mul, Nat.cast_sub hn', Nat.cast_one, Nat.cast_pow]
      ring_nf
    unfold phiCompactTermBox phiCompactTerm
    rw [if_neg hn, ← hpower, ← Nat.cast_pow]
    exact QInterval.mul_containsReal (phiCompactPolynomialBox_containsReal hX (n^2) i j)
      (intervalPow_containsReal hE (n^2-1))

/-- A rank-p box over one closed compact cell including the analytic square-index tail. -/
def phiCompactBlockBox (a b : ℚ) (p : ℕ) : Matrix (Fin p) (Fin p) QInterval :=
  let E := phiCompactExpBox a b
  Matrix.of (fun i j =>
    (QInterval.sumBox (Finset.range 4) (phiCompactTermBox ⟨a,b⟩ E i.val j.val)).add
      ⟨-(1/1000), 1/1000⟩)

theorem phiCompactBlockBox_containsReal {a b : ℚ} {p : ℕ} (hp : p ≤ 4) (t : ℝ)
    (ha : 3 ≤ a) (hb : b ≤ 16) (hlo : (a:ℝ) ≤ phiThetaCoordinate t)
    (hhi : phiThetaCoordinate t ≤ (b:ℝ)) (i j : Fin p) :
    (phiCompactBlockBox a b p i j).ContainsReal (phiCompactMatrix p (phiThetaCoordinate t) i j) := by
  have hi := i.isLt.trans_le hp
  have hj := j.isLt.trans_le hp
  have hX : (⟨a,b⟩:QInterval).ContainsReal (phiThetaCoordinate t) := ⟨hlo,hhi⟩
  have h3 : (3:ℝ) ≤ phiThetaCoordinate t := (by exact_mod_cast ha : (3:ℝ) ≤ (a:ℝ)).trans hlo
  have hE := phiCompactExpBox_containsReal (by linarith : 0 ≤ a) hb hlo hhi
  simp only [phiCompactBlockBox, phiCompactMatrix, Matrix.of_apply]
  rw [← (phiCompactTerm_summable t hi hj).sum_add_tsum_nat_add 4]
  apply QInterval.add_containsReal
  · exact QInterval.sumBox_containsReal _ _ _ (fun n _ => phiCompactTermBox_containsReal hX hE _ _ n)
  · have h := abs_le.mp (by simpa only [add_comm] using phiCompactTail_abs_le h3 hi hj)
    simpa only [QInterval.ContainsReal, Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] using h

/-- A rational sign check whose implication is proved independently of the cells. -/
def phiCompactCellCheck (a b : ℚ) (p : ℕ) : Prop :=
  let D := QInterval.determinant p (phiCompactBlockBox a b p)
  0 < (QInterval.mul (QInterval.point ((-1:ℚ)^(p*(p-1)/2))) D).lo

theorem phiCompactCellCheck_sound {a b : ℚ} {p : ℕ} (hp : p ≤ 4) (t : ℝ)
    (ha : 3 ≤ a) (hb : b ≤ 16) (hlo : (a:ℝ) ≤ phiThetaCoordinate t)
    (hhi : phiThetaCoordinate t ≤ (b:ℝ)) (h : phiCompactCellCheck a b p) :
    0 < kernelMinorSign p * wronskian Phi p t := by
  apply (phiCompactMatrix_signed_det_pos_iff hp t).mp
  have hd := QInterval.determinant_containsReal p _ _
    (phiCompactBlockBox_containsReal hp t ha hb hlo hhi)
  have hs := QInterval.mul_containsReal (intervalPoint_containsReal ((-1:ℚ)^(p*(p-1)/2))) hd
  have h₀ : (0:ℝ) < ((QInterval.mul (QInterval.point ((-1:ℚ)^(p*(p-1)/2)))
      (QInterval.determinant p (phiCompactBlockBox a b p))).lo:ℝ) := by
    exact_mod_cast h
  exact h₀.trans_le (by simpa only [kernelMinorSign, Rat.cast_pow, Rat.cast_neg, Rat.cast_one] using hs.1)

#print axioms phiCompactCellCheck_sound

end Nuttall
