import Nuttall.PhiJetCoefficients
import Mathlib.LinearAlgebra.Matrix.Block

namespace Nuttall

open scoped BigOperators

/-- Coefficients through degree three of the gauged logarithmic change of variables.
The row indexed by i acts on ordinary derivatives of orders 0 through i. -/
noncomputable def phiCompactRow (X : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 1, 0 => X - 5/4
  | 1, 1 => 1/4
  | 2, 0 => X^2/2 - 5*X/4 + 45/32
  | 2, 1 => X/4 - 7/16
  | 2, 2 => 1/32
  | 3, 0 => X^3/6 - 5*X^2/8 + 45*X/32 - 195/128
  | 3, 1 => X^2/8 - 7*X/16 + 227/384
  | 3, 2 => X/32 - 9/128
  | 3, 3 => 1/384
  | _, _ => 0

/-- The mixed coefficient of the linear and bilinear Gaussian factors. -/
noncomputable def phiCompactGaussian (X q : ℝ) (i j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (min i j + 1),
    ((-(q-1)*X)^(i-k) / ((i-k).factorial:ℝ)) *
    ((-(q-1)*X)^(j-k) / ((j-k).factorial:ℝ)) *
    ((-q*X)^k / (k.factorial:ℝ))

/-- The polynomial part of the normalized square-index term. -/
noncomputable def phiCompactPolynomial (X q : ℝ) (i j : ℕ) : ℝ :=
  q * ((2*q*X-3) * phiCompactGaussian X q i j +
    2*q*X * ((if i = 0 then 0 else phiCompactGaussian X q (i-1) j) +
      (if j = 0 then 0 else phiCompactGaussian X q i (j-1)) +
      (if i = 0 ∨ j = 0 then 0 else phiCompactGaussian X q (i-1) (j-1))))

/-- A square-index summand of the normalized Hankel matrix in the compact test. -/
noncomputable def phiCompactTerm (X : ℝ) (i j n : ℕ) : ℝ :=
  phiCompactPolynomial X ((n:ℝ)^2) i j * Real.exp (-((n:ℝ)^2-1)*X)

theorem phiCompactRow_zero {X : ℝ} {i j : ℕ} (hi : i < 4) (hij : i < j) :
    phiCompactRow X i j = 0 := by
  by_cases hj : j < 4
  · interval_cases i <;> interval_cases j <;> first | omega | rfl
  · obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 4 ≤ j by omega)
    rw [show j = k+4 by omega]
    interval_cases i <;> rfl

private noncomputable def phiCompactJet (x : ℝ) : ℕ → ℝ
  | 0 => 2*x - 3
  | 1 => -8*x^2 + 30*x - 15
  | 2 => 32*x^3 - 224*x^2 + 330*x - 75
  | 3 => -128*x^4 + 1440*x^3 - 4232*x^2 + 3270*x - 375
  | 4 => 512*x^5 - 8448*x^4 + 41408*x^3 - 68096*x^2 + 30930*x - 1875
  | 5 => -2048*x^6 + 46592*x^5 - 343040*x^4 + 976320*x^3 - 1008968*x^2 + 285870*x - 9375
  | 6 => 8192*x^7 - 245760*x^6 + 2536960*x^5 - 11109120*x^4 + 20633312*x^3 - 14260064*x^2 + 2610330*x - 46875
  | _ => 0

private theorem phiCompactJet_eq_eval (x : ℝ) {j : ℕ} (h : j ≤ 6) :
    (phiJetPolynomial j).eval x = phiCompactJet x j := by
  rw [eval_phiJetPolynomial (by omega : j ≤ 8)]
  interval_cases j <;>
    norm_num [Finset.sum_range_succ, phiJetCoeff, auxiliaryJetCoeff, phiCompactJet] <;> ring

set_option maxHeartbeats 2000000 in
/-- Algebraic coefficient comparison for the change of variables, without an exchange
of mixed derivatives and the infinite theta sum. -/
theorem phiCompactPolynomial_eq_rows (X q : ℝ) (i j : ℕ) (hi : i < 4) (hj : j < 4) :
    phiCompactPolynomial X q i j =
      ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
        phiCompactRow X i a * phiCompactRow X j b *
          (q * (phiJetPolynomial (a+b)).eval (q*X)) := by
  interval_cases i <;> interval_cases j <;>
    norm_num [Finset.sum_range_succ, phiCompactRow, phiCompactPolynomial, phiCompactGaussian,
      Nat.factorial] <;>
    simp only [phiCompactJet_eq_eval _ (by decide : 0 ≤ 6),
      phiCompactJet_eq_eval _ (by decide : 1 ≤ 6), phiCompactJet_eq_eval _ (by decide : 2 ≤ 6),
      phiCompactJet_eq_eval _ (by decide : 3 ≤ 6), phiCompactJet_eq_eval _ (by decide : 4 ≤ 6),
      phiCompactJet_eq_eval _ (by decide : 5 ≤ 6), phiCompactJet_eq_eval _ (by decide : 6 ≤ 6),
      phiCompactJet] <;> ring <;> simp

noncomputable def phiCompactRows (p : ℕ) (X : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of (fun i j => phiCompactRow X i.val j.val)

theorem phiCompactRows_det_pos {p : ℕ} (hp : p ≤ 4) (X : ℝ) :
    0 < (phiCompactRows p X).det := by
  rw [Matrix.det_of_isLowerTriangular]
  · apply Finset.prod_pos
    intro i _
    have hi : i.val < 4 := i.isLt.trans_le hp
    change 0 < phiCompactRow X i.val i.val
    have hj : i.val < 4 := hi
    let k := i.val
    change k < 4 at hj
    change 0 < phiCompactRow X k k
    interval_cases k <;> norm_num [phiCompactRow]
  · intro i j hij
    exact phiCompactRow_zero (i.isLt.trans_le hp) hij

#print axioms phiCompactPolynomial_eq_rows
#print axioms phiCompactRows_det_pos

end Nuttall
