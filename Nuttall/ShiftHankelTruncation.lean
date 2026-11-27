import Nuttall.ShiftHankelBasis

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- Equality of coefficients in the low rectangular block of the two variables. -/
def ShiftCoeffEq (k : ℕ) (P Q : (ℝ[X])[X]) : Prop :=
  ∀ i j : Fin k, (P.coeff i.val).coeff j.val = (Q.coeff i.val).coeff j.val

theorem ShiftCoeffEq.symm {k : ℕ} {P Q : (ℝ[X])[X]} (h : ShiftCoeffEq k P Q) :
    ShiftCoeffEq k Q P :=
  fun i j => (h i j).symm

theorem ShiftCoeffEq.trans {k : ℕ} {P Q R : (ℝ[X])[X]}
    (h : ShiftCoeffEq k P Q) (g : ShiftCoeffEq k Q R) : ShiftCoeffEq k P R :=
  fun i j => (h i j).trans (g i j)

theorem ShiftCoeffEq.sub {k : ℕ} {P Q R S : (ℝ[X])[X]}
    (h : ShiftCoeffEq k P Q) (g : ShiftCoeffEq k R S) : ShiftCoeffEq k (P-R) (Q-S) := by
  intro i j
  simp only [coeff_sub, h i j, g i j]

theorem ShiftCoeffEq.mul {k : ℕ} {P Q : (ℝ[X])[X]} (h : ShiftCoeffEq k P Q)
    (R : (ℝ[X])[X]) : ShiftCoeffEq k (R*P) (R*Q) := by
  intro i j
  simp only [coeff_mul, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha' := Finset.mem_antidiagonal.mp ha
  have hb' := Finset.mem_antidiagonal.mp hb
  have hai : a.2 < k := by have := i.isLt; omega
  have hbj : b.2 < k := by have := j.isLt; omega
  rw [h ⟨a.2, hai⟩ ⟨b.2, hbj⟩]

theorem ShiftCoeffEq.normalized {k : ℕ} {P Q : (ℝ[X])[X]} (h : ShiftCoeffEq k P Q) (M : ℕ) :
    normalizedShiftCoefficients M k P = normalizedShiftCoefficients M k Q := by
  ext i j
  simp only [normalizedShiftCoefficients, Matrix.of_apply, h i j]

private theorem shiftHankelBasisTerm_succ_mul_prefix {M a : ℕ} (ha : a ≤ M) (k : ℕ) (u : ℝ) :
    shiftGeometricPrefix k * shiftHankelBasisTerm (M+1) a u =
      (1-X^k) * shiftHankelBasisTerm M a u := by
  unfold shiftHankelBasisTerm
  rw [show M+1-a = M-a+1 by omega, pow_succ]
  calc
    _ = (shiftGeometricPrefix k * (1-X)) * (C (u^a / (a.factorial : ℝ)) * (X^a * (1-X)^(M-a))) := by ring
    _ = _ := by rw [shiftGeometricPrefix_mul_one_sub]

private theorem shiftHankelBasisTerm_succ_coeff_prefix {M a k i : ℕ}
    (ha : a ≤ M) (hi : i < k) (u : ℝ) :
    (shiftGeometricPrefix k * shiftHankelBasisTerm (M+1) a u).coeff i =
      (shiftHankelBasisTerm M a u).coeff i := by
  rw [shiftHankelBasisTerm_succ_mul_prefix ha, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
  simp [hi.not_ge]

/-- Two geometric prefixes convert the exponent-(M+1) basis back to the
exponent-(M) basis on the rectangular block. -/
theorem shiftHankelPolynomial_succ_prefix {M k : ℕ} (hk : k ≤ M+1) (u : ℝ)
    (H : Matrix (Fin k) (Fin k) ℝ) :
    ShiftCoeffEq k
      ((shiftGeometricPrefix k * C (shiftGeometricPrefix k)) * shiftHankelPolynomial (M+1) k u H)
      (shiftHankelPolynomial M k u H) := by
  intro i j
  have hp : separatedProduct (shiftGeometricPrefix k) (shiftGeometricPrefix k) =
      shiftGeometricPrefix k * C (shiftGeometricPrefix k) := by
    unfold separatedProduct shiftGeometricPrefix
    rw [Polynomial.map_sum]
    simp only [Polynomial.map_pow, Polynomial.map_X]
  simp only [shiftHankelPolynomial, Finset.mul_sum]
  simp only [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hterm :
      (shiftGeometricPrefix k * C (shiftGeometricPrefix k)) *
        (C (C (H a b)) * separatedProduct (shiftHankelBasisTerm (M+1) a.val u)
          (shiftHankelBasisTerm (M+1) b.val u)) =
      C (C (H a b)) * separatedProduct
        (shiftGeometricPrefix k * shiftHankelBasisTerm (M+1) a.val u)
        (shiftGeometricPrefix k * shiftHankelBasisTerm (M+1) b.val u) := by
    rw [← hp, separatedProduct_mul]
    ac_rfl
  rw [hterm]
  simp only [coeff_C_mul, coeff_separatedProduct]
  rw [shiftHankelBasisTerm_succ_coeff_prefix (show a.val ≤ M by have := a.isLt; omega) i.isLt,
    shiftHankelBasisTerm_succ_coeff_prefix (show b.val ≤ M by have := b.isLt; omega) j.isLt]

/-- The geometric prefix applied to one extra power gives exactly the
correction multiplier through the retained coefficient block. -/
theorem geometricPrefix_shiftForm {k : ℕ} (d : ℝ) (P : (ℝ[X])[X]) :
    ShiftCoeffEq k
      ((shiftGeometricPrefix k * C (shiftGeometricPrefix k)) *
        (bilinearPolynomial (1-d) d d (-(1+d)) * P))
      (shiftCorrectionMultiplier k d * P) := by
  let G : (ℝ[X])[X] := shiftGeometricPrefix k
  let H : (ℝ[X])[X] := C (shiftGeometricPrefix k)
  let D : (ℝ[X])[X] := C (C (1+d))
  let B := bilinearPolynomial (1-d) d d (-(1+d))
  let w : (ℝ[X])[X] := X
  let z : (ℝ[X])[X] := C X
  have hw : G*(1-w) = 1-w^k := shiftGeometricPrefix_mul_one_sub k
  have hz : H*(1-z) = 1-z^k := by
    simpa only [H, z, map_sub, map_mul, map_one, map_pow] using
      congrArg (C : ℝ[X] →+* (ℝ[X])[X]) (shiftGeometricPrefix_mul_one_sub (R := ℝ) k)
  have hB : B = (1-w)+(1-z)-D*(1-w)*(1-z) := by
    dsimp [B, D, w, z]
    rw [bilinearPolynomial_shift, map_add, map_add, map_one, map_one]
    ring
  have h : (G*H)*(B*P) =
      (G+H-D)*P +
        w^k * ((-H + D - D*z^k)*P) + z^k * ((-G+D)*P) := by
    calc
      _ = ((G*(1-w))*H+(H*(1-z))*G-D*(G*(1-w))*(H*(1-z)))*P := by rw [hB]; ring
      _ = _ := by rw [hw, hz]; ring
  intro i j
  change ((((G*H)*(B*P)).coeff i.val).coeff j.val) = (((G+H-D)*P).coeff i.val).coeff j.val
  rw [h]
  simp only [coeff_add]
  rw [show w^k * ((-H+D-D*z^k)*P) =
    X^k * ((-H+D-D*z^k)*P) from rfl, coeff_X_pow_mul', ite_eq_right i.isLt.not_ge, coeff_zero, add_zero]
  simp only [z, ← map_pow, coeff_C_mul, coeff_X_pow_mul', ite_eq_right j.isLt.not_ge, add_zero]

#print axioms shiftHankelPolynomial_succ_prefix
#print axioms geometricPrefix_shiftForm

end Nuttall
