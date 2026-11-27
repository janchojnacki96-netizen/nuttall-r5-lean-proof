import Nuttall.ShiftedMomentDerivatives
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Polynomial.BigOperators

namespace Nuttall

open scoped BigOperators

/-- On the small interval used for the relative slice bound only the first
theta term is active. -/
theorem shiftedMoment_eq_tailMomentWeight_on_small_interval (j : ℕ) {u : ℝ}
    (hu : 0 < u) (hu' : u ≤ 1/4) :
    shiftedMoment j u = tailMomentWeight j u := by
  have hlog : (1/2:ℝ) < Real.log 2 := by
    have hs : Real.exp (1/2:ℝ) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    have he : Real.exp (1/2:ℝ) < 2 := by
      nlinarith only [hs, Real.exp_one_lt_three, Real.exp_pos (1/2:ℝ)]
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
    exact he
  have hactive : activeThetaIndices u = {1} := by
    ext n
    rw [mem_activeThetaIndices, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, hnu⟩
      by_contra hne
      have hn₂ : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      have hln := Real.log_le_log (by norm_num) hn₂
      unfold thetaKnot at hnu
      linarith only [hnu, hln, hlog, hu']
    · rintro rfl
      simpa [thetaKnot] using hu
  rw [shiftedMoment_eq_sum_active, hactive]
  simp [thetaKnot]

/-- A maximal normalized coefficient survives the subtraction of the
previous coefficient, since its own multiplier is at least two. -/
theorem abs_le_abs_adjacent_coefficient {a b c : ℝ} (ha : 2 ≤ a) (hb : |c| ≤ |b|) :
    |b| ≤ |a*b-c| := by
  have h := abs_sub_abs_le_abs_sub (a*b) c
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ a)] at h
  have hmul := mul_le_mul_of_nonneg_right ha (abs_nonneg b)
  linarith only [h, hmul, hb]

/-- The linear combination in the central slice factors as the common power
times a sum of two consecutive powers for each normalized coefficient. -/
theorem shiftedMoment_linearCombination_small_interval {L p : ℕ} (hL : 1 ≤ L)
    (c : Fin p → ℝ) {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1/4) :
    (∑ j : Fin p, c j * shiftedMoment (L+j.val-1) u) =
      u^(L-1) * ∑ j : Fin p, (c j / ((L+j.val).factorial:ℝ)) *
        ((L+j.val:ℕ)*u^j.val - u^(j.val+1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [shiftedMoment_eq_tailMomentWeight_on_small_interval _ hu hu']
  unfold tailMomentWeight
  have hj : L+j.val-1+1 = L+j.val := by omega
  rw [hj, show L+j.val-1 = L-1+j.val by omega, pow_add,
    show L+j.val = L-1+(j.val+1) by omega, pow_add]
  have hfac : (L+j.val).factorial = (L+j.val)*(L+j.val-1).factorial := by
    calc
      _ = ((L+j.val-1)+1).factorial := congrArg Nat.factorial hj.symm
      _ = _ := by rw [Nat.factorial_succ, hj]
  -- Restore the original factorial indices before clearing the denominators.
  rw [show L-1+j.val = L+j.val-1 by omega, show L-1+(j.val+1) = L+j.val by omega]
  have hn : (L:ℝ)+(j.val:ℝ) ≠ 0 := by
    exact_mod_cast (show L+j.val ≠ 0 by omega)
  have hfn : ((L+j.val-1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  rw [hfac]
  push_cast
  field_simp

/-- The polynomial left after removing the common central power. -/
noncomputable def shiftCentralSlicePolynomial {p : ℕ} (L : ℕ) (b : Fin p → ℝ) : Polynomial ℝ :=
  ∑ j : Fin p, (Polynomial.monomial j.val ((L+j.val:ℕ)*b j) -
    Polynomial.monomial (j.val+1) (b j))

theorem shiftCentralSlicePolynomial_natDegree_le {p : ℕ} (L : ℕ) (b : Fin p → ℝ) :
    (shiftCentralSlicePolynomial L b).natDegree ≤ p := by
  unfold shiftCentralSlicePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le
    ((Polynomial.natDegree_monomial_le ((L+j.val:ℕ)*b j) (m := j.val)).trans j.isLt.le)
    ((Polynomial.natDegree_monomial_le (b j) (m := j.val+1)).trans (Nat.succ_le_of_lt j.isLt))

theorem shiftedMoment_linearCombination_eq_polynomial {L p : ℕ} (hL : 1 ≤ L)
    (c : Fin p → ℝ) {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1/4) :
    (∑ j : Fin p, c j * shiftedMoment (L+j.val-1) u) =
      u^(L-1) * (shiftCentralSlicePolynomial L
        (fun j => c j / ((L+j.val).factorial:ℝ))).eval u := by
  rw [shiftedMoment_linearCombination_small_interval hL c hu hu']
  congr 1
  simp only [shiftCentralSlicePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_sub,
    Polynomial.eval_monomial]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem coeff_shiftCentralSlicePolynomial {L p : ℕ} (b : Fin p → ℝ) (j : Fin p) :
    (shiftCentralSlicePolynomial L b).coeff j.val =
      ((L+j.val:ℕ):ℝ) * b j - if h : 0 < j.val then b ⟨j.val-1, by omega⟩ else 0 := by
  classical
  simp only [shiftCentralSlicePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_sub,
    Polynomial.coeff_monomial, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ h
      exact ite_eq_right (fun hij => h (Fin.ext hij))
    · simp
  · split_ifs with hj
    · let k : Fin p := ⟨j.val-1, by omega⟩
      rw [Finset.sum_eq_single k]
      · rw [ite_eq_left (show k.val+1 = j.val by dsimp [k]; omega)]
      · intro i _ hi
        exact ite_eq_right (fun hij => hi (Fin.ext (by dsimp [k]; omega)))
      · simp
    · exact Finset.sum_eq_zero (fun i _ => ite_eq_right (by omega))

theorem abs_le_abs_shiftCentralSlicePolynomial_coeff_of_max {L p : ℕ} (hL : 2 ≤ L)
    (b : Fin p → ℝ) (j : Fin p) (hmax : ∀ i, |b i| ≤ |b j|) :
    |b j| ≤ |(shiftCentralSlicePolynomial L b).coeff j.val| := by
  rw [coeff_shiftCentralSlicePolynomial]
  apply abs_le_abs_adjacent_coefficient
  · exact_mod_cast (show 2 ≤ L+j.val by omega)
  · split_ifs
    · exact hmax _
    · simp

#print axioms shiftedMoment_eq_tailMomentWeight_on_small_interval
#print axioms shiftedMoment_linearCombination_small_interval
#print axioms abs_le_abs_shiftCentralSlicePolynomial_coeff_of_max

end Nuttall
