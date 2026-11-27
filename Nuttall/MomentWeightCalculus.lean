import Nuttall.TailMoments

namespace Nuttall

private theorem normalizedPower_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => y^(k+1) / ((k+1).factorial : ℝ))
      (x^k / (k.factorial : ℝ)) x := by
  have h := ((hasDerivAt_id x).pow (k+1)).div_const ((k+1).factorial : ℝ)
  convert h using 1
  · funext y
    simp only [Pi.pow_apply, id_eq]
  · simp only [id_eq, Nat.add_sub_cancel, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hk : (k.factorial : ℝ) ≠ 0 := by positivity
    have hs : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk, hs] <;> ring

theorem tailMomentWeight_succ_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (tailMomentWeight (k+1)) (tailMomentWeight k x) x :=
  (normalizedPower_hasDerivAt k x).sub (normalizedPower_hasDerivAt (k+1) x)

theorem tailMomentWeight_succ_zero (k : ℕ) : tailMomentWeight (k+1) 0 = 0 := by
  simp [tailMomentWeight]

/-- Every derivative through the index is the corresponding lower weight. -/
theorem iteratedDeriv_tailMomentWeight {j k : ℕ} (hkj : k ≤ j) (x : ℝ) :
    iteratedDeriv k (tailMomentWeight j) x = tailMomentWeight (j-k) x := by
  induction k generalizing j x with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ j := by omega
    have hfun : iteratedDeriv k (tailMomentWeight j) = tailMomentWeight (j-k) :=
      funext (ih hk)
    rw [iteratedDeriv_succ, hfun]
    rw [show j-k = (j-(k+1))+1 by omega]
    exact (tailMomentWeight_succ_hasDerivAt (j-(k+1)) x).deriv

/-- The finite boundary terms in successive integrations by parts vanish. -/
theorem iteratedDeriv_tailMomentWeight_zero {j k : ℕ} (hkj : k < j) :
    iteratedDeriv k (tailMomentWeight j) 0 = 0 := by
  rw [iteratedDeriv_tailMomentWeight hkj.le,
    show j-k = (j-k-1)+1 by omega, tailMomentWeight_succ_zero]

#print axioms iteratedDeriv_tailMomentWeight_zero

end Nuttall
