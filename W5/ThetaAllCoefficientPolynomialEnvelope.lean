import W5.ThetaAllCoefficientGenericSplitting

/-!
# One quantitative polynomial envelope for ALL 25 theta coefficients

The numerically defined B_ij(d,q) are finite polynomials with
total degrees at most eight for i,j : Fin 5. Instead of bounding
25 explicit polynomials one at a time, we majorize every monomial
by the SAME eighth power of 1 + |d| + |q|.

The only multiplier is the finite sum of absolute values of the
EXACT factorial coefficients, which is a nonnegative real constant
for each i,j. It requires NO numerical approximations.

The resulting envelope is designed to combine with the previously
verified, separable theta Gaussian index/w-tail majorants. It is
not yet an analytic proof of correction-series summability or
a determinant-sign statement.
-/

namespace W5

/-- Total absolute weight of the finite original B_ij polynomial,
with factorials taken EXACTLY as in the numerical certificate. -/
noncomputable def thetaCoefficientAbsoluteWeight
    (i j : Fin 5) : ℝ :=
  ∑ k ∈ Finset.range (min i.val j.val + 1),
    |(((-1:ℝ) ^ (i.val + j.val - k)) /
      ((Nat.factorial k : ℝ) *
       (Nat.factorial (i.val-k) : ℝ) *
       (Nat.factorial (j.val-k) : ℝ)))|

theorem thetaCoefficientAbsoluteWeight_nonneg (i j : Fin 5) :
    0 ≤ thetaCoefficientAbsoluteWeight i j := by
  unfold thetaCoefficientAbsoluteWeight
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- A single eighth-degree envelope controls EVERY certificate
coefficient B_ij(d,q) for i,j:Fin5, with no x- or n-dependent
assumptions and no appeal to unproved coefficient positivity. -/
theorem coefficientPolynomial_abs_le_eighth_power
    (i j : Fin 5) (d q : ℝ) :
    |coefficientPolynomial i j d q| ≤
      thetaCoefficientAbsoluteWeight i j *
        (1+|d|+|q|)^8 := by
  let R : ℝ := 1+|d|+|q|
  have hR1 : 1 ≤ R := by
    dsimp [R]
    have hd : 0 ≤ |d| := abs_nonneg d
    have hq : 0 ≤ |q| := abs_nonneg q
    linarith
  have hdR : |d| ≤ R := by
    dsimp [R]
    have hq : 0 ≤ |q| := abs_nonneg q
    linarith
  have hqR : |q| ≤ R := by
    dsimp [R]
    have hd : 0 ≤ |d| := abs_nonneg d
    linarith
  have hmono (k : ℕ)
      (hk : k ∈ Finset.range (min i.val j.val + 1)) :
      |d|^(i.val+j.val-2*k) * |q|^k ≤ R^8 := by
    have hi : i.val < 5 := i.isLt
    have hj : j.val < 5 := j.isLt
    have hki : k ≤ min i.val j.val :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hexp : i.val+j.val-2*k+k ≤ 8 := by omega
    calc
      |d|^(i.val+j.val-2*k) * |q|^k ≤
          R^(i.val+j.val-2*k) * R^k := by gcongr
      _ = R^(i.val+j.val-2*k+k) := by rw [pow_add]
      _ ≤ R^8 := pow_le_pow_right₀ hR1 hexp
  have hterm (k : ℕ) :
      |(((-1:ℝ)^(i.val+j.val-k) *
        d^(i.val+j.val-2*k) * q^k) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ)))| =
      |(((-1:ℝ)^(i.val+j.val-k)) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ)))| *
      (|d|^(i.val+j.val-2*k) * |q|^k) := by
    rw [div_eq_mul_inv]
    simp only [abs_mul, abs_pow]
    ring
  unfold coefficientPolynomial
  calc
    |∑ k ∈ Finset.range (min i.val j.val + 1),
      (((-1:ℝ)^(i.val+j.val-k) *
        d^(i.val+j.val-2*k) * q^k) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ)))| ≤
      ∑ k ∈ Finset.range (min i.val j.val + 1),
        |(((-1:ℝ)^(i.val+j.val-k) *
          d^(i.val+j.val-2*k) * q^k) /
          ((Nat.factorial k : ℝ) *
           (Nat.factorial (i.val-k) : ℝ) *
           (Nat.factorial (j.val-k) : ℝ)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (min i.val j.val + 1),
      |(((-1:ℝ)^(i.val+j.val-k)) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ)))| * R^8 := by
          apply Finset.sum_le_sum
          intro k hk
          rw [hterm]
          exact mul_le_mul_of_nonneg_left (hmono k hk) (abs_nonneg _)
    _ = thetaCoefficientAbsoluteWeight i j * (1+|d|+|q|)^8 := by
      rw [← Finset.sum_mul]
      rfl

end W5
