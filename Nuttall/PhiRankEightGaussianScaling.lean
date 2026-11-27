import Nuttall.PhiCompactNormalization
import Nuttall.PhiRankEightGaussianRows

namespace Nuttall

open scoped BigOperators

/-- Scale the ordinary coefficient of degree i into the normalized monomial basis. -/
noncomputable def phiRankEightBasisScale (X : ℝ) (i : ℕ) : ℝ :=
  Real.sqrt (i.factorial:ℝ) / (Real.sqrt X)^i

theorem phiRankEightBasisScale_pos {X : ℝ} (hX : 0 < X) (i : ℕ) :
    0 < phiRankEightBasisScale X i :=
  div_pos (Real.sqrt_pos.2 (by positivity)) (pow_pos (Real.sqrt_pos.2 hX) _)

theorem phiRankEightBasisScale_succ (X : ℝ) (i : ℕ) :
    Real.sqrt ((i+1:ℕ):ℝ) / Real.sqrt X * phiRankEightBasisScale X i =
      phiRankEightBasisScale X (i+1) := by
  unfold phiRankEightBasisScale
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity : 0 ≤ ((i+1:ℕ):ℝ)),
    pow_succ, div_mul_div_comm, mul_comm ((Real.sqrt X)^i)]

theorem phiRankEightGaussian_eq_scaled_compact {X : ℝ} (hX : 0 < X) (q : ℝ) (i j : ℕ) :
    phiRankEightGaussian X q i j =
      (phiRankEightBasisScale X i * phiRankEightBasisScale X j) *
        phiCompactGaussian X q i j * Real.exp (-(q-1)*X) := by
  unfold phiRankEightGaussian phiCompactGaussian
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  let s := Real.sqrt X
  let m := (i-k)+(j-k)
  have hs : 0 < s := Real.sqrt_pos.2 hX
  have hsX : s^2 = X := Real.sq_sqrt hX.le
  have hk' := Finset.mem_range.mp hk
  have he : i+j = m+2*k := by dsimp [m]; omega
  have hp : (-(q-1)*s)^m*(-q)^k*s^(i+j) =
      (-(q-1)*X)^m*(-q*X)^k := by
    calc
      _ = ((-(q-1)*s)^m*s^m)*((-q)^k*(s^2)^k) := by
        rw [he, pow_add s m (2*k), pow_mul s 2 k]
        ring
      _ = ((-(q-1)*s)*s)^m*((-q)*(s^2))^k := by simp only [mul_pow]
      _ = _ := by rw [mul_assoc (-(q-1)) s s, ← pow_two, hsX]
  have hraw :
      ((-(q-1)*X)^(i-k) / ((i-k).factorial:ℝ)) *
        ((-(q-1)*X)^(j-k) / ((j-k).factorial:ℝ)) *
        ((-q*X)^k / (k.factorial:ℝ)) =
      (-(q-1)*X)^m*(-q*X)^k /
        (((i-k).factorial:ℝ)*((j-k).factorial:ℝ)*(k.factorial:ℝ)) := by
    rw [div_mul_div_comm, div_mul_div_comm, ← pow_add]
  rw [hraw]
  change (Real.sqrt ((i.factorial:ℝ)*(j.factorial:ℝ)) * (-(q-1)*s)^m *
      (-q)^k / (((i-k).factorial:ℝ)*((j-k).factorial:ℝ)*(k.factorial:ℝ))) = _
  rw [Real.sqrt_mul (by positivity : 0 ≤ (i.factorial:ℝ))]
  unfold phiRankEightBasisScale
  change Real.sqrt (i.factorial:ℝ)*Real.sqrt (j.factorial:ℝ)* (-(q-1)*s)^m *
      (-q)^k / _ = (Real.sqrt (i.factorial:ℝ)/s^i * (Real.sqrt (j.factorial:ℝ)/s^j)) * _
  rw [div_mul_div_comm, ← pow_add, ← hp]
  field_simp [hs.ne']

#print axioms phiRankEightGaussian_eq_scaled_compact
#print axioms phiRankEightBasisScale_succ

end Nuttall
