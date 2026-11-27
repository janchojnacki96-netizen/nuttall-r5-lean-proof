import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Nuttall

open scoped BigOperators

/-- Magnitude of the Gaussian coefficient term at X=16 and q=4 after
using q-1 ≤ q and max(i!,j!) in place of the factorial square root. -/
def phiRankEightGaussianMajorantTerm (i j k : ℕ) : ℚ :=
  (4:ℚ)^(2*((i-k)+(j-k))+k) * (max i.factorial j.factorial:ℕ) /
    (((i-k).factorial:ℚ)*((j-k).factorial:ℚ)*(k.factorial:ℚ))

def phiRankEightGaussianMajorantRow (i : Fin 8) : ℚ :=
  ∑ j : Fin 8, ∑ k ∈ Finset.range (min i.val j.val+1),
    phiRankEightGaussianMajorantTerm i.val j.val k

set_option maxRecDepth 32768 in
set_option maxHeartbeats 6000000 in
theorem phiRankEightGaussianMajorantRow_lt (i : Fin 8) :
    phiRankEightGaussianMajorantRow i < 2^46 := by
  fin_cases i <;> decide +kernel

private noncomputable def phiRankEightGaussianTerm (X q : ℝ) (i j k : ℕ) : ℝ :=
  Real.sqrt ((i.factorial:ℝ)*(j.factorial:ℝ)) *
    (-(q-1)*Real.sqrt X)^((i-k)+(j-k)) * (-q)^k /
      (((i-k).factorial:ℝ)*((j-k).factorial:ℝ)*(k.factorial:ℝ))

/-- The normalized coefficient of u^i v^j in the Gaussian factor of the
square-index term, in the basis u^i / √i! and v^j / √j!. -/
noncomputable def phiRankEightGaussian (X q : ℝ) (i j : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (min i j+1), phiRankEightGaussianTerm X q i j k) *
    Real.exp (-(q-1)*X)

theorem phiRankEightGaussian_one (X : ℝ) (i j : ℕ) :
    phiRankEightGaussian X 1 i j = if i = j then (-1:ℝ)^i else 0 := by
  have hv (k : ℕ) (hk : k ≤ min i j) (hn : i ≠ k ∨ j ≠ k) :
      phiRankEightGaussianTerm X 1 i j k = 0 := by
    have hki := hk.trans (min_le_left i j)
    have hkj := hk.trans (min_le_right i j)
    have hm : (i-k)+(j-k) ≠ 0 := by omega
    simp [phiRankEightGaussianTerm, zero_pow hm]
  unfold phiRankEightGaussian
  simp only [sub_self, neg_zero, zero_mul, Real.exp_zero, mul_one]
  by_cases he : i = j
  · subst j
    rw [ite_eq_left rfl, Finset.sum_eq_single i]
    · have hf : (i.factorial:ℝ) ≠ 0 := by positivity
      simp only [phiRankEightGaussianTerm, Nat.sub_self, sub_self, Nat.add_zero, pow_zero,
        mul_one, Nat.factorial_zero, Nat.cast_one, one_mul]
      rw [Real.sqrt_mul_self (by positivity)]
      field_simp
    · intro k hk hki
      exact hv k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) (Or.inl hki.symm)
    · simp
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro k hk
    exact hv k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) (by omega)

private theorem rankEightGaussianTerm_bound {X q : ℝ} (hX : 16 ≤ X) (hq : 4 ≤ q)
    (i j k : ℕ) (hi : i < 8) (hj : j < 8) (hk : k ≤ min i j) :
    |phiRankEightGaussianTerm X q i j k| ≤
      (phiRankEightGaussianMajorantTerm i j k:ℝ) * ((X/16)^7*(q/4)^14) := by
  let m := (i-k)+(j-k)
  have hm : m ≤ 14 := by dsimp [m]; omega
  have hmk : m+k ≤ 14 := by
    have hki := hk.trans (min_le_left i j)
    have hkj := hk.trans (min_le_right i j)
    dsimp [m]
    omega
  have hq' : 0 ≤ q := by linarith
  have hq₁ : 0 ≤ q-1 := by linarith
  have hx₁ : 1 ≤ X/16 := by linarith
  have hx₀ : 0 ≤ X/16 := by linarith
  have hy₁ : 1 ≤ q/4 := by linarith
  have hs₁ : 1 ≤ Real.sqrt (X/16) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx₁
  have hsixteen : Real.sqrt (16:ℝ) = 4 := by
    have h := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)
    norm_num at h
    exact h
  have hsqrt : Real.sqrt X = 4*Real.sqrt (X/16) := by
    calc
      _ = Real.sqrt (16*(X/16)) := congrArg Real.sqrt (by ring)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : 0 ≤ (16:ℝ)), hsixteen]
  have hxpow : (Real.sqrt (X/16))^m ≤ (X/16)^7 :=
    (pow_le_pow_right₀ hs₁ hm).trans_eq (by
      change (Real.sqrt (X/16))^(2*7) = _
      rw [pow_mul, Real.sq_sqrt hx₀])
  have hqpow : (q/4)^(m+k) ≤ (q/4)^14 := pow_le_pow_right₀ hy₁ hmk
  have hv : ((q-1)*Real.sqrt X)^m*q^k ≤
      4^(2*m+k)*((X/16)^7*(q/4)^14) := by
    calc
      _ ≤ (q*Real.sqrt X)^m*q^k :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_right (by linarith : q-1 ≤ q) (Real.sqrt_nonneg _)) m)
          (by positivity)
      _ = (4*(q/4)*(4*Real.sqrt (X/16)))^m*(4*(q/4))^k := by
        rw [← hsqrt, show 4*(q/4) = q by ring]
      _ = 4^(2*m+k) * ((Real.sqrt (X/16))^m*(q/4)^(m+k)) := by
        have hfour : (4:ℝ)^(2*m) = 4^m*4^m := by rw [two_mul, pow_add]
        rw [pow_add (4:ℝ) (2*m) k, hfour, pow_add (q/4) m k]
        simp only [mul_pow]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul hxpow hqpow (by positivity) (by positivity)) (by positivity)
  let F := (max i.factorial j.factorial:ℕ)
  have hF : Real.sqrt ((i.factorial:ℝ)*(j.factorial:ℝ)) ≤ (F:ℝ) := by
    have hi' : (i.factorial:ℝ) ≤ (F:ℝ) := by exact_mod_cast (le_max_left i.factorial j.factorial)
    have hj' : (j.factorial:ℝ) ≤ (F:ℝ) := by exact_mod_cast (le_max_right i.factorial j.factorial)
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by
      rw [pow_two]
      exact mul_le_mul hi' hj' (by positivity) (by positivity)⟩
  have hD : 0 < (((i-k).factorial:ℝ)*((j-k).factorial:ℝ)*(k.factorial:ℝ)) := by positivity
  unfold phiRankEightGaussianTerm
  rw [abs_div, abs_of_pos hD, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_pow, abs_pow, abs_neg, abs_mul, abs_neg, abs_of_nonneg hq₁,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hq']
  change Real.sqrt ((i.factorial:ℝ)*(j.factorial:ℝ))*((q-1)*Real.sqrt X)^m*q^k /
      _ ≤ _
  rw [mul_assoc]
  apply (div_le_div_of_nonneg_right
    (mul_le_mul hF hv (by positivity) (by positivity)) hD.le).trans_eq
  simp only [phiRankEightGaussianMajorantTerm, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat, F, m]
  ring

theorem phiRankEightGaussian_row_le {X q : ℝ} (hX : 16 ≤ X) (hq : 4 ≤ q) (i : Fin 8) :
    (∑ j : Fin 8, |phiRankEightGaussian X q i.val j.val|) ≤
      2^46*(X/16)^7*(q/4)^14*Real.exp (-(q-1)*X) := by
  let factor := ((X/16)^7*(q/4)^14)*Real.exp (-(q-1)*X)
  have hf : 0 ≤ factor := by dsimp [factor]; positivity
  have hrow : (phiRankEightGaussianMajorantRow i:ℝ) ≤ (2:ℝ)^46 := by
    simpa only [Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_mono (K := ℝ) (phiRankEightGaussianMajorantRow_lt i).le)
  simp only [phiRankEightGaussianMajorantRow, Rat.cast_sum] at hrow
  have hentry (j : Fin 8) :
      |phiRankEightGaussian X q i.val j.val| ≤
        (∑ k ∈ Finset.range (min i.val j.val+1), (phiRankEightGaussianMajorantTerm i.val j.val k:ℝ)) *
          factor := by
    unfold phiRankEightGaussian
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le).trans
    have hh := Finset.sum_le_sum (s := Finset.range (min i.val j.val+1)) (fun k hk =>
      rankEightGaussianTerm_bound hX hq i.val j.val k i.isLt j.isLt
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
    rw [← Finset.sum_mul] at hh
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hentry j)
  rw [← Finset.sum_mul] at hs
  have hm := hs.trans (mul_le_mul_of_nonneg_right hrow hf)
  simpa only [factor, mul_assoc] using hm

#print axioms phiRankEightGaussianMajorantRow_lt
#print axioms phiRankEightGaussian_row_le
#print axioms phiRankEightGaussian_one

end Nuttall
