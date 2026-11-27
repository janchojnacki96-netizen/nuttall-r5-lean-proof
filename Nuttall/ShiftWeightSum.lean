import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

namespace Nuttall

open scoped BigOperators

theorem sum_inv_sqrt_succ_le (m : ℕ) :
    (∑ n ∈ Finset.range m, 1/Real.sqrt ((n:ℝ)+1)) ≤ 2*Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
    have hp : 0 < Real.sqrt ((m:ℝ)+1) := Real.sqrt_pos.2 (by positivity)
    have hmon := Real.sqrt_le_sqrt (show (m:ℝ) ≤ (m:ℝ)+1 by linarith)
    have hprod : (Real.sqrt ((m:ℝ)+1)-Real.sqrt m) *
        (Real.sqrt ((m:ℝ)+1)+Real.sqrt m) = 1 := by
      nlinarith only [Real.sq_sqrt hm, Real.sq_sqrt (show 0 ≤ (m:ℝ)+1 by positivity)]
    have hstep : 1/Real.sqrt ((m:ℝ)+1) ≤ 2*(Real.sqrt ((m:ℝ)+1)-Real.sqrt m) := by
      apply (div_le_iff₀ hp).2
      calc
        1 = _ := hprod.symm
        _ ≤ (Real.sqrt ((m:ℝ)+1)-Real.sqrt m)*(2*Real.sqrt ((m:ℝ)+1)) :=
          mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.2 hmon)
        _ = _ := by ring
    linarith only [ih, hstep]

private theorem sum_cross_sqrt_half {s : Finset ℕ} {m : ℕ} (hm : 0 < m)
    (a b : ℕ → ℕ) (ha : Set.InjOn a s)
    (ha₀ : ∀ n ∈ s, 1 ≤ a n) (ha₁ : ∀ n ∈ s, a n ≤ m)
    (hb : ∀ n ∈ s, m ≤ b n) :
    (∑ n ∈ s, 1/Real.sqrt ((a n:ℝ)*(b n:ℝ))) ≤ 2 := by
  have hp : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  calc
    _ ≤ ∑ l ∈ Finset.range m, (1/Real.sqrt ((l:ℝ)+1))/Real.sqrt m := by
      apply Finset.sum_le_sum_of_injOn (fun n => a n-1)
      · intro x hx y hy he
        change a x-1 = a y-1 at he
        apply ha hx hy
        have := ha₀ x hx
        have := ha₀ y hy
        omega
      · intro l hl
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hl
        exact Finset.mem_range.mpr (by have := ha₁ n hn; omega)
      · intro n hn
        have hz : ((a n-1:ℕ):ℝ)+1 = (a n:ℝ) := by
          rw [Nat.cast_sub (ha₀ n hn), Nat.cast_one, sub_add_cancel]
        change _ ≤ (1/Real.sqrt (((a n-1:ℕ):ℝ)+1))/Real.sqrt m
        rw [hz, div_div, Real.sqrt_mul (Nat.cast_nonneg _)]
        apply one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.2 (by exact_mod_cast ha₀ n hn)) hp)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hb n hn))
          (Real.sqrt_nonneg _)
      · intro l _ _
        positivity
    _ ≤ _ := by
      rw [← Finset.sum_div]
      exact (div_le_iff₀ hp).2 (sum_inv_sqrt_succ_le m)

/-- Splitting at the midpoint and reflecting the second half gives a bound
independent of the last active theta index. -/
theorem sum_cross_inv_sqrt_le_four (K : ℕ) :
    (∑ n ∈ Finset.Ico 1 K, 1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) ≤ 4 := by
  classical
  by_cases hK : 2 ≤ K
  · let s := Finset.Ico 1 K
    let m := K/2
    have hm : 0 < m := by dsimp [m]; omega
    have he (n : ℕ) (hn : n ∈ s) : ((K:ℝ)-(n:ℝ)) = ((K-n:ℕ):ℝ) :=
      (Nat.cast_sub (Finset.mem_Ico.mp hn).2.le).symm
    have hlo :=
      sum_cross_sqrt_half (s := s.filter (fun n => n ≤ m)) hm id (fun n => K-n)
        Function.injective_id.injOn
        (fun n hn => (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1)
        (fun n hn => (Finset.mem_filter.mp hn).2)
        (fun n hn => by
          have h := (Finset.mem_filter.mp hn).2
          dsimp [m] at *
          omega)
    have hhi :=
      sum_cross_sqrt_half (s := s.filter (fun n => ¬n ≤ m)) hm (fun n => K-n) id
        (by
          intro x hx y hy h
          have hx' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1).2
          have hy' := (Finset.mem_Ico.mp (Finset.mem_filter.mp hy).1).2
          dsimp at h
          omega)
        (fun n hn => by have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).2; omega)
        (fun n hn => by have := (Finset.mem_filter.mp hn).2; dsimp [m] at *; omega)
        (fun n hn => (Nat.lt_of_not_ge (Finset.mem_filter.mp hn).2).le)
    change (∑ n ∈ s, 1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) ≤ 4
    rw [← Finset.sum_filter_add_sum_filter_not s (fun n => n ≤ m)]
    have h₁ : (∑ n ∈ s.filter (fun n => n ≤ m), 1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) ≤ 2 := by
      convert hlo using 1
      exact Finset.sum_congr rfl (fun n hn => by rw [he n (Finset.mem_filter.mp hn).1]; rfl)
    have h₂ : (∑ n ∈ s.filter (fun n => ¬n ≤ m), 1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) ≤ 2 := by
      convert hhi using 1
      exact Finset.sum_congr rfl (fun n hn => by rw [he n (Finset.mem_filter.mp hn).1, mul_comm]; rfl)
    linarith only [h₁, h₂]
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    norm_num

#print axioms sum_cross_inv_sqrt_le_four

end Nuttall
