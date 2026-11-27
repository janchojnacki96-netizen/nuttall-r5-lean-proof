import Nuttall.ShiftReflectionOrthogonality
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Nuttall

open scoped BigOperators

/-- The diagonal weight is no larger than the scalar exponential on the shift interval. -/
theorem shiftScale_le_exp_neg {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    shiftScale d ≤ Real.exp (-d) := by
  let F (x : ℝ) := Real.exp (-2*x)*(1+x)-(1-x)
  have hderiv (x : ℝ) :
      HasDerivAt F (1-(1+2*x)*Real.exp (-2*x)) x := by
    have he := (Real.hasDerivAt_exp (-2*x)).comp x ((hasDerivAt_id x).const_mul (-2))
    convert (he.mul ((hasDerivAt_id x).const_add 1)).sub ((hasDerivAt_id x).const_mul (-1) |>.const_add 1) using 1
    · funext y
      simp [F]
      ring
    · simp
      ring
  have hm : MonotoneOn F (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun x => (hderiv x).continuousAt)).continuousOn
    · intro x hx
      exact (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hderiv x).deriv]
      have h := Real.add_one_le_exp (2*x)
      have hex : (1+2*x)*Real.exp (-2*x) ≤ 1 := by
        rw [show -2*x = -(2*x) by ring, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        linarith only [h]
      linarith only [hex]
  have hF : 0 ≤ F d := by
    have h := hm (show 0 ∈ Set.Ici (0:ℝ) from Set.mem_Ici.mpr le_rfl) hd₀ hd₀
    simpa [F] using h
  have hp : 0 < 1+d := by linarith
  unfold shiftScale
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_nonneg _)).mp
  rw [Real.sq_sqrt (div_nonneg (sub_nonneg.2 hd₁) hp.le), ← Real.exp_nat_mul]
  apply (div_le_iff₀ hp).2
  rw [show (↑(2:ℕ) : ℝ) * -d = -2*d by push_cast; ring]
  linarith only [hF]

theorem shiftScale_pow_le_exp_neg {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (a : ℕ) :
    shiftScale d ^ a ≤ Real.exp (-d*(a:ℝ)) := by
  rw [show -d*(a:ℝ) = (a:ℝ)*(-d) by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (shiftScale_le_exp_neg hd₀ hd₁) _

private theorem abs_reflectionPower_entry_le_one {M k : ℕ} {d : ℝ} (hk : k ≤ M+1)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (i j : Fin k) :
    |shiftReflectionPower M k d i j| ≤ 1 := by
  let T := shiftReflectionPower M (M+1) d
  let i' := Fin.castLE hk i
  let j' := Fin.castLE hk j
  have h := congrArg (fun A : Matrix (Fin (M+1)) (Fin (M+1)) ℝ => A j' j')
    (shiftReflectionPower_transpose_mul hd₀ hd₁ M)
  have hsum : ∑ l : Fin (M+1), (T l j')^2 = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq, T] using h
  have hi : (T i' j')^2 ≤ 1 :=
    (Finset.single_le_sum (f := fun l => (T l j')^2) (fun l _ => sq_nonneg _) (Finset.mem_univ i')).trans_eq hsum
  change |T i' j'| ≤ 1
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa only [sq_abs, one_pow] using hi

/-- The coefficient bound away from the central square used in equation eq:shift. -/
theorem abs_shiftCore_le_offCentral {M k : ℕ} {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d < 1)
    (hM : 2*(k-1) ≤ M) (i j : Fin k)
    (hoff : Real.sqrt (M : ℝ)/16 ≤ (M : ℝ)/2 - i.val ∨
            Real.sqrt (M : ℝ)/16 ≤ (M : ℝ)/2 - j.val) :
    |shiftCore M k d i j| ≤ Real.exp (-d*Real.sqrt (M : ℝ)/16) := by
  have hi := i.isLt
  have hj := j.isLt
  have hsum : i.val+j.val ≤ M := by omega
  have hk : k ≤ M+1 := by omega
  have hi' : (2 * i.val : ℕ) ≤ M := by omega
  have hj' : (2 * j.val : ℕ) ≤ M := by omega
  have hi'' : (i.val : ℝ) ≤ (M : ℝ)/2 := by
    have h : (2 : ℝ) * i.val ≤ M := by exact_mod_cast hi'
    linarith
  have hj'' : (j.val : ℝ) ≤ (M : ℝ)/2 := by
    have h : (2 : ℝ) * j.val ≤ M := by exact_mod_cast hj'
    linarith
  have hex : Real.sqrt (M : ℝ)/16 ≤ ((M-(i.val+j.val) : ℕ) : ℝ) := by
    rw [Nat.cast_sub hsum, Nat.cast_add]
    rcases hoff with h | h <;> linarith
  have hs : 0 ≤ shiftScale d := Real.sqrt_nonneg _
  rw [shiftCore_eq_scaled_reflectionPower hd₀ hd₁ hM, abs_mul,
    abs_of_nonneg (pow_nonneg hs _)]
  calc
    _ ≤ shiftScale d ^ (M-(i.val+j.val)) :=
      mul_le_of_le_one_right (pow_nonneg hs _)
        (abs_reflectionPower_entry_le_one hk hd₀ hd₁.le i j)
    _ ≤ Real.exp (-d * ((M-(i.val+j.val) : ℕ) : ℝ)) :=
      shiftScale_pow_le_exp_neg hd₀ hd₁.le _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hex hd₀])

#print axioms shiftScale_le_exp_neg
#print axioms abs_shiftCore_le_offCentral

end Nuttall
