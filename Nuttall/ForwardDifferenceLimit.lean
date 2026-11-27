import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Asymptotics.Lemmas

namespace Nuttall

open Filter Function Set Asymptotics
open scoped Topology BigOperators

private theorem fwdDiff_affine (n : ℕ) (f : ℝ → ℝ) (t h z : ℝ) :
    (fwdDiff 1)^[n] (fun x : ℝ => f (t+x*h)) z = (fwdDiff h)^[n] f (t+z*h) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    simp only [fwdDiff, ih]
    rw [show t+(z+1)*h = t+z*h+h by ring]

private theorem fwdDiff_taylor (f : ℝ → ℝ) (n : ℕ) (t h : ℝ) :
    (fwdDiff h)^[n] (taylorWithinEval f n univ t) t = h^n*iteratedDeriv n f t := by
  let T := taylorWithinEval f n univ t
  let c (k : ℕ) := ((k.factorial:ℝ)⁻¹ * iteratedDeriv k f t) * h^k
  have hPoly : (fun x : ℝ => T (t+x*h)) =
      ∑ k ∈ Finset.range (n+1), c k • (fun x : ℝ => x^k) := by
    funext x
    simp only [T, c, taylor_within_apply, iteratedDerivWithin_univ, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, mul_pow]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  calc
    _ = (fwdDiff 1)^[n] (fun x : ℝ => T (t+x*h)) 0 := by
      simpa only [zero_mul, add_zero] using (fwdDiff_affine n T t h 0).symm
    _ = _ := by
      rw [hPoly, fwdDiff_iter_finsetSum]
      simp only [fwdDiff_iter_const_smul, Finset.sum_apply]
      rw [Finset.sum_eq_single n]
      · rw [fwdDiff_iter_eq_factorial]
        change c n * (n.factorial:ℝ) = _
        dsimp [c]
        field_simp
        <;> ring
      · intro k hk hkn
        rw [fwdDiff_iter_pow_eq_zero_of_lt (by have := Finset.mem_range.1 hk; omega)]
        simp
      · simp

/-- Dividing the (n)-th forward difference by (h^n) recovers the
(n)-th derivative as the positive mesh size tends to zero. -/
theorem tendsto_normalized_fwdDiff {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ n f) (t : ℝ) :
    Tendsto (fun h : ℝ => (fwdDiff h)^[n] f t / h^n) (𝓝[>] (0:ℝ))
      (𝓝 (iteratedDeriv n f t)) := by
  let T := taylorWithinEval f n univ t
  let R (x : ℝ) := f x - T x
  have hR : R =o[𝓝 t] (fun x : ℝ => (x-t)^n) := taylor_isLittleO_univ hf
  have hterm (k : ℕ) : (fun h : ℝ => R (t+k•h)) =o[𝓝 (0:ℝ)] (fun h : ℝ => h^n) := by
    have hc : Continuous (fun h : ℝ => t+(k:ℝ)*h) := by fun_prop
    have ht : Tendsto (fun h : ℝ => t+(k:ℝ)*h) (𝓝 (0:ℝ)) (𝓝 t) := by
      simpa using (hc.continuousAt (x := (0:ℝ))).tendsto
    have hcomp := hR.comp_tendsto ht
    have hcoef : (fun h : ℝ => ((k:ℝ)*h)^n) =O[𝓝 (0:ℝ)] (fun h : ℝ => h^n) := by
      simpa only [mul_pow] using (isBigO_refl (fun h : ℝ => h^n) (𝓝 (0:ℝ))).const_mul_left ((k:ℝ)^n)
    exact (by simpa only [Function.comp_def, nsmul_eq_mul, add_sub_cancel_left] using hcomp :
      (fun h : ℝ => R (t+k•h)) =o[𝓝 (0:ℝ)] (fun h : ℝ => ((k:ℝ)*h)^n)).trans_isBigO hcoef
  have hs : (fun h : ℝ => (fwdDiff h)^[n] R t) =o[𝓝 (0:ℝ)] (fun h : ℝ => h^n) := by
    simp only [fwdDiff_iter_eq_sum_shift, zsmul_eq_mul]
    let a (k : ℕ) (h : ℝ) := (((-1:ℤ)^(n-k)*n.choose k:ℤ):ℝ) * R (t+k•h)
    have he : (∑ k ∈ Finset.range (n+1), a k) = fun h => ∑ k ∈ Finset.range (n+1), a k h :=
      funext (fun h => Finset.sum_apply h _ _)
    change (fun h => ∑ k ∈ Finset.range (n+1), a k h) =o[𝓝 (0:ℝ)] (fun h : ℝ => h^n)
    rw [← he]
    exact IsLittleO.sum (fun k _ => (hterm k).const_mul_left _)
  have hsub (h : ℝ) : (fwdDiff h)^[n] R t = (fwdDiff h)^[n] f t - h^n*iteratedDeriv n f t := by
    rw [← fwdDiff_taylor f n t h]
    simp only [fwdDiff_iter_eq_sum_shift, R, smul_sub, Finset.sum_sub_distrib, T]
  have hzero := hs.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have heq : (fun h : ℝ => (fwdDiff h)^[n] R t / h^n) =ᶠ[𝓝[>] (0:ℝ)]
      (fun h : ℝ => (fwdDiff h)^[n] f t / h^n - iteratedDeriv n f t) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [hsub, sub_div, mul_comm (h^n), mul_div_cancel_right₀ _ (pow_ne_zero _ (ne_of_gt hh))]
  exact tendsto_sub_nhds_zero_iff.1 (hzero.congr' heq)

#print axioms tendsto_normalized_fwdDiff

end Nuttall
