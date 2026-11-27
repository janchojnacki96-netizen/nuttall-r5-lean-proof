import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace Nuttall

open MeasureTheory Set

/-- After the substitution `y = exp(4*u)`, the dominating density is the
ordinary Gamma integrand, with its Jacobian. -/
theorem exp_four_gamma_envelope (m : ℕ) :
    IntegrableOn (fun u : ℝ => 4*Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u))) (Ioi 0) ∧
    (∫ u in Ioi (0:ℝ), 4*Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u))) ≤ m.factorial := by
  let f (x : ℝ) := Real.exp (4*x)
  let g (y : ℝ) := Real.exp (-y)*y^m
  have hf' (x : ℝ) (_ : x ∈ Ioi (0:ℝ)) :
      HasDerivWithinAt f (4*f x) (Ioi 0) x := by
    have h := ((hasDerivAt_id x).const_mul 4).exp
    simpa only [f, id_eq, mul_one, one_mul, mul_comm] using h.hasDerivWithinAt
  have hf : StrictMono f := fun a b hab => Real.exp_lt_exp.2 (by linarith)
  have himage : f '' Ioi 0 = Ioi (1:ℝ) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact Real.one_lt_exp_iff.2 (by have : 0 < x := hx; positivity)
    · intro hy
      have hp : 0 < y := zero_lt_one.trans hy
      refine ⟨Real.log y/4, div_pos (Real.log_pos hy) (by norm_num), ?_⟩
      dsimp [f]
      rw [show 4*(Real.log y/4) = Real.log y by ring, Real.exp_log hp]
  have hfun : (fun x => |4*f x| • g (f x)) =
      fun u : ℝ => 4*Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u)) := by
    funext x
    dsimp [f,g]
    rw [abs_of_nonneg (by positivity), ← Real.exp_nat_mul]
    calc
      _ = 4*(Real.exp (4*x) * Real.exp (-Real.exp (4*x)) * Real.exp (m*(4*x))) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have hg : IntegrableOn g (Ioi 0) := by
    have h := Real.GammaIntegral_convergent (show 0 < (m:ℝ)+1 by positivity)
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using h
  have he : (∫ y in Ioi (0:ℝ), g y) = m.factorial := by
    rw [← Real.Gamma_nat_eq_factorial m, Real.Gamma_eq_integral (by positivity)]
    simp [g, Real.rpow_natCast]
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hf' hf.injective.injOn g
  rw [himage,hfun] at hi
  have hsub : Ioi (1:ℝ) ⊆ Ioi 0 := fun _ hy => mem_Ioi.mpr ((zero_lt_one : (0:ℝ) < 1).trans (mem_Ioi.mp hy))
  refine ⟨hi.1 (hg.mono_set hsub), ?_⟩
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hf' hf.injective.injOn g
  rw [himage,hfun] at hcv
  rw [← hcv, ← he]
  apply setIntegral_mono_set hg _ (Filter.Eventually.of_forall hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg hy.le _)

#print axioms exp_four_gamma_envelope

end Nuttall
