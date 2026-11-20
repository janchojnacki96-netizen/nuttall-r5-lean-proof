import W5.ThetaGammaAffineGaussianIntegrand
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Mathlib measure-theoretic affine substitution on the positive half-line

The remaining original gamma-to-certificate bridge needs exactly
z = 1 + (x²/p) w, carrying w>0 to z>1.

Rather than prove another change-of-variables theorem from scratch,
we specialize Mathlib's
`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`:
an increasing affine map has derivative c>0 and sends Ioi 0 onto
Ioi a. Mathlib then handles Lebesgue measure and the Jacobian.

The resulting gamma integral identity is unconditional under
x>0 and p>0; no integrability is assumed or postulated.
It can subsequently be combined with the already verified
pointwise identity `theta_gamma_affine_weighted_gaussian_exact`.
-/

namespace W5
open MeasureTheory

/-- A reusable Lebesgue integral change of variables
for the affine map w ↦ a+c*w between two half-lines.
Reuses Mathlib's generic image/derivative integral theorem. -/
theorem theta_integral_affine_Ioi
    (g : ℝ → ℝ) (a c : ℝ) (hc : 0 < c) :
    (∫ w in Set.Ioi (0:ℝ), c * g (a+c*w)) =
      ∫ z in Set.Ioi a, g z := by
  let f : ℝ → ℝ := fun w => a+c*w
  have hfderiv (w : ℝ) : HasDerivAt f c w := by
    simpa only [f, id_eq] using
      (((hasDerivAt_id w).const_mul c).const_add a)
  have hderiv (w : ℝ) : deriv f w = c := (hfderiv w).deriv
  have himage : f '' Set.Ioi (0:ℝ) = Set.Ioi a := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change a < a+c*w
      exact lt_add_of_pos_right a (mul_pos hc hw)
    · intro hz
      refine ⟨(z-a)/c, div_pos (sub_pos.mpr hz) hc, ?_⟩
      change a+c*((z-a)/c) = z
      field_simp [hc.ne'] <;> ring
  have hinj : Set.InjOn f (Set.Ioi (0:ℝ)) := by
    intro w _ v _ heq
    dsimp only [f] at heq
    have hmul : c*w = c*v := add_left_cancel heq
    have hzero : c*(w-v) = 0 := by nlinarith [hmul]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hc.ne')
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioi (a := (0:ℝ)))
      (fun w _ => (hfderiv w).hasDerivWithinAt)
      hinj g
  simpa [himage, hderiv, f, abs_of_pos hc] using hchange.symm

/-- Exact original incomplete-gamma change of variables.
The positive Jacobian x²/p emerges directly from Mathlib.
No Taylor expansion, numerical quadrature, or derivative/integral
interchange is involved. -/
theorem theta_gamma_integral_affine_exact
    (x p y : ℝ) (hx : 0 < x) (hp : 0 < p) :
    (∫ z in Set.Ioi (1:ℝ),
        z^((1:ℝ)/4) * Real.exp (-p*y*z)) =
      (x^2/p) *
        (∫ w in Set.Ioi (0:ℝ),
          (1+(x^2/p)*w)^((1:ℝ)/4) *
            Real.exp (-p*y*(1+(x^2/p)*w))) := by
  have hc : 0 < x^2/p := by positivity
  have h := theta_integral_affine_Ioi
    (fun z : ℝ => z^((1:ℝ)/4) * Real.exp (-p*y*z))
    1 (x^2/p) hc
  rw [integral_const_mul] at h
  exact h.symm

end W5
