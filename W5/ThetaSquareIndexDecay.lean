import W5.ThetaGaussianNeighborhoodEnvelope
import W5.ThetaGaussianSummability

/-!
# Retaining Gaussian square-index decay after local differentiation

The |u|,|v| <= 1 envelope suffices for each fixed index, but its
crude exponential prefactor can grow too quickly with p=n^2 to
prove summability over n. In the smaller box |u|,|v| <= x/8,
the exponent grows at most by (p-1)/4 + p*x²/64.

For 0<x<=1 and p>=1, the original theta prefactor
exp(-(p-1)/x²) absorbs this growth, leaving Gaussian decay
exp(-47*p/64) up to the constant exp(3/4).

These are exact pointwise inequalities and summability statements,
NOT yet a derivative-under-infinite-sum theorem.
-/

namespace W5

/-- A radius-sensitive bound for the exponential prefactor.
Unlike the fixed unit-ball bound, it retains the smallness of
the local parameter radius. -/
theorem thetaGaussian_base_exponent_radius
    (δ p d0 u v : ℝ)
    (hδ : 0 ≤ δ)
    (hu : |u| ≤ δ) (hv : |v| ≤ δ) :
    Real.exp (-d0*(u+v)-p*u*v) ≤
      Real.exp (2*δ*|d0| + δ^2*|p|) := by
  have hsum : |u+v| ≤ 2*δ := by
    calc
      |u+v| ≤ |u|+|v| := abs_add_le _ _
      _ ≤ 2*δ := by linarith
  have hprod : |u*v| ≤ δ^2 := by
    rw [abs_mul]
    calc
      |u|*|v| ≤ δ*δ := mul_le_mul hu hv (abs_nonneg _) hδ
      _ = δ^2 := by ring
  have hd : -d0*(u+v) ≤ 2*δ*|d0| := by
    calc
      -d0*(u+v) = -(d0*(u+v)) := by ring
      _ ≤ |d0*(u+v)| := neg_le_abs _
      _ = |d0|*|u+v| := by rw [abs_mul]
      _ ≤ |d0|*(2*δ) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = 2*δ*|d0| := by ring
  have hp : -p*u*v ≤ δ^2*|p| := by
    calc
      -p*u*v = -(p*(u*v)) := by ring
      _ ≤ |p*(u*v)| := neg_le_abs _
      _ = |p|*|u*v| := by rw [abs_mul]
      _ ≤ |p|*δ^2 := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = δ^2*|p| := by ring
  apply Real.exp_le_exp.mpr
  linarith

/-- Specialization to p>=1 and the theta scale d0=(p-1)/x. -/
theorem thetaGaussian_base_exponent_small_box
    (x p u v : ℝ)
    (hx : 0 < x) (hp : 1 ≤ p)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-((p-1)/x)*(u+v)-p*u*v) ≤
      Real.exp ((p-1)/4+p*x^2/64) := by
  have hδ : 0 ≤ x/8 := by positivity
  have hbase := thetaGaussian_base_exponent_radius
    (x/8) p ((p-1)/x) u v hδ hu hv
  have hd0 : 0 ≤ (p-1)/x := div_nonneg (by linarith) hx.le
  have hp0 : 0 ≤ p := by linarith
  have heq :
      2*(x/8)*|(p-1)/x|+(x/8)^2*|p| =
        (p-1)/4+p*x^2/64 := by
    rw [abs_of_nonneg hd0, abs_of_nonneg hp0]
    field_simp [ne_of_gt hx]
    ring
  simpa only [heq] using hbase

/-- The actual theta outer Gaussian survives the losses from the
small parameter box, uniformly for all p>=1 and 0<x<=1. -/
theorem thetaGaussian_outer_prefactor_decay
    (x p : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p) :
    Real.exp (-(p-1)/x^2) *
        Real.exp ((p-1)/4+p*x^2/64) ≤
      Real.exp (3/4) * Real.exp (-((47:ℝ)/64)*p) := by
  have hsq : 0 < x^2 := by positivity
  have hxle : x^2 ≤ 1 := by nlinarith
  have hpp : 0 ≤ p-1 := by linarith
  have hdiv : p-1 ≤ (p-1)/x^2 := by
    apply (le_div_iff₀ hsq).2
    nlinarith [mul_nonneg hpp (by linarith : 0 ≤ 1-x^2)]
  have hterm : p*x^2 ≤ p := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ p)
      (by linarith : 0 ≤ 1-x^2)]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [hdiv, hterm]

/-- The resulting square-index Gaussian is summable. -/
theorem thetaGaussian_surviving_square_decay_summable :
    Summable (fun n : ℕ =>
      Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) := by
  have h := theta_gaussian_polynomial_summable
    0 ((47:ℝ)/64) (by norm_num)
  simpa only [pow_zero, one_mul] using h


/-- The Gaussian weight from an individual theta square survives
uniformly on the shrinking parameter box.  In particular the
estimate already includes the outer factor `exp (-(p-1)/x²)`,
which is needed when summing over the square index. -/
theorem thetaGaussian_small_box_weighted_decay
    (x p u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hp : 1 ≤ p)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Real.exp (-(p-1)/x^2) *
      Real.exp (-((p-1)/x)*(u+v)-p*u*v) ≤
      Real.exp (3/4) * Real.exp (-((47:ℝ)/64)*p) := by
  calc
    Real.exp (-(p-1)/x^2) *
        Real.exp (-((p-1)/x)*(u+v)-p*u*v) ≤
      Real.exp (-(p-1)/x^2) *
        Real.exp ((p-1)/4+p*x^2/64) :=
          mul_le_mul_of_nonneg_left
            (thetaGaussian_base_exponent_small_box x p u v hx hp hu hv)
            (Real.exp_nonneg _)
    _ ≤ Real.exp (3/4) * Real.exp (-((47:ℝ)/64)*p) :=
      thetaGaussian_outer_prefactor_decay x p hx hx1 hp


/-- The shrinking parameter box required to retain Gaussian decay
automatically lies in the local positivity patch used by the
integrable first-derivative majorant. -/
theorem thetaGaussian_small_box_inside_local_patch
    (x z : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hz : |z| ≤ x/8) :
    |z| ≤ 1 ∧ -(1:ℝ)/2 ≤ x*z := by
  have hzlow : -x/8 ≤ z := by
    have hneg : -|z| ≤ z := neg_abs_le z
    linarith
  have hprod : 0 ≤ x * (z+x/8) :=
    mul_nonneg hx.le (by linarith)
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (by linarith : 0 ≤ 1-x)]
  constructor
  · exact hz.trans (by linarith)
  · nlinarith [hprod]

end W5
