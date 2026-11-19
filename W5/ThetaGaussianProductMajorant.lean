import W5.ThetaSquareIndexDecay

/-!
# A separable Gaussian majorant for the theta square index and w-integral

This module isolates a product majorant with Gaussian decay in n and
integrable polynomial-exponential decay in w.  Both properties are
proved separately, without postulating a derivative / integral or
derivative / infinite-sum interchange.

IMPORTANT: One must still bound the *actual* differentiated theta
kernel by a suitable constant multiple of this product majorant,
uniformly on an open parameter patch, and justify any desired
interchange theorem.  No Nuttall r=5 sign claim follows here.
-/

namespace W5

open MeasureTheory

/-- An explicit, nonnegative on w >= 0 product of a quadratic
square-index Gaussian and an integrable w-envelope. -/
noncomputable def thetaGaussianProductMajorant (n : ℕ) (w : ℝ) : ℝ :=
  (((n:ℝ)^2 + 1) * Real.exp (-((47:ℝ)/64) * (n:ℝ)^2)) *
    ((w^2 + w + 1) * Real.exp (-((1:ℝ)/4) * w))

/-- Summability of the n-factor including its quadratic loss. -/
theorem thetaGaussianProductMajorant_index_factor_summable :
    Summable (fun n : ℕ =>
      ((n:ℝ)^2 + 1) * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) := by
  have h2 : Summable (fun n : ℕ =>
      (n:ℝ)^2 * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) :=
    theta_gaussian_polynomial_summable 2 ((47:ℝ)/64) (by norm_num)
  have h0 : Summable (fun n : ℕ =>
      Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) :=
    thetaGaussian_surviving_square_decay_summable
  have heq :
      (fun n : ℕ => ((n:ℝ)^2 + 1) *
        Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) =
      (fun n : ℕ =>
        (n:ℝ)^2 * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2) +
        Real.exp (-((47:ℝ)/64)*(n:ℝ)^2)) := by
    funext n
    ring
  rw [heq]
  exact h2.add h0

/-- For every fixed real w, the product majorant is summable over
the full natural-number square index. -/
theorem thetaGaussianProductMajorant_summable (w : ℝ) :
    Summable (fun n : ℕ => thetaGaussianProductMajorant n w) := by
  have heq :
      (fun n : ℕ => thetaGaussianProductMajorant n w) =
      (fun n : ℕ =>
        ((w^2 + w + 1) * Real.exp (-((1:ℝ)/4)*w)) *
        (((n:ℝ)^2 + 1) *
          Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))) := by
    funext n
    unfold thetaGaussianProductMajorant
    ring
  rw [heq]
  exact thetaGaussianProductMajorant_index_factor_summable.mul_left
    ((w^2 + w + 1) * Real.exp (-((1:ℝ)/4)*w))

/-- For each fixed index, the product majorant is integrable on
the positive w half-line. -/
theorem thetaGaussianProductMajorant_integrableOn (n : ℕ) :
    IntegrableOn
      (fun w : ℝ => thetaGaussianProductMajorant n w)
      (Set.Ioi (0:ℝ)) volume := by
  have hw : IntegrableOn
      (fun w : ℝ => (w^2 + w + 1) *
        Real.exp (-((1:ℝ)/4)*w))
      (Set.Ioi (0:ℝ)) volume := by
    simpa only [one_mul] using
      (thetaGaussian_quadratic_exp_integrable (1:ℝ) 1 1)
  have h := hw.const_mul
    (((n:ℝ)^2 + 1) * Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))
  change Integrable
    (fun w : ℝ => thetaGaussianProductMajorant n w)
    (volume.restrict (Set.Ioi (0:ℝ)))
  simpa only [thetaGaussianProductMajorant] using h


/-- The integrals of this explicit separable majorant are also
summable over the square index.  This is a stronger summability fact
than pointwise-in-w summability, but it does not establish a bound
for the actual differentiated theta kernel. -/
theorem thetaGaussianProductMajorant_integrals_summable :
    Summable (fun n : ℕ =>
      ∫ w : ℝ, thetaGaussianProductMajorant n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  let c : ℝ := ∫ w : ℝ,
    (w^2+w+1) * Real.exp (-((1:ℝ)/4)*w)
      ∂(volume.restrict (Set.Ioi (0:ℝ)))
  have heq :
      (fun n : ℕ =>
        ∫ w : ℝ, thetaGaussianProductMajorant n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) =
      (fun n : ℕ =>
        c * (((n:ℝ)^2+1) *
          Real.exp (-((47:ℝ)/64)*(n:ℝ)^2))) := by
    funext n
    simp only [thetaGaussianProductMajorant, integral_const_mul]
    dsimp [c]
    ring
  rw [heq]
  exact thetaGaussianProductMajorant_index_factor_summable.mul_left c

end W5
