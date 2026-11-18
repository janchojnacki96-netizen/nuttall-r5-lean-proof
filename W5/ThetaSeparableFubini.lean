import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Exchange of a countable sum and an integral under separable domination

This is a fully general statement with a finite-rank majorant:
‖F n x‖ ≤ a n * b x almost everywhere, where
  a is summable and b is integrable.

It uses Mathlib's dominated-convergence-for-series theorem.
The next step for the theta proof is to apply it to the concrete
theta integrand via ThetaIntegrandMajorant; this generic theorem
does not silently assert that those hypotheses hold.
-/

namespace W5

open MeasureTheory

theorem hasSum_integral_of_separable_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : ℕ → α → ℝ) (a : ℕ → ℝ) (b : α → ℝ)
    (ha : Summable a)
    (hb : Integrable b μ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ n : ℕ, ‖F n x‖ ≤ a n * b x) :
    HasSum (fun n : ℕ => ∫ x, F n x ∂μ)
      (∫ x, ∑' n : ℕ, F n x ∂μ) := by
  have hbound_summable :
      ∀ᵐ x ∂μ, Summable (fun n : ℕ => a n * b x) :=
    Filter.Eventually.of_forall (fun x => ha.mul_right (b x))
  have hbound_integrable :
      Integrable (fun x => ∑' n : ℕ, a n * b x) μ := by
    have heq :
        (fun x => ∑' n : ℕ, a n * b x) =
          (fun x => (∑' n : ℕ, a n) * b x) := by
      funext x
      rw [tsum_mul_right]
    rw [heq]
    exact hb.const_mul _
  have hbound_each (n : ℕ) :
      ∀ᵐ x ∂μ, ‖F n x‖ ≤ a n * b x :=
    hbound.mono (fun x hx => hx n)
  have hlim :
      ∀ᵐ x ∂μ, HasSum (fun n : ℕ => F n x)
        (∑' n : ℕ, F n x) := by
    filter_upwards [hbound] with x hx
    exact (Summable.of_norm_bounded (ha.mul_right (b x)) hx).hasSum
  exact hasSum_integral_of_dominated_convergence
    (fun n x => a n * b x)
    hF hbound_each hbound_summable hbound_integrable hlim

end W5
