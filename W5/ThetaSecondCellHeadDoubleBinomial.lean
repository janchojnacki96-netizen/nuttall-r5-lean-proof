import W5.ThetaSecondCellHeadPositiveWPolynomial
import W5.ThetaSecondCellHeadFiniteMajorants

/-!
# The exact double-binomial expansion behind the n=2,3 K majorants

Expand only the TWO affine factors of the already-defined exact
positive factorial envelope. Mathlib's `add_pow` and
`Finset.sum_mul_sum` provide all combinatorics; no hand-written
cases for the 25 entries or bespoke binomial theorem are needed.

Together with the existing weighted-polynomial integral identity
and sound Gamma moment bounds, this finite identity is the
remaining algebraic bridge to the already native_decide-checked
rational K caps on the second x-cell.
-/

namespace W5

/-- Exact two-factor binomial identity, uniform in both degrees.
All coefficients here are the ORIGINAL Mathlib Nat.choose values. -/
theorem thetaHead_affine_product_double_binomial
    (D p b w : ℝ) (m t : ℕ) :
    (D+w*b)^m * (p+w*b^2)^t =
      ∑ s ∈ Finset.range (m+1),
        ∑ u ∈ Finset.range (t+1),
          (m.choose s : ℝ) * (t.choose u : ℝ) *
            D^(m-s) * b^s * p^(t-u) * b^(2*u) *
              w^(s+u) := by
  calc
    (D+w*b)^m * (p+w*b^2)^t =
        (w*b+D)^m * (w*b^2+p)^t := by
      rw [add_comm D (w*b), add_comm p (w*b^2)]
    _ = (∑ s ∈ Finset.range (m+1),
          (w*b)^s * D^(m-s) * (m.choose s : ℝ)) *
        (∑ u ∈ Finset.range (t+1),
          (w*b^2)^u * p^(t-u) * (t.choose u : ℝ)) := by
      rw [add_pow, add_pow]
    _ = _ := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      calc
        ((w*b)^s * D^(m-s) * (m.choose s : ℝ)) *
            ((w*b^2)^u * p^(t-u) * (t.choose u : ℝ)) =
          (m.choose s : ℝ) * (t.choose u : ℝ) *
            D^(m-s) * b^s * p^(t-u) * b^(2*u) *
              (w^s*w^u) := by
          simp only [mul_pow, pow_mul]
          ring
        _ = _ := by rw [← pow_add]

/-- This simultaneously expands all 25 original factorial
envelopes and preserves the exact denominators and binomial
coefficients used by the rational K checker. -/
theorem thetaHeadPositiveWPolynomial_eval_double_binomial
    (D p b w : ℝ) (i j : Fin 5) :
    (thetaHeadPositiveWPolynomial D p b i j).eval w =
      ∑ t ∈ Finset.range (min i.val j.val + 1),
        (1 / ((Nat.factorial t : ℝ) *
          (Nat.factorial (i.val-t) : ℝ) *
          (Nat.factorial (j.val-t) : ℝ))) *
          (∑ s ∈ Finset.range (i.val+j.val-2*t+1),
            ∑ u ∈ Finset.range (t+1),
              ((i.val+j.val-2*t).choose s : ℝ) *
                (t.choose u : ℝ) *
                D^(i.val+j.val-2*t-s) * b^s *
                p^(t-u) * b^(2*u) * w^(s+u)) := by
  rw [thetaHeadPositiveWPolynomial_eval]
  unfold thetaCoefficientPositivePolynomial
  apply Finset.sum_congr rfl
  intro t ht
  calc
    _ = (1 / ((Nat.factorial t : ℝ) *
          (Nat.factorial (i.val-t) : ℝ) *
          (Nat.factorial (j.val-t) : ℝ))) *
          ((D+w*b)^(i.val+j.val-2*t) *
            (p+w*b^2)^t) := by ring
    _ = _ := by rw [thetaHead_affine_product_double_binomial]

end W5
