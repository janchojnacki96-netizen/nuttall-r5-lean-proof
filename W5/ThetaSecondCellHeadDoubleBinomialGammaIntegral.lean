import W5.ThetaSecondCellHeadDoubleBinomial
import W5.ThetaSecondCellHeadMomentReuse
import W5.ThetaAllSquareIndexNineMoments

/-!
# Exact weighted integration of the double binomial theta envelope

Use the prior TWO-affine-factor Mathlib binomial identity to integrate
the positive original correction polynomial by finite linearity.
This directly produces the binomial/Gamma moment structure appearing
in the exact rational K bound. Coefficientwise positivity of a
Mathlib Polynomial is not required: every term's sign is manifest.

No fresh improper integral or infinite Fubini theorem is proved.
-/

namespace W5
open MeasureTheory

/-- Exactly integrate any two affine powers against the ORIGINAL
quarter-Gamma measure, using the existing integrable moments. -/
theorem thetaHead_affine_product_weighted_integral_double_binomial
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (D p b : ℝ) (m t : ℕ) :
    (∫ w in Set.Ici (0:ℝ),
      (Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)) *
        ((D+w*b)^m * (p+w*b^2)^t) ∂volume) =
      ∑ s ∈ Finset.range (m+1),
        ∑ u ∈ Finset.range (t+1),
          ((m.choose s : ℝ) * (t.choose u : ℝ) *
            D^(m-s) * b^s * p^(t-u) * b^(2*u)) *
              thetaAuditedOneWeightedMoment y (s+u) := by
  classical
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)
  let C : ℕ → ℕ → ℝ := fun s u =>
    (m.choose s : ℝ) * (t.choose u : ℝ) *
      D^(m-s) * b^s * p^(t-u) * b^(2*u)
  have hexpand (w : ℝ) :
      W w * ((D+w*b)^m * (p+w*b^2)^t) =
        ∑ s ∈ Finset.range (m+1),
          ∑ u ∈ Finset.range (t+1),
            C s u * (W w * w^(s+u)) := by
    rw [thetaHead_affine_product_double_binomial]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [C]
    ring
  calc
    (∫ w in Set.Ici (0:ℝ),
      W w * ((D+w*b)^m * (p+w*b^2)^t) ∂volume) =
      ∫ w in Set.Ici (0:ℝ),
        ∑ s ∈ Finset.range (m+1),
          ∑ u ∈ Finset.range (t+1),
            C s u * (W w * w^(s+u)) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with w
      exact hexpand w
    _ = ∑ s ∈ Finset.range (m+1),
          (∫ w in Set.Ici (0:ℝ),
            ∑ u ∈ Finset.range (t+1),
              C s u * (W w * w^(s+u)) ∂volume) := by
      exact integral_finsetSum (Finset.range (m+1))
        (fun s _ =>
          integrable_finsetSum (Finset.range (t+1))
            (fun u _ =>
              (thetaAuditedOneWeightedMoment_integrable
                y hy hy1 (s+u)).const_mul (C s u)))
    _ = ∑ s ∈ Finset.range (m+1),
          ∑ u ∈ Finset.range (t+1),
            (∫ w in Set.Ici (0:ℝ),
              C s u * (W w * w^(s+u)) ∂volume) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact integral_finsetSum (Finset.range (t+1))
        (fun u _ =>
          (thetaAuditedOneWeightedMoment_integrable
            y hy hy1 (s+u)).const_mul (C s u))
    _ = ∑ s ∈ Finset.range (m+1),
          ∑ u ∈ Finset.range (t+1),
            C s u * thetaAuditedOneWeightedMoment y (s+u) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      rw [integral_const_mul]
      rfl

/-- Replace each genuine Gamma moment with its previously proved
rational quarter-Gamma upper endpoint. The entire double binomial
sum is positive termwise for D,p,b >=0, so no interval multiplication
or additional polynomial theorem is required. -/
theorem thetaHead_affine_product_integral_le_double_binomial_caps
    (b : ℚ) (x D p : ℝ) (n m t : ℕ)
    (hx : 0 < x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1) (hn : 0 < n)
    (hD : 0 ≤ D) (hp : 0 ≤ p) :
    (∫ w in Set.Ici (0:ℝ),
      (Real.exp (-w) *
        (1+w*(x/(n:ℝ))^2)^((1:ℝ)/4)) *
        ((D+w*(b:ℝ))^m * (p+w*(b:ℝ)^2)^t)
      ∂volume) ≤
      ∑ s ∈ Finset.range (m+1),
        ∑ u ∈ Finset.range (t+1),
          ((m.choose s : ℝ) * (t.choose u : ℝ) *
            D^(m-s) * (b:ℝ)^s * p^(t-u) *
              (b:ℝ)^(2*u)) *
            (thetaHeadMomentUpper b n (s+u) : ℝ) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have h : 1 ≤ n := by omega
    exact_mod_cast h
  have hy : 0 < x/(n:ℝ) := div_pos hx hnR
  have hy1 : x/(n:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    linarith
  have hb0 : (0:ℝ) ≤ (b:ℝ) := hx.le.trans hxb
  rw [thetaHead_affine_product_weighted_integral_double_binomial
    (x/(n:ℝ)) hy hy1 D p (b:ℝ) m t]
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro u hu
  exact mul_le_mul_of_nonneg_left
    (thetaHeadMomentUpper_real_sound b x hx.le hxb hb n (s+u) hn)
    (by positivity)

end W5
