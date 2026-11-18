import W5.Statement

namespace W5
/-- Sign consequence of a Jacobi determinant identity, provided as hypothesis. -/
theorem fifth_positive_iff_curvature
    (w3 w4 dw4 ddw4 w5 : ℝ)
    (hw3 : w3 < 0)
    (hjac : w3 * w5 = w4 * ddw4 - dw4 ^ 2) :
    0 < w5 ↔ w4 * ddw4 < dw4 ^ 2 := by
  constructor
  · intro hw5
    have hprod : w3 * w5 < 0 := mul_neg_of_neg_of_pos hw3 hw5
    rw [hjac] at hprod
    nlinarith
  · intro hcurv
    by_contra hn
    have hnonpos : w5 ≤ 0 := le_of_not_gt hn
    have hprod : 0 ≤ w3 * w5 :=
      mul_nonneg_of_nonpos_of_nonpos (le_of_lt hw3) hnonpos
    rw [hjac] at hprod
    nlinarith

theorem normalized_curvature_negative_iff
    (w4 dw4 ddw4 : ℝ) (hw4 : 0 < w4) :
    (w4 * ddw4 - dw4 ^ 2) / w4 ^ 2 < 0 ↔
      w4 * ddw4 < dw4 ^ 2 := by
  have hs : 0 < w4 ^ 2 := sq_pos_of_pos hw4
  constructor
  · intro h
    have hh := (div_lt_iff₀ hs).mp h
    nlinarith
  · intro h
    apply (div_lt_iff₀ hs).mpr
    nlinarith

theorem order_five_of_curvature_assumptions
    (hW3 : ∀ t : ℝ, 0 ≤ t → W 3 t < 0)
    (hJacobi : ∀ t : ℝ, 0 ≤ t →
      W 3 t * W 5 t =
        W 4 t * deriv (deriv (W 4)) t - (deriv (W 4) t) ^ 2)
    (hCurvature : ∀ t : ℝ, 0 ≤ t →
      W 4 t * deriv (deriv (W 4)) t < (deriv (W 4) t) ^ 2) :
    ∀ t : ℝ, 0 ≤ t → 0 < W 5 t := by
  intro t ht
  exact (fifth_positive_iff_curvature
    (W 3 t) (W 4 t) (deriv (W 4) t)
    (deriv (deriv (W 4)) t) (W 5 t)
    (hW3 t ht) (hJacobi t ht)).mpr (hCurvature t ht)
end W5
