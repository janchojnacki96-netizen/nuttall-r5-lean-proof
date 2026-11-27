import Nuttall.AuxiliaryVandermonde

namespace Nuttall

open scoped BigOperators

/-- The knot associated with theta index `n` in Section 4.1. -/
noncomputable def thetaKnot (n : ℕ) : ℝ := Real.log (n : ℝ) / 2

noncomputable def thetaScale (t : ℝ) : ℝ := Real.pi * Real.exp (4*t)

noncomputable def thetaOrthantWeight (X u : ℝ) : ℝ := Real.exp (5*u-X*Real.exp (4*u))

theorem thetaKnot_lt_iff (n : ℕ) (hn : 0 < n) (u : ℝ) :
    thetaKnot n < u ↔ (n : ℝ) < Real.exp (2*u) := by
  unfold thetaKnot
  rw [div_lt_iff₀ (by norm_num : 0 < (2 : ℝ)), mul_comm u 2,
    Real.log_lt_iff_lt_exp (by exact_mod_cast hn)]

theorem exp_thetaKnot (n : ℕ) (hn : 0 < n) :
    Real.exp (thetaKnot n) = Real.sqrt (n : ℝ) := by
  rw [thetaKnot, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  congr 1
  ring

theorem auxiliaryCoordinate_shift (n : ℕ) (hn : 0 < n) (t s : ℝ) :
    auxiliaryCoordinate n (t+s) = thetaScale t * Real.exp (4*(s+thetaKnot n)) := by
  have hlog : Real.exp (Real.log (n : ℝ)) = n := Real.exp_log (by exact_mod_cast hn)
  have hk : Real.exp (4 * thetaKnot n) = (n : ℝ)^2 := by
    rw [show 4 * thetaKnot n = Real.log (n : ℝ) + Real.log (n : ℝ) by
      unfold thetaKnot; ring, Real.exp_add, hlog, pow_two]
  rw [auxiliaryCoordinate, thetaScale, show 4*(t+s) = 4*t + 4*s by ring,
    show 4*(s+thetaKnot n) = 4*s + 4*thetaKnot n by ring, Real.exp_add, Real.exp_add, hk]
  ring

theorem auxiliarySummand_shift (n : ℕ) (hn : 0 < n) (t s : ℝ) :
    auxiliarySummand n (t+s) =
      (thetaScale t * Real.exp t) * thetaOrthantWeight (thetaScale t) (s+thetaKnot n) /
        Real.sqrt (n : ℝ) := by
  have hbase : auxiliarySummand n (t+s) =
      Real.exp (t+s) * auxiliaryCoordinate n (t+s) *
        Real.exp (-auxiliaryCoordinate n (t+s)) := by
    unfold auxiliarySummand auxiliaryCoordinate
    rw [show 5*(t+s) = t+s+4*(t+s) by ring, Real.exp_add]
    ring
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  rw [hbase, auxiliaryCoordinate_shift n hn, thetaOrthantWeight,
    show 5*(s+thetaKnot n)-thetaScale t*Real.exp (4*(s+thetaKnot n)) =
      s + thetaKnot n + 4*(s+thetaKnot n) + -(thetaScale t*Real.exp (4*(s+thetaKnot n))) by ring]
  simp only [Real.exp_add, exp_thetaKnot n hn]
  field_simp
  <;> ring

theorem det_vandermonde_scaled {p : ℕ} (X : ℝ) (v : Fin p → ℝ) :
    (Matrix.vandermonde (fun i => X * v i)).det =
      X^(p*(p-1)/2) * (Matrix.vandermonde v).det := by
  have h : Matrix.vandermonde (fun i => X*v i) =
      Matrix.of (fun (i j : Fin p) => X^j.val * (Matrix.vandermonde v) i j) := by
    ext i j
    simp [Matrix.vandermonde, mul_pow]
  rw [h, Matrix.det_mul_row, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

/-- Evaluate the derivative determinant after shifting each fixed theta index.
The integration domains and sums are handled separately. -/
theorem det_auxiliary_summands_shift {p : ℕ} (n : Fin p → ℕ) (hn : ∀ i, 0 < n i)
    (t : ℝ) (s : Fin p → ℝ) :
    (Matrix.of (fun (i j : Fin p) =>
      auxiliarySummand (n i) (t+s i) *
        (auxiliaryDerivativePolynomial j.val).eval (auxiliaryCoordinate (n i) (t+s i)))).det =
      (thetaScale t * Real.exp t)^p *
      (4 * thetaScale t)^(p*(p-1)/2) *
      (Matrix.vandermonde (fun i => Real.exp (4*(s i+thetaKnot (n i))))).det *
      ∏ i : Fin p, thetaOrthantWeight (thetaScale t) (s i+thetaKnot (n i)) /
        Real.sqrt (n i : ℝ) := by
  rw [det_auxiliary_weighted_summands]
  simp_rw [auxiliaryCoordinate_shift _ (hn _), auxiliarySummand_shift _ (hn _)]
  rw [det_vandermonde_scaled]
  have hprod : (∏ i : Fin p, thetaScale t * Real.exp t *
      thetaOrthantWeight (thetaScale t) (s i+thetaKnot (n i)) / Real.sqrt (n i : ℝ)) =
      (thetaScale t * Real.exp t)^p *
        ∏ i : Fin p, thetaOrthantWeight (thetaScale t) (s i+thetaKnot (n i)) /
          Real.sqrt (n i : ℝ) := by
    simp only [mul_div_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, mul_pow]
  rw [hprod, Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => i),
    Finset.sum_range_id, mul_pow]
  ring

#print axioms det_auxiliary_summands_shift

end Nuttall
