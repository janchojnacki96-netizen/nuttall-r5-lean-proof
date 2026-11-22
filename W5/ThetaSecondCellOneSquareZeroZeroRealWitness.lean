import W5.ThetaOneSquareCellQuadraticBridge

/-!
# Exact second-cell n=1 witness: entry (0,0)

For i=j=0, the ORIGINAL first-square polynomial is identically 1.
Thus the genuine n=1 theta coefficient is precisely 1 - x²/4*M₀(x).
We combine Mathlib's existing Gamma monotonicity and the now-verified
two-sided analytic fourth-root estimates. The exact rational result
fits the ORIGINAL 768-bit cell-2 matrix, checked separately already.
No numerical integration, untrusted oracle, sorry, or new axiom.
-/

namespace W5

/-- The original weighted correction polynomial for entry (0,0)
contains only the constant coefficient 1. -/
theorem thetaCorrectionWPolynomial_one_zero_zero
    (x : ℝ) :
    thetaCorrectionWPolynomial x 1 0 (0 : Fin 5) (0 : Fin 5) =
      Polynomial.C 1 := by
  simp [thetaCorrectionWPolynomial]

/-- No interval approximation here: this is the ACTUAL n=1
theta-series coefficient for entry (0,0). -/
theorem thetaAuditedSeriesTerm_one_zero_zero_eq_moment
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) 1 =
      1 - (x^2/4) * thetaAuditedOneWeightedMoment x 0 := by
  simpa [thetaCorrectionWPolynomial_one_zero_zero,
    Polynomial.coeff_one, Polynomial.coeff_C,
    Finset.sum_range_succ] using
      (thetaAuditedSeriesTerm_one_nine_weighted_moments
        x hx hx1 (0 : Fin 5) (0 : Fin 5))

/-- The second cell's n=1 entry (0,0) is enclosed by the exact
rational quadratic-Gamma candidate, pointwise for EVERY real x
in [1/8,177/512]. This is a strictly stronger statement than
the finite arithmetic check that the box fits the stored audit. -/
theorem thetaSecondCellOneSquareZeroZeroQuadraticBox_containsReal
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512) :
    QInterval.ContainsReal
      thetaSecondCellOneSquareZeroZeroQuadraticBox
      (thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) 1) := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
  let M : ℝ := thetaAuditedOneWeightedMoment x 0
  have hmonoLo :=
    thetaAuditedOneWeightedMoment_mono
      ((1:ℝ)/8) x (by norm_num) hax hx1 0
  have hmonoHi :=
    thetaAuditedOneWeightedMoment_mono
      x ((177:ℝ)/512) hx.le hxb (by norm_num) 0
  have hMlo :
      1 + ((1:ℝ)/8)^2/4 -
        (3*((1:ℝ)/8)^4)/16 ≤ M := by
    calc
      _ = (Nat.factorial 0 : ℝ) +
          (((1:ℝ)/8)^2/4) * (Nat.factorial (0+1) : ℝ) -
          (3*((1:ℝ)/8)^4/32) * (Nat.factorial (0+2) : ℝ) := by
            norm_num
      _ ≤ thetaAuditedOneWeightedMoment ((1:ℝ)/8) 0 :=
        thetaAuditedOneWeightedMoment_gamma_lower_quadratic
          ((1:ℝ)/8) (by norm_num) (by norm_num) 0
      _ ≤ M := hmonoLo
  have hMhi :
      M ≤ 1 + ((177:ℝ)/512)^2/4 := by
    calc
      M ≤ thetaAuditedOneWeightedMoment ((177:ℝ)/512) 0 :=
        hmonoHi
      _ ≤ (Nat.factorial 0 : ℝ) +
          (((177:ℝ)/512)^2/4) * (Nat.factorial (0+1) : ℝ) :=
        thetaAuditedOneWeightedMoment_gamma_upper_quarter
          ((177:ℝ)/512) (by norm_num) (by norm_num) 0
      _ = 1 + ((177:ℝ)/512)^2/4 := by norm_num
  have hMnonneg : 0 ≤ M := by
    have hpos : 0 ≤
        1 + ((1:ℝ)/8)^2/4 -
          (3*((1:ℝ)/8)^4)/16 := by norm_num
    exact hpos.trans hMlo
  have hslo : ((1:ℝ)/8)^2/4 ≤ x^2/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hax)
      (add_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/8) hx.le)]
  have hshi : x^2/4 ≤ ((177:ℝ)/512)^2/4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxb)
      (add_nonneg hx.le (by norm_num : (0:ℝ) ≤ (177:ℝ)/512))]
  have hProductLo :
      (((1:ℝ)/8)^2/4) *
          (1 + ((1:ℝ)/8)^2/4 -
            (3*((1:ℝ)/8)^4)/16) ≤
        (x^2/4)*M := by
    calc
      _ ≤ (((1:ℝ)/8)^2/4)*M :=
        mul_le_mul_of_nonneg_left hMlo (by positivity)
      _ ≤ (x^2/4)*M :=
        mul_le_mul_of_nonneg_right hslo hMnonneg
  have hProductHi :
      (x^2/4)*M ≤
        (((177:ℝ)/512)^2/4) *
          (1 + ((177:ℝ)/512)^2/4) := by
    calc
      _ ≤ (((177:ℝ)/512)^2/4)*M :=
        mul_le_mul_of_nonneg_right hshi hMnonneg
      _ ≤ (((177:ℝ)/512)^2/4) *
            (1 + ((177:ℝ)/512)^2/4) :=
        mul_le_mul_of_nonneg_left hMhi (by positivity)
  change
    ((thetaSecondCellOneSquareZeroZeroQuadraticBox.lo : ℝ) ≤
      thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) 1) ∧
    (thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) 1 ≤
      (thetaSecondCellOneSquareZeroZeroQuadraticBox.hi : ℝ))
  rw [thetaAuditedSeriesTerm_one_zero_zero_eq_moment x hx hx1]
  constructor
  · have hBound :
        ((thetaSecondCellOneSquareZeroZeroQuadraticBox.lo : ℚ) : ℝ) =
          1 - (((177:ℝ)/512)^2/4) *
            (1 + ((177:ℝ)/512)^2/4) := by
        norm_num [thetaSecondCellOneSquareZeroZeroQuadraticBox]
    rw [hBound]
    dsimp [M] at hProductHi
    linarith
  · have hBound :
        ((thetaSecondCellOneSquareZeroZeroQuadraticBox.hi : ℚ) : ℝ) =
          1 - (((1:ℝ)/8)^2/4) *
            (1 + ((1:ℝ)/8)^2/4 -
              (3*((1:ℝ)/8)^4)/16) := by
        norm_num [thetaSecondCellOneSquareZeroZeroQuadraticBox]
    rw [hBound]
    dsimp [M] at hProductLo
    linarith

/-- For the complete ORIGINAL cell-2 audited interval, we have
a genuine real-sound enclosure of its n=1 summand, with no
numerical or analytic hypotheses left for this summand. -/
theorem thetaSecondCell_one_zero_zero_fits_audit
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512) :
    QInterval.ContainsReal
      (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5))
      (thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) 1) := by
  have h :=
    thetaSecondCellOneSquareZeroZeroQuadraticBox_containsReal x hax hxb
  have hfits :=
    thetaSecondCellOneSquareZeroZeroQuadraticBox_fits_audit
  exact ⟨le_trans (by exact_mod_cast hfits.1) h.1,
    le_trans h.2 (by exact_mod_cast hfits.2)⟩

end W5
