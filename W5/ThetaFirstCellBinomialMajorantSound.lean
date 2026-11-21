import W5.ThetaFirstCellComputableCoefficientBound

/-!
# Fully real-sound first-cell theta coefficient bound

Reuses the ORIGINAL theta coefficient binomial identity and the
kernel-checked 225-case rational majorant. The only analytic step
is coefficientwise comparison of nonnegative powers when
0 <= x <= 1/8; Gamma moments, theta tails and signed LDL checking
are already proved in imported files.

This aims to close the TRUE first theta cell, not merely its
numerical surrogate. No sorry, admit, axiom, or numerical oracle.
-/

namespace W5

private theorem thetaCoeffFactorAbs (i j : Fin 5) (t : ℕ) :
    |((-1 : ℝ)^(i.val+j.val-t)) /
      ((Nat.factorial t : ℝ) *
       (Nat.factorial (i.val-t) : ℝ) *
       (Nat.factorial (j.val-t) : ℝ))| =
    1 / ((Nat.factorial t : ℝ) *
         (Nat.factorial (i.val-t) : ℝ) *
         (Nat.factorial (j.val-t) : ℝ)) := by
  have hden : 0 ≤ ((Nat.factorial t : ℝ) *
      (Nat.factorial (i.val-t) : ℝ) *
      (Nat.factorial (j.val-t) : ℝ)) := by positivity
  simp [abs_div, abs_pow, abs_of_nonneg hden]

/-- A single original binomial summand is bounded by an exact rational
quantity, uniformly in the first x-cell. -/
private theorem thetaBinomialTermAbsolute_le_majorant
    (x : ℝ) (hx : 0 ≤ x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) (t k : ℕ) :
    |(((-1 : ℝ)^(i.val+j.val-t)) /
       ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) *
      (if i.val+j.val-2*t ≤ k then
        x^(i.val+j.val-2*t) *
          ((t.choose (k-(i.val+j.val-2*t)) : ℝ) *
            (x^2)^(k-(i.val+j.val-2*t)))
       else 0)| ≤
      ((if i.val+j.val-2*t ≤ k ∧ k-(i.val+j.val-2*t) ≤ t then
        ((t.choose (k-(i.val+j.val-2*t)) : ℚ) /
          ((Nat.factorial t : ℚ) *
           (Nat.factorial (i.val-t) : ℚ) *
           (Nat.factorial (j.val-t) : ℚ))) *
           (1/8 : ℚ)^(i.val+j.val-2*t) *
           (1/64 : ℚ)^(k-(i.val+j.val-2*t))
       else 0) : ℝ) := by
  let m := i.val+j.val-2*t
  let u := k-m
  have hx2 : x^2 ≤ (1 : ℝ)/64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxB)
      (add_nonneg hx (by norm_num : (0 : ℝ) ≤ 1/8))]
  have hc := thetaCoeffFactorAbs i j t
  by_cases hm : m ≤ k
  · by_cases hu : u ≤ t
    · have hreal :
        |(((-1 : ℝ)^(i.val+j.val-t)) /
            ((Nat.factorial t : ℝ) *
             (Nat.factorial (i.val-t) : ℝ) *
             (Nat.factorial (j.val-t) : ℝ))) *
          (x^m * ((t.choose u : ℝ) * (x^2)^u))| ≤
            ((t.choose u : ℝ) /
              ((Nat.factorial t : ℝ) *
               (Nat.factorial (i.val-t) : ℝ) *
               (Nat.factorial (j.val-t) : ℝ))) *
               (1/8 : ℝ)^m * (1/64 : ℝ)^u := by
        have hpow : x^m ≤ (1/8 : ℝ)^m :=
          pow_le_pow_left₀ hx hxB _
        have hpow2 : (x^2)^u ≤ (1/64 : ℝ)^u :=
          pow_le_pow_left₀ (sq_nonneg x) hx2 _
        have hsub :
            x^m * ((t.choose u : ℝ) * (x^2)^u) ≤
              (1/8 : ℝ)^m * ((t.choose u : ℝ) * (1/64 : ℝ)^u) := by
          apply mul_le_mul hpow
            (mul_le_mul_of_nonneg_left hpow2 (by positivity))
            (by positivity) (by positivity)
        have hnonneg :
            0 ≤ x^m * ((t.choose u : ℝ) * (x^2)^u) := by
          positivity
        rw [abs_mul, hc, abs_of_nonneg hnonneg]
        calc
          _ ≤ (1 / ((Nat.factorial t : ℝ) *
                   (Nat.factorial (i.val-t) : ℝ) *
                   (Nat.factorial (j.val-t) : ℝ))) *
                ((1/8 : ℝ)^m * ((t.choose u : ℝ) * (1/64 : ℝ)^u)) :=
            mul_le_mul_of_nonneg_left hsub (by positivity)
          _ = _ := by ring
      have hm' : i.val+j.val-2*t ≤ k := by
        simpa [m] using hm
      have hmu : i.val+j.val-2*t ≤ k ∧
          k-(i.val+j.val-2*t) ≤ t := by
        constructor
        · exact hm'
        · simpa [u, m] using hu
      dsimp [m, u] at hreal
      simpa only [if_pos hm', if_pos hmu,
        Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
        Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hreal
    · have hcho : t.choose u = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp [m, u, hm, hu, hcho]
  · simp [m, u, hm]

/-- The ORIGINAL theta coefficients obey their computable
exact-rational majorants, for every index and the whole cell. -/
theorem thetaFirstCellBinomialMajorant_sound
    (x : ℝ) (hx : 0 ≤ x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) (k : ℕ) :
    |(thetaCorrectionWPolynomial x 1 0 i j).coeff k| ≤
      (thetaFirstCellBinomialMajorant i j k : ℝ) := by
  rw [thetaFirstCell_original_coeff_binomial]
  calc
    |∑ t ∈ Finset.range (min i.val j.val + 1),
      (((-1 : ℝ)^(i.val+j.val-t)) /
        ((Nat.factorial t : ℝ) *
         (Nat.factorial (i.val-t) : ℝ) *
         (Nat.factorial (j.val-t) : ℝ))) *
      (if i.val+j.val-2*t ≤ k then
        x^(i.val+j.val-2*t) *
          ((t.choose (k-(i.val+j.val-2*t)) : ℝ) *
            (x^2)^(k-(i.val+j.val-2*t)))
       else 0)| ≤
      ∑ t ∈ Finset.range (min i.val j.val + 1),
        |(((-1 : ℝ)^(i.val+j.val-t)) /
           ((Nat.factorial t : ℝ) *
            (Nat.factorial (i.val-t) : ℝ) *
            (Nat.factorial (j.val-t) : ℝ))) *
          (if i.val+j.val-2*t ≤ k then
            x^(i.val+j.val-2*t) *
              ((t.choose (k-(i.val+j.val-2*t)) : ℝ) *
                (x^2)^(k-(i.val+j.val-2*t)))
           else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range (min i.val j.val + 1),
         (((if i.val+j.val-2*t ≤ k ∧
                     k-(i.val+j.val-2*t) ≤ t then
            ((t.choose (k-(i.val+j.val-2*t)) : ℚ) /
              ((Nat.factorial t : ℚ) *
               (Nat.factorial (i.val-t) : ℚ) *
               (Nat.factorial (j.val-t) : ℚ))) *
                (1/8 : ℚ)^(i.val+j.val-2*t) *
                (1/64 : ℚ)^(k-(i.val+j.val-2*t))
          else 0) : ℚ) : ℝ) := by
      apply Finset.sum_le_sum
      intro t _
      have ht := thetaBinomialTermAbsolute_le_majorant x hx hxB i j t k
      by_cases h : i.val+j.val-2*t ≤ k ∧
          k-(i.val+j.val-2*t) ≤ t
      · simpa only [if_pos h, Rat.cast_mul, Rat.cast_div,
          Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
          Rat.cast_one] using ht
      · simpa only [if_neg h, Rat.cast_zero] using ht
    _ = (thetaFirstCellBinomialMajorant i j k : ℝ) := by
      simp only [thetaFirstCellBinomialMajorant, Rat.cast_sum]

/-- The finite 225-case rational check and the analytic coefficient
identity combine to REMOVE the last first-cell coefficient premise. -/
theorem thetaFirstCellGammaUniformCoefficientBound_from_majorant :
    ThetaFirstCellGammaUniformCoefficientBound := by
  intro x hx hxB i j k hk
  have hk9 : k < 9 := Finset.mem_range.mp hk
  have hmajorant :=
    thetaFirstCellBinomialMajorant_sound x hx.le hxB i j k
  have hfinite := thetaFirstCellBinomialMajorant_le_box i j ⟨k, hk9⟩
  have hreal : (thetaFirstCellBinomialMajorant i j k : ℝ) ≤
      (4 : ℝ) / (8 : ℝ)^k := by
    have hrat : thetaFirstCellBinomialMajorant i j k ≤
        4 / (8 : ℚ)^k := by
      simpa using hfinite
    have hcast :
        ((thetaFirstCellBinomialMajorant i j k : ℚ) : ℝ) ≤
          ((4 / (8 : ℚ)^k : ℚ) : ℝ) := by
      exact_mod_cast hrat
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hcast
  exact hmajorant.trans hreal

/-- Five alternating Schur signs for the TRUE original theta
matrix at all points of 0<x<=1/8, without numerical premises.
The other 50 cells and Nuttall R5 conclusion remain separate. -/
theorem thetaFirstCellGammaUniform_realPivotSigns_from_binomial
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) :=
  thetaFirstCellGammaUniform_realPivotSigns
    thetaFirstCellGammaUniformCoefficientBound_from_majorant x hx hxB

end W5
