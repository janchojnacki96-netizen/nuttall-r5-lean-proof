import W5.ThetaSecondCellHeadAbsoluteFactor
import W5.ThetaSecondCellHeadOriginalIntegralComparison
import W5.ThetaSecondCellHeadDoubleBinomialGammaIntegral

/-!
# Real soundness of the original n-th theta head majorant K

Combine three INDEPENDENT reusable arguments rather than proving
25 entries one-by-one:
1. Original signed integral <= positive factorial-polynomial integral.
2. Mathlib's two-factor binomial expansion and actual weighted Gamma
   moments give a finite positive upper bound.
3. Identify that exact expression with the previously native_decide
   checked rational majorant K(a,b,n,i,j).

This is the central genuine analytic inequality needed by the
second-cell two-term LDL reduction, and is intended to generalize
to OTHER rational x-cells without a new per-entry proof.
-/

namespace W5
open MeasureTheory

/-- The exact finite real Gamma correction used by K.
This formula is intentionally the rational checker expression
with only the scalar field changed from Rat to Real. -/
noncomputable def thetaHeadExpandedCorrectionCap
    (b : ℚ) (D p : ℝ) (n : ℕ) (i j : Fin 5) : ℝ :=
  ∑ t ∈ Finset.range (min i.val j.val + 1),
    (1 / ((Nat.factorial t : ℝ) *
      (Nat.factorial (i.val-t) : ℝ) *
      (Nat.factorial (j.val-t) : ℝ))) *
      (∑ s ∈ Finset.range (i.val+j.val-2*t+1),
        ∑ u ∈ Finset.range (t+1),
          ((i.val+j.val-2*t).choose s : ℝ) *
            (t.choose u : ℝ) *
            D^(i.val+j.val-2*t-s) * (b:ℝ)^s *
              p^(t-u) * (b:ℝ)^(2*u) *
                (thetaHeadMomentUpper b n (s+u) : ℝ))

/-- The cap is nonnegative without numerical checks, and this
fact justifies replacing x²/4 by b²/4 in the original correction. -/
theorem thetaHeadExpandedCorrectionCap_nonneg
    (b : ℚ) (D p : ℝ) (n : ℕ) (i j : Fin 5)
    (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ thetaHeadExpandedCorrectionCap b D p n i j := by
  have hmoment (k : ℕ) :
      0 ≤ (thetaHeadMomentUpper b n k : ℝ) := by
    simp only [thetaHeadMomentUpper, Rat.cast_add, Rat.cast_mul,
      Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
    positivity
  unfold thetaHeadExpandedCorrectionCap
  apply Finset.sum_nonneg
  intro t ht
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.sum_nonneg
  intro u hu
  positivity

/-- Integrate the whole positive polynomial by ONE Mathlib finite
sum, then apply PR #138's real Gamma bound to each affine-power
product. No coefficientwise-nonnegative-polynomial machinery needed. -/
theorem thetaHeadPositiveWIntegral_le_expandedCap
    (b : ℚ) (D p x : ℝ) (n : ℕ) (i j : Fin 5)
    (hD : 0 ≤ D) (hp : 0 ≤ p)
    (hx : 0 < x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1) (hn : 0 < n) :
    (∫ w in Set.Ici (0:ℝ),
      (Real.exp (-w) *
        (1+w*(x/(n:ℝ))^2)^((1:ℝ)/4)) *
          (thetaHeadPositiveWPolynomial D p (b:ℝ) i j).eval w
      ∂volume) ≤
        thetaHeadExpandedCorrectionCap b D p n i j := by
  let y : ℝ := x/(n:ℝ)
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)
  let c : ℕ → ℝ := fun t =>
    1 / ((Nat.factorial t : ℝ) *
      (Nat.factorial (i.val-t) : ℝ) *
      (Nat.factorial (j.val-t) : ℝ))
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have h : 1 ≤ n := by omega
    exact_mod_cast h
  have hy : 0 < y := div_pos hx hnR
  have hy1 : y ≤ 1 := by
    dsimp [y]
    apply (div_le_iff₀ hnR).2
    linarith
  have hfunc (w : ℝ) :
      W w * (thetaHeadPositiveWPolynomial D p (b:ℝ) i j).eval w =
        ∑ t ∈ Finset.range (min i.val j.val + 1),
          c t * (W w *
            ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
              (p+w*(b:ℝ)^2)^t)) := by
    rw [thetaHeadPositiveWPolynomial_eval]
    unfold thetaCoefficientPositivePolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [c]
    ring
  have hterm (t : ℕ) :
      IntegrableOn (fun w : ℝ =>
        W w * ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
          (p+w*(b:ℝ)^2)^t))
        (Set.Ici (0:ℝ)) volume := by
    let P : Polynomial ℝ :=
      (Polynomial.C D + Polynomial.C (b:ℝ) * Polynomial.X) ^
          (i.val+j.val-2*t) *
      (Polynomial.C p + Polynomial.C ((b:ℝ)^2) * Polynomial.X)^t
    have hP := thetaHeadWeightedPolynomial_integrableOn y hy hy1 P
    have heq :
        (fun w : ℝ =>
          W w * ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
            (p+w*(b:ℝ)^2)^t)) =
        (fun w : ℝ => W w * P.eval w) := by
      funext w
      dsimp [P]
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      ring
    rw [heq]
    exact hP
  have hIntegrable :
      ∀ t ∈ Finset.range (min i.val j.val + 1),
      IntegrableOn (fun w : ℝ =>
        c t * (W w *
          ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
            (p+w*(b:ℝ)^2)^t)))
        (Set.Ici (0:ℝ)) volume :=
    fun t _ => (hterm t).const_mul (c t)
  have hIntegral :
      (∫ w in Set.Ici (0:ℝ),
        W w * (thetaHeadPositiveWPolynomial D p (b:ℝ) i j).eval w
        ∂volume) =
      ∑ t ∈ Finset.range (min i.val j.val + 1),
        c t * (∫ w in Set.Ici (0:ℝ),
          W w * ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
            (p+w*(b:ℝ)^2)^t) ∂volume) := by
    calc
      _ = ∫ w in Set.Ici (0:ℝ),
          ∑ t ∈ Finset.range (min i.val j.val + 1),
            c t * (W w *
              ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
                (p+w*(b:ℝ)^2)^t)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with w
          exact hfunc w
      _ = ∑ t ∈ Finset.range (min i.val j.val + 1),
            (∫ w in Set.Ici (0:ℝ),
              c t * (W w *
                ((D+w*(b:ℝ))^(i.val+j.val-2*t) *
                  (p+w*(b:ℝ)^2)^t)) ∂volume) := by
          exact integral_finsetSum _ hIntegrable
      _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [integral_const_mul]
  rw [hIntegral]
  unfold thetaHeadExpandedCorrectionCap
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_left
    (thetaHead_affine_product_integral_le_double_binomial_caps
      b x D p n (i.val+j.val-2*t) t
      hx hxb hb hn hD hp)
    (by positivity)

/-- Exact real cast of the already checked rational K. This is
only a finite sum/rational-field identity and uses no analysis. -/
theorem thetaHeadPositiveMajorant_cast_eq_expandedCap
    (a b : ℚ) (n : ℕ) (i j : Fin 5) :
    (thetaHeadPositiveMajorant a b n i j : ℝ) =
      (n:ℝ)^2 *
        thetaCoefficientPositivePolynomial i j
          (((n:ℝ)^2-1)/(a:ℝ)) ((n:ℝ)^2) +
      ((b:ℝ)^2/4) *
        thetaHeadExpandedCorrectionCap b
          (((n:ℝ)^2-1)/(a:ℝ)) ((n:ℝ)^2) n i j := by
  unfold thetaHeadPositiveMajorant thetaHeadExpandedCorrectionCap
    thetaHeadPositiveIntegralTerm thetaCoefficientPositivePolynomial
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_sum,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
  ring

/-- Central semantic inequality: the ACTUAL original n-th theta
series term is bounded by the SAME computable rational majorant K
already checked by native_decide, simultaneously for all 25 entries. -/
theorem thetaHead_originalSeriesTerm_abs_le_rationalK
    (a b : ℚ) (x : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (i j : Fin 5)
    (ha : (0:ℝ) < (a:ℝ))
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1) :
    |thetaAuditedSeriesTerm x i j n| ≤
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        (thetaHeadPositiveMajorant a b n i j : ℝ) := by
  let p : ℝ := (n:ℝ)^2
  let D : ℝ := (p-1)/(a:ℝ)
  let C : ℝ := thetaHeadExpandedCorrectionCap b D p n i j
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpn : (1:ℝ) ≤ p := by
    dsimp [p]
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hp : 0 ≤ p := le_trans (by norm_num) hpn
  have hD : 0 ≤ D := by
    dsimp [D]
    exact div_nonneg (by linarith) ha.le
  have hx : 0 < x := ha.trans_le hax
  have hB :
      |coefficientPolynomial i j (((n:ℝ)^2-1)/x) ((n:ℝ)^2)| ≤
      thetaCoefficientPositivePolynomial i j D p := by
    dsimp [D, p]
    exact thetaAuditedBasePolynomial_abs_le_positive_at_cell
      (a:ℝ) (b:ℝ) x ha hax hxb n hn i j
  have hI :
      |∫ w in Set.Ici (0:ℝ),
         Real.exp (-w) *
           (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4) *
           coefficientPolynomial i j
             ((((n:ℝ)^2-1)/x)+w*x) (((n:ℝ)^2)+w*x^2)
         ∂volume| ≤ C := by
    calc
      _ ≤ ∫ w in Set.Ici (0:ℝ),
        (Real.exp (-w) *
          (1+w*(x/(n:ℝ))^2)^((1:ℝ)/4)) *
        (thetaHeadPositiveWPolynomial D p (b:ℝ) i j).eval w
        ∂volume := by
          dsimp [D, p]
          exact thetaHeadOriginalIntegral_abs_le_positiveIntegral
            a b x n hn i j ha hax hxb hb
      _ ≤ C := thetaHeadPositiveWIntegral_le_expandedCap
        b D p x n i j hD hp hx hxb hb (by omega)
  have hC : 0 ≤ C :=
    thetaHeadExpandedCorrectionCap_nonneg b D p n i j hD hp
  have hsq : x^2 ≤ (b:ℝ)^2 := by
    have hbpos : 0 ≤ (b:ℝ) + x := by linarith
    have hproduct : 0 ≤ ((b:ℝ)-x)*((b:ℝ)+x) :=
      mul_nonneg (sub_nonneg.mpr hxb) hbpos
    nlinarith
  have hscale : x^2/4 ≤ (b:ℝ)^2/4 := by linarith
  have hTerm :=
    thetaAuditedSeriesTerm_abs_le_of_base_integral
      x i j n (by omega)
      (thetaCoefficientPositivePolynomial i j D p) C hB hI
  have hK : (thetaHeadPositiveMajorant a b n i j : ℝ) =
      p * thetaCoefficientPositivePolynomial i j D p +
        ((b:ℝ)^2/4)*C := by
    dsimp [D, p, C]
    exact thetaHeadPositiveMajorant_cast_eq_expandedCap a b n i j
  calc
    |thetaAuditedSeriesTerm x i j n| ≤
        Real.exp (-((n:ℝ)^2-1)/x^2) *
          (p * thetaCoefficientPositivePolynomial i j D p +
            (x^2/4)*C) := hTerm
    _ ≤ Real.exp (-((n:ℝ)^2-1)/x^2) *
          (p * thetaCoefficientPositivePolynomial i j D p +
            ((b:ℝ)^2/4)*C) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      have hmult := mul_le_mul_of_nonneg_right hscale hC
      linarith
    _ = Real.exp (-((n:ℝ)^2-1)/x^2) *
          (thetaHeadPositiveMajorant a b n i j : ℝ) := by
      rw [hK]

end W5
