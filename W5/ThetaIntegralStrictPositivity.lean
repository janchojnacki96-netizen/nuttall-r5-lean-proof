import W5.WronskianLowOrder
import W5.ThetaYFubini
import W5.ThetaTermIntegrability
import W5.ThetaDensityClosedForm

/-!
# Strict positivity of the ORIGINAL first Wronskian

For t >= 0 the theta y-kernel is nonnegative term by term, and the
n=1 term has a strictly positive improper integral. By the proved
sum/integral interchange and the original Psi1 change of variables,
the actual integral Psi1(t) is strictly positive.

This closes the first (r=1) sign in MainClaim. It does not prove any
sign for W2,...,W5.
-/

namespace W5

open MeasureTheory

/-- Every nonzero theta y-summand is strictly positive for y >= 3. -/
theorem thetaYIntegrand_pos (n : ℕ) (y : ℝ)
    (hn : n ≠ 0) (hy : 3 ≤ y) :
    0 < thetaYIntegrand n y := by
  have hn1 : 1 ≤ n := by omega
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn1
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  have hprod : (3:ℝ) ≤ (n:ℝ)^2*y := by
    calc
      (3:ℝ) = 1*3 := by ring
      _ ≤ (n:ℝ)^2*y :=
        mul_le_mul hp hy (by norm_num) (by positivity)
  have hgap : 0 < 2*(n:ℝ)^2*y-3 := by nlinarith
  have hp0 : 0 < (n:ℝ)^2 :=
    lt_of_lt_of_le (by norm_num) hp
  have hpow : 0 < y ^ ((1:ℝ)/4) :=
    Real.rpow_pos_of_pos (by linarith) _
  change 0 < (n:ℝ)^2 *
    (y ^ ((1:ℝ)/4) * (2*(n:ℝ)^2*y-3) *
      Real.exp (-(n:ℝ)^2*y))
  exact mul_pos hp0
    (mul_pos (mul_pos hpow hgap) (Real.exp_pos _))

theorem thetaYIntegrand_nonneg (n : ℕ) (y : ℝ) (hy : 3 ≤ y) :
    0 ≤ thetaYIntegrand n y := by
  by_cases hn : n = 0
  · subst n
    simp [thetaYIntegrand]
  · exact (thetaYIntegrand_pos n y hn hy).le

/-- The first y-summand is integrable on any tail beginning at y0 >= 3. -/
theorem thetaYIntegrand_one_integrableOn (y0 : ℝ) (hy0 : 3 ≤ y0) :
    IntegrableOn (thetaYIntegrand 1) (Set.Ici y0) volume := by
  have hypos : 0 < y0 := by linarith
  have h1 := theta_rpow_exp_integrableOn_tail
    (1:ℝ) ((1:ℝ)/4) y0 (by norm_num) (by norm_num) hypos
  have h5 := theta_rpow_exp_integrableOn_tail
    (1:ℝ) ((5:ℝ)/4) y0 (by norm_num) (by norm_num) hypos
  have hcomb : IntegrableOn
      (fun y : ℝ =>
        2 * (y ^ ((5:ℝ)/4) * Real.exp (-(1:ℝ)*y)) -
        3 * (y ^ ((1:ℝ)/4) * Real.exp (-(1:ℝ)*y)))
      (Set.Ici y0) volume :=
    (h5.const_mul 2).sub (h1.const_mul 3)
  apply hcomb.congr_fun _ measurableSet_Ici
  intro y hy
  have hyp : 0 < y := lt_of_lt_of_le hypos hy
  have hpow : y ^ ((5:ℝ)/4) = y * y ^ ((1:ℝ)/4) := by
    rw [show ((5:ℝ)/4) = 1 + ((1:ℝ)/4) by ring,
      Real.rpow_add hyp, Real.rpow_one]
  dsimp [thetaYIntegrand]
  simp only [Nat.cast_one, one_pow, one_mul]
  rw [hpow]
  ring

/-- Unlike merely nonnegative Bochner integrals, this positive integral
is backed by explicit integrability of its single n=1 summand. -/
theorem thetaYIntegrand_one_integral_pos (y0 : ℝ) (hy0 : 3 ≤ y0) :
    0 < ∫ y in Set.Ici y0, thetaYIntegrand 1 y := by
  have hint := thetaYIntegrand_one_integrableOn y0 hy0
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ici y0)]
        thetaYIntegrand 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    exact (thetaYIntegrand_pos 1 y (by decide)
      (le_trans hy0 hy)).le
  have hopen : (0 : ENNReal) < volume (Set.Ioi y0) :=
    isOpen_Ioi.measure_pos volume
      ⟨y0 + 1, by simp⟩
  have hsubset :
      Set.Ioi y0 ⊆
        Function.support (thetaYIntegrand 1) ∩ Set.Ici y0 := by
    intro y hy
    exact ⟨(thetaYIntegrand_pos 1 y (by decide)
      (le_trans hy0 hy.le)).ne', hy.le⟩
  have hmass : (0 : ENNReal) <
      volume (Function.support (thetaYIntegrand 1) ∩ Set.Ici y0) :=
    lt_of_lt_of_le hopen (measure_mono hsubset)
  exact (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint).mpr hmass

/-- Strictly positive whole integral of the genuine theta y-series. -/
theorem thetaY_integral_strict_pos (y0 : ℝ) (hy0 : 3 ≤ y0) :
    0 < ∫ y in Set.Ici y0, ∑' n : ℕ, thetaYIntegrand n y := by
  have hs := thetaY_integral_tsum y0 (by linarith : 1 ≤ y0)
  have hsum : 0 <
      ∑' n : ℕ, ∫ y in Set.Ici y0, thetaYIntegrand n y :=
    hs.summable.tsum_pos
      (fun n =>
        setIntegral_nonneg measurableSet_Ici
          (fun y hy =>
            thetaYIntegrand_nonneg n y (le_trans hy0 hy)))
      1 (thetaYIntegrand_one_integral_pos y0 hy0)
  rw [hs.tsum_eq] at hsum
  exact hsum

/-- Strict positivity of the ORIGINAL Psi1(t) for every t >= 0. -/
theorem Psi1_pos (t : ℝ) (ht : 0 ≤ t) :
    0 < Psi1 t := by
  have he : (1:ℝ) ≤ Real.exp (4*t) := by
    have hnonneg : (0:ℝ) ≤ 4*t := by positivity
    simpa using
      (Real.exp_le_exp.mpr hnonneg :
        Real.exp 0 ≤ Real.exp (4*t))
  have hy0 : (3:ℝ) ≤ Real.pi * Real.exp (4*t) := by
    calc
      (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
      _ = Real.pi * 1 := by ring
      _ ≤ Real.pi * Real.exp (4*t) :=
        mul_le_mul_of_nonneg_left he (le_of_lt Real.pi_pos)
  have hscale :
      0 < (1:ℝ) / (4 * Real.pi ^ ((1:ℝ)/4)) := by
    positivity
  have hpositive := mul_pos hscale
    (thetaY_integral_strict_pos (Real.pi * Real.exp (4*t)) hy0)
  rw [Psi1_eq_thetaY_integral]
  simpa only [MeasureTheory.integral_Ici_eq_integral_Ioi] using
    hpositive

/-- The r=1 clause of the actual unconditional Nuttall main claim. -/
theorem W_one_pos (t : ℝ) (ht : 0 ≤ t) : 0 < W 1 t := by
  rw [W_one_eq_Psi1]
  exact Psi1_pos t ht

end W5
