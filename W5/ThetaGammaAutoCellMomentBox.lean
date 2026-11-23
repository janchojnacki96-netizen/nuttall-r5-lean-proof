import W5.ThetaGammaAutoMomentCheck

/-!
# Stronger original theta moment intervals on every rational x-cell

The last fifth-pivot failure may be caused by the old global
quadratic/cubic moments M_k(x/n). Instead of an assumption or a
new per-k calculation, evaluate the already certified FULL original
moment at the left/right x endpoints using one exact Gamma grid.

Existing Mathlib-backed monotonicity of M_k (for x>=0) then
certifies the ENTIRE x-cell. This module is uniform in n,k,a,b
and requires only the two fully executable endpoint Boolean checks.
-/

namespace W5

/-- One sharp rational interval for the genuine theta moment
M_k(x/n) on x in [a,b], with a common w-grid. -/
def thetaGammaAutoCellMomentBox (steps k : ℕ)
    (a b : ℚ) (n : ℕ) (us : List ℚ) : QInterval :=
  ⟨(thetaGammaAutoMomentBox steps k (a/(n:ℚ)) us).lo,
    (thetaGammaAutoMomentBox steps k (b/(n:ℚ)) us).hi⟩

/-- Soundness for ALL moment degrees, all n>=1, and ALL x-cells.
The only numerical conditions are the two exact rational endpoint
tests, and the existing monotonicity of the original real moments. -/
theorem thetaGammaAutoCellMomentBox_containsReal
    (steps k : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hn : 0 < n)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck
      steps (a/(n:ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b/(n:ℚ)) us = true) :
    QInterval.ContainsReal
      (thetaGammaAutoCellMomentBox steps k a b n us)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  let A := thetaGammaAutoMomentBox steps k (a/(n:ℚ)) us
  let B := thetaGammaAutoMomentBox steps k (b/(n:ℚ)) us
  have hAn : QInterval.ContainsReal A
      (thetaAuditedOneWeightedMoment
        ((a:ℝ)/(n:ℝ)) k) := by
    simpa only [A, Rat.cast_div, Rat.cast_natCast] using
      (thetaGammaAutoMomentBox_containsReal_of_check
        steps k (a/(n:ℚ)) us hA)
  have hBn : QInterval.ContainsReal B
      (thetaAuditedOneWeightedMoment
        ((b:ℝ)/(n:ℝ)) k) := by
    simpa only [B, Rat.cast_div, Rat.cast_natCast] using
      (thetaGammaAutoMomentBox_containsReal_of_check
        steps k (b/(n:ℚ)) us hB)
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have hn1Nat : 1 ≤ n := by omega
    exact_mod_cast hn1Nat
  have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hya : 0 ≤ (a:ℝ)/(n:ℝ) :=
    div_nonneg haR hnR.le
  have hInv : 0 ≤ ((n:ℝ)⁻¹) := inv_nonneg.mpr hnR.le
  have haxn : (a:ℝ)/(n:ℝ) ≤ x/(n:ℝ) := by
    simpa only [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hax hInv)
  have hxbn : x/(n:ℝ) ≤ (b:ℝ)/(n:ℝ) := by
    simpa only [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hxb hInv)
  have hb1 : (b:ℝ)/(n:ℝ) ≤ 1 :=
    (div_le_iff₀ hnR).2 (by linarith)
  have hM := thetaAuditedOneWeightedMoment_cell_interval
    ((a:ℝ)/(n:ℝ)) (x/(n:ℝ)) ((b:ℝ)/(n:ℝ))
    hya haxn hxbn hb1 k A B hAn hBn
  simpa only [thetaGammaAutoCellMomentBox, A, B] using hM

end W5
