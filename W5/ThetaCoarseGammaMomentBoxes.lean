import W5.ThetaAllSquareIndexNineMoments
import W5.ThetaAuditedMomentGammaBox

/-!
# Uniform rational Gamma boxes for all retained theta square indices

A useful fallback to expensive endpoint quadrature: for every n>0,
the actual weighted moment of x/n is bounded using the existing
Gamma moment estimate and the upper endpoint of the rational x-cell.

The bound is deliberately coarse. It is mathematically sound for
all positive square indices, but the resulting rational matrix may
fail strict LDL interval checks unless a sharper moment certificate
is supplied. The algorithm can select finer enclosures only where
the coarse bound is inadequate.
-/

namespace W5

/-- Exact rational coarse moment enclosure at an x-cell upper bound.
No numerical integration is involved. -/
def thetaNthCoarseGammaMomentBox (b : ℚ) (n k : ℕ) : QInterval :=
  ⟨(Nat.factorial k : ℚ),
   (Nat.factorial k : ℚ) +
     (b / (n : ℚ))^2 * (Nat.factorial (k+1) : ℚ)⟩

/-- A single Mathlib-backed Gamma bound proves soundness of the
coarse box for every n>0, index k and all x in 0≤x≤b≤1. -/
theorem thetaNthCoarseGammaMomentBox_containsReal
    (b : ℚ) (x : ℝ)
    (hx : 0 ≤ x) (hxb : x ≤ (b : ℝ)) (hb : (b : ℝ) ≤ 1)
    (n k : ℕ) (hn : 0 < n) :
    QInterval.ContainsReal (thetaNthCoarseGammaMomentBox b n k)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let y : ℝ := x/(n:ℝ)
  let z : ℝ := (b:ℝ)/(n:ℝ)
  have hy : 0 ≤ y := div_nonneg hx hnR.le
  have hyz : y ≤ z := by
    dsimp [y, z]
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hxb (inv_nonneg.mpr hnR.le)
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hy1 : y ≤ 1 := hyz.trans hz1
  have hsq : y^2 ≤ z^2 := pow_le_pow_left₀ hy hyz 2
  have hlo := thetaAuditedOneWeightedMoment_gamma_lower y hy hy1 k
  have hu := thetaAuditedOneWeightedMoment_gamma_upper y hy hy1 k
  have hupper :
      thetaAuditedOneWeightedMoment y k ≤
        (Nat.factorial k : ℝ) +
        z^2 * (Nat.factorial (k+1) : ℝ) := by
    calc
      _ ≤ (Nat.factorial k : ℝ) +
            y^2 * (Nat.factorial (k+1) : ℝ) := hu
      _ ≤ (Nat.factorial k : ℝ) +
            z^2 * (Nat.factorial (k+1) : ℝ) := by
          exact add_le_add_left
            (mul_le_mul_of_nonneg_right hsq (by positivity))
            (Nat.factorial k : ℝ)
  dsimp [y, z] at hlo hupper
  simpa only [QInterval.ContainsReal,
    thetaNthCoarseGammaMomentBox,
    Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat] using
    (show
      (Nat.factorial k : ℝ) ≤
        thetaAuditedOneWeightedMoment (x/(n:ℝ)) k ∧
      thetaAuditedOneWeightedMoment (x/(n:ℝ)) k ≤
        (Nat.factorial k : ℝ) +
        ((b:ℝ)/(n:ℝ))^2 * (Nat.factorial (k+1) : ℝ)
      from ⟨hlo, hupper⟩)

end W5
