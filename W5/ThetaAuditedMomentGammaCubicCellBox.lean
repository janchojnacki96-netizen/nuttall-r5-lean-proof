import W5.ThetaAuditedMomentGammaCubicUpper
import W5.ThetaOneSquareCellQuadraticBridge

/-!
# Uniform cubic-Gamma moment enclosures on every rational x-cell

Refines the previous quadratic-lower/quarter-upper box by replacing
ONLY the upper endpoint with the new proved cubic fourth-root bound.
The lower quadratic moment bound is reused verbatim, as are the
previous real-sound rational interval arithmetic and polynomial
coefficient bounds.

One theorem handles every square-index n>0 and moment k.
One subsequent n=1 term bridge handles all 25 theta entries
without explicit per-entry expansion or fresh integration.
-/

namespace W5

/-- A stronger, entirely rational and real-sound moment box;
its lower endpoint reuses the previously validated quadratic box. -/
def thetaNthCubicGammaMomentBox (a b : ℚ) (n k : ℕ) : QInterval :=
  ⟨(thetaNthQuadraticGammaMomentBox a b n k).lo,
    (Nat.factorial k : ℚ) +
      (((b/(n:ℚ))^2)/4) * (Nat.factorial (k+1) : ℚ) -
      (3*((b/(n:ℚ))^4)/32) * (Nat.factorial (k+2) : ℚ) +
      (7*((b/(n:ℚ))^6)/128) * (Nat.factorial (k+3) : ℚ)⟩

/-- Uniform real validity of all cubic Gamma moment intervals. -/
theorem thetaNthCubicGammaMomentBox_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ))
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (n k : ℕ) (hn : 0 < n) :
    QInterval.ContainsReal (thetaNthCubicGammaMomentBox a b n k)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  have hquad :=
    thetaNthQuadraticGammaMomentBox_containsReal
      a b x ha hax hxb hb n k hn
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  let y : ℝ := (b:ℝ)/(n:ℝ)
  have hb0 : (0:ℝ) ≤ (b:ℝ) := (ha.trans hax).trans hxb
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg hb0 hnR.le
  have hy1 : y ≤ 1 := by
    dsimp [y]
    apply (div_le_iff₀ hnR).2
    linarith
  have hxy0 : 0 ≤ x/(n:ℝ) := div_nonneg (ha.trans hax) hnR.le
  have hxy : x/(n:ℝ) ≤ y := by
    dsimp [y]
    simpa only [div_eq_mul_inv] using
      (mul_le_mul_of_nonneg_right hxb (inv_nonneg.mpr hnR.le))
  have hm :=
    thetaAuditedOneWeightedMoment_mono
      (x/(n:ℝ)) y hxy0 hxy hy1 k
  have hu :=
    hm.trans (thetaAuditedOneWeightedMoment_gamma_upper_cubic y hy0 hy1 k)
  constructor
  · simpa only [thetaNthCubicGammaMomentBox] using hquad.1
  · dsimp [y] at hu
    simpa only [thetaNthCubicGammaMomentBox,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hu

/-- A computable rational n=1 interval for all original theta
coefficient entries. It uses the stronger third-order upper
Gamma moments but does not alter the already proved semantics
of polynomial evaluation or nine-term interval folding. -/
noncomputable def thetaOneSquareCellTermCubicBox
    (a b : ℚ) (i j : Fin 5) : QInterval :=
  thetaAuditedOneTermMomentInterval
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaOneSquareCellCoefficientBox a b i j)
    (thetaNthCubicGammaMomentBox a b 1) 9

/-- The new n=1 term interval soundly contains the actual original
theta summand on any rational cell [a,b] with b<=1. -/
theorem thetaOneSquareCellTermCubicBox_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ))
    (hx : 0 < x) (hax : (a:ℝ) ≤ x)
    (hxb : x ≤ (b:ℝ)) (hb1 : (b:ℝ) ≤ 1)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaOneSquareCellTermCubicBox a b i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  have hdiag : QInterval.ContainsReal
      (thetaFirstCellGammaUniformDiagonal i j)
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) := by
    by_cases hij : i = j
    · subst j
      simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, Rat.cast_div, Rat.cast_pow]
    · simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, hij]
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx (hxb.trans hb1) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaOneSquareCellCoefficientBox a b i j)
    (thetaNthCubicGammaMomentBox a b 1)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaOneSquareCellCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ => by
      simpa only [Nat.cast_one, div_one] using
        (thetaNthCubicGammaMomentBox_containsReal
          a b x ha hax hxb hb1 1 k (by omega)))

end W5
