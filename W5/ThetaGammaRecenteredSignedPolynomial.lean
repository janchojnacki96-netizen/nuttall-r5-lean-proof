import W5.ThetaGammaRecenteredBinIntegral

/-!
# EXACT signed cubic polynomial for every locally recentered theta Γ bin

The CI-verified recentered real fourth-root lower/upper envelopes
are written in powers of v=q*(w-L)/(1+qL). To consume the generic
signed Gamma-moment engine and avoid sign-destroying positive
majorants, expand them *symbolically* as polynomials in w.

The resulting coefficients may be POSITIVE OR NEGATIVE and are
simple rational expressions in t=q/(1+qL) and the bin origin L.
One Mathlib ring proof works for every x-cell, every n, every
Gamma moment degree, and every integration bin.

No numerical approximations or assumptions are introduced here.
-/

namespace W5

/-- Signed degree-2 polynomial obtained from the recentered lower
fourth-root envelope. All exact coefficients remain visible. -/
noncomputable def thetaGammaRecenteredLowerPoly
    (t L w : ℝ) : ℝ :=
  (1-t*L/4-3*t^2*L^2/32) +
    (t/4+3*t^2*L/16)*w - (3*t^2/32)*w^2

/-- Signed degree-3 polynomial obtained from the recentered upper
fourth-root envelope. -/
noncomputable def thetaGammaRecenteredUpperPoly
    (t L w : ℝ) : ℝ :=
  (1-t*L/4-3*t^2*L^2/32-7*t^3*L^3/128) +
    (t/4+3*t^2*L/16+21*t^3*L^2/128)*w +
    (-3*t^2/32-21*t^3*L/128)*w^2 +
    (7*t^3/128)*w^3

/-- Exact lower polynomial expansion. No positivity required. -/
theorem thetaGammaRecenteredLowerPoly_expansion
    (t L w : ℝ) :
    thetaGammaRecenteredLowerPoly t L w =
      1+t*(w-L)/4-3*(t*(w-L))^2/32 := by
  unfold thetaGammaRecenteredLowerPoly
  ring

/-- Exact upper polynomial expansion. No positivity required. -/
theorem thetaGammaRecenteredUpperPoly_expansion
    (t L w : ℝ) :
    thetaGammaRecenteredUpperPoly t L w =
      1+t*(w-L)/4-3*(t*(w-L))^2/32+
        7*(t*(w-L))^3/128 := by
  unfold thetaGammaRecenteredUpperPoly
  ring

/-- The original locally recentered quadratic lower theta root
is EXACTLY a constant real fourth root times a signed polynomial
in the Gamma integration variable w. -/
theorem thetaGammaBinLowerRoot_eq_signed_poly
    (q L w : ℝ) :
    thetaGammaBinLowerRoot q L w =
      (thetaGammaBinBase q L)^((1:ℝ)/4) *
        thetaGammaRecenteredLowerPoly
          (q/(thetaGammaBinBase q L)) L w := by
  rw [thetaGammaRecenteredLowerPoly_expansion]
  dsimp [thetaGammaBinLowerRoot, thetaGammaBinOffset]
  simp only [div_eq_mul_inv]
  ring

/-- The corresponding exact upper representation, including
the signed cubic correction. -/
theorem thetaGammaBinUpperRoot_eq_signed_poly
    (q L w : ℝ) :
    thetaGammaBinUpperRoot q L w =
      (thetaGammaBinBase q L)^((1:ℝ)/4) *
        thetaGammaRecenteredUpperPoly
          (q/(thetaGammaBinBase q L)) L w := by
  rw [thetaGammaRecenteredUpperPoly_expansion]
  dsimp [thetaGammaBinUpperRoot, thetaGammaBinOffset]
  simp only [div_eq_mul_inv]
  ring

/-- These formulas are explicitly centered: their difference
is the EXACT cubic correction in (w-L), preserving its sign. -/
theorem thetaGammaRecenteredPoly_gap
    (t L w : ℝ) :
    thetaGammaRecenteredUpperPoly t L w -
      thetaGammaRecenteredLowerPoly t L w =
        (7:ℝ)/128 * (t*(w-L))^3 := by
  rw [thetaGammaRecenteredUpperPoly_expansion,
    thetaGammaRecenteredLowerPoly_expansion]
  ring


/-!
## One exact integral bridge for every recentered Gamma bin

Compose the existing signed-polynomial expansion with Mathlib's
intervalIntegral.integral_const_mul. This works for any moment degree
and both lower/upper roots, without reproducing analytic integration.
It is an exact identity; numerical interval evaluation is separate.
-/

/-- Pull a constant recentered fourth-root factor outside any
weighted finite Gamma integral. -/
theorem thetaGammaWeightedIntegral_constFactor
    (k : ℕ) (L U A : ℝ) (f g : ℝ → ℝ)
    (hfg : ∀ w : ℝ, f w = A * g w) :
    (∫ w in L..U, thetaGammaBinDensity k w * f w) =
      A * (∫ w in L..U, thetaGammaBinDensity k w * g w) := by
  have heq :
      (fun w : ℝ => thetaGammaBinDensity k w * f w) =
      (fun w : ℝ => A * (thetaGammaBinDensity k w * g w)) := by
    funext w
    rw [hfg w]
    ring
  calc
    (∫ w in L..U, thetaGammaBinDensity k w * f w) =
      (∫ w in L..U, A * (thetaGammaBinDensity k w * g w)) :=
        congrArg (fun h : ℝ → ℝ => ∫ w in L..U, h w) heq
    _ = A * (∫ w in L..U, thetaGammaBinDensity k w * g w) := by
      rw [intervalIntegral.integral_const_mul]

/-- Every lower recentered Gamma-bin integral is exactly the
constant fourth root times an integral of a SIGNED quadratic. -/
theorem thetaGammaBinLowerWeightedIntegral_eq_signed_poly
    (q L U : ℝ) (k : ℕ) :
    (∫ w in L..U,
      thetaGammaBinDensity k w * thetaGammaBinLowerRoot q L w) =
      (thetaGammaBinBase q L)^((1:ℝ)/4) *
        (∫ w in L..U, thetaGammaBinDensity k w *
          thetaGammaRecenteredLowerPoly
            (q/(thetaGammaBinBase q L)) L w) := by
  exact thetaGammaWeightedIntegral_constFactor k L U
    ((thetaGammaBinBase q L)^((1:ℝ)/4))
    (thetaGammaBinLowerRoot q L)
    (thetaGammaRecenteredLowerPoly
      (q/(thetaGammaBinBase q L)) L)
    (thetaGammaBinLowerRoot_eq_signed_poly q L)

/-- Every upper recentered Gamma-bin integral is exactly the
constant fourth root times an integral of a SIGNED cubic. -/
theorem thetaGammaBinUpperWeightedIntegral_eq_signed_poly
    (q L U : ℝ) (k : ℕ) :
    (∫ w in L..U,
      thetaGammaBinDensity k w * thetaGammaBinUpperRoot q L w) =
      (thetaGammaBinBase q L)^((1:ℝ)/4) *
        (∫ w in L..U, thetaGammaBinDensity k w *
          thetaGammaRecenteredUpperPoly
            (q/(thetaGammaBinBase q L)) L w) := by
  exact thetaGammaWeightedIntegral_constFactor k L U
    ((thetaGammaBinBase q L)^((1:ℝ)/4))
    (thetaGammaBinUpperRoot q L)
    (thetaGammaRecenteredUpperPoly
      (q/(thetaGammaBinBase q L)) L)
    (thetaGammaBinUpperRoot_eq_signed_poly q L)

end W5
