import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import W5.ThetaAuditedMomentGammaCubicCellBox

/-!
# Arbitrarily refinable original theta weighted Gamma moments

The existing quadratic-lower/cubic-upper fourth-root bounds are
too wide even when the x-cell collapses to one point. In particular
their k=8 weighted moment width at x=145/256 exceeds 70,000.

A rigorous high-precision alternative partitions the INTEGRATION
VARIABLE w, not the 51 original x-cells, into uniform rational bins.
On each bin the concave fourth root is bracketed by its chord
(lower) and left-endpoint tangent (upper). Both are AFFINE in w,
so integrating their product with e^{-w}w^k requires only the two
already known Γ moment indices k and k+1 on each bin.

This file proves the algebraic and convexity core of that strategy,
without re-proving concavity: Real.concaveOn_rpow is from Mathlib.
Further work: finite-bin exponential Gamma masses, exact rational
fourth-root endpoints, and an independently bounded w-tail.
No claim that the resulting 48-cell LDL checks have passed.
-/

namespace W5

/-- The existing quarter-root algebra, isolated as a generic lemma,
using exactly Mathlib's real-power composition theorem. -/
theorem thetaQuarterRoot_pow_four (t : ℝ) (ht : 0 ≤ t) :
    (t^((1:ℝ)/4))^4 = t := by
  calc
    (t^((1:ℝ)/4))^4 =
      (t^((1:ℝ)/4))^(4:ℝ) := by
        exact (Real.rpow_natCast (t^((1:ℝ)/4)) 4).symm
    _ = t^(((1:ℝ)/4)*(4:ℝ)) :=
      (Real.rpow_mul ht ((1:ℝ)/4) (4:ℝ)).symm
    _ = t := by norm_num

/-- A global affine TANGENT upper bound at any a≥1, proved
directly by an exact quartic factorization (no new calculus).

  fourthRoot(a+h) ≤ fourthRoot(a) + h/(4*fourthRoot(a)^3).

This is the local upper integrand for every w-bin. -/
theorem thetaQuarterRoot_tangent_step
    (a h : ℝ) (ha : 1 ≤ a) (hh : 0 ≤ h) :
    (a+h)^((1:ℝ)/4) ≤
      a^((1:ℝ)/4) + h/(4*(a^((1:ℝ)/4))^3) := by
  let r : ℝ := (a+h)^((1:ℝ)/4)
  let s : ℝ := a^((1:ℝ)/4)
  have har : 0 < a := by linarith
  have hr : r^4 = a+h :=
    thetaQuarterRoot_pow_four (a+h) (by linarith)
  have hs : s^4 = a :=
    thetaQuarterRoot_pow_four a har.le
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.rpow_pos_of_pos har _
  have hfactor :
      0 ≤ (r-s)^2*(r^2+2*r*s+3*s^2) := by
    positivity
  have hquartic : 4*s^3*(r-s) ≤ h := by
    nlinarith [hfactor, hr, hs]
  have hden : 0 < 4*s^3 := by positivity
  have hstep : r-s ≤ h/(4*s^3) :=
    (le_div_iff₀ hden).2 (by nlinarith [hquartic])
  dsimp [r,s] at hstep
  linarith

/-- The lower chord bound is JUST Mathlib's proved concavity of
t↦t^(1/4) on t≥0; no re-derivation of the curvature theorem.
The weights are the exact barycentric weights of t∈[a,b]. -/
theorem thetaQuarterRoot_chord_step
    (a b t : ℝ)
    (ha : 0 ≤ a) (hab : a < b)
    (hat : a ≤ t) (htb : t ≤ b) :
    ((b-t)/(b-a))*a^((1:ℝ)/4) +
      ((t-a)/(b-a))*b^((1:ℝ)/4) ≤
        t^((1:ℝ)/4) := by
  let u : ℝ := (b-t)/(b-a)
  let v : ℝ := (t-a)/(b-a)
  have hden : 0 < b-a := sub_pos.mpr hab
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr htb) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hat) hden.le
  have huv : u+v=1 := by
    dsimp [u,v]
    field_simp [ne_of_gt hden]
    ring
  have haSet : a ∈ Set.Ici (0:ℝ) := ha
  have hbSet : b ∈ Set.Ici (0:ℝ) :=
    ha.trans hab.le
  have hchord :=
    (Real.concaveOn_rpow
      (p:=((1:ℝ)/4)) (by norm_num) (by norm_num)).2
      haSet hbSet hu hv huv
  have ht : u*a+v*b=t := by
    dsimp [u,v]
    field_simp [ne_of_gt hden]
    ring
  simpa only [ht] using hchord

/-- One generic piecewise upper integrand, for any nonnegative
w-bin [L,U] and any nonnegative scaled theta parameter q.
No Taylor series or numeric approximations are involved. -/
theorem thetaQuarterRoot_tangent_on_bin
    (q L w : ℝ) (hq : 0 ≤ q)
    (hL : 0 ≤ L) (hLw : L ≤ w) :
    (1+q*w)^((1:ℝ)/4) ≤
      (1+q*L)^((1:ℝ)/4) +
        (q*(w-L))/(4*((1+q*L)^((1:ℝ)/4))^3) := by
  have ha : (1:ℝ) ≤ 1+q*L := by
    have : 0 ≤ q*L := mul_nonneg hq hL
    linarith
  have hh : 0 ≤ q*(w-L) := mul_nonneg hq (sub_nonneg.mpr hLw)
  have h := thetaQuarterRoot_tangent_step
    (1+q*L) (q*(w-L)) ha hh
  convert h using 1 <;> ring

end W5
