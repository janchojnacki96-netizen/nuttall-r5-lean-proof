import W5.ThetaGammaRecenteredCertifiedChain

/-!
# Exact-rational adaptive fourth-root brackets for all theta Gamma bins

Every local root factor is (1+qL)^(1/4), q,L >= 0 rational.
Rather than supply a handwritten pair of fourth-power bounds for
every bin, bisect the rational interval [1,1+qL] EXACTLY.

The recursive function does not assert its own correctness.
The existing thetaGammaRootGridEligible predicate checks the resulting
rational fourth-power inequalities before the soundness theorem may be
applied. Thus any implementation error causes eligibility to fail, not
a false proof. No floating-point data, root oracle, or extra axiom.
-/

namespace W5

/-- Bisection with exact rational fourth-power comparisons. Each
step shrinks the current bracket by two; the last bounds remain
explicit exact rational numbers suitable for native_decide. -/
def thetaGammaRationalFourthRootBisect :
    ℕ → ℚ → ℚ → ℚ → QInterval
  | 0, _, lo, hi => ⟨lo,hi⟩
  | steps+1, t, lo, hi =>
      let mid := (lo+hi)/2
      if mid^4 ≤ t then
        thetaGammaRationalFourthRootBisect steps t mid hi
      else
        thetaGammaRationalFourthRootBisect steps t lo mid

/-- For q,L>=0, the fourth root of 1+qL starts in [1,1+qL].
The grid eligibility predicate checks this and all bisection output
bounds using exact rational fourth powers (without a trusted oracle). -/
def thetaGammaAutoFourthRootBounds
    (steps : ℕ) (q L : ℚ) : ℚ × ℚ :=
  let t := 1+q*L
  let I := thetaGammaRationalFourthRootBisect steps t 1 t
  (I.lo,I.hi)

/-- One uniform rational choice of root enclosures over every w-bin.
The precision can be raised without changing any analytic theorem. -/
def thetaGammaAutoRootGrid
    (steps : ℕ) (q : ℚ) : ℚ → ℚ × ℚ :=
  fun L => thetaGammaAutoFourthRootBounds steps q L

/-- A purely rational, executable eligibility check for a full grid.
True implies all root-power and Gamma-bin assumptions required by
the genuine truncated theta integral theorem. -/
def thetaGammaAutoRootGridCheck
    (steps : ℕ) (q L : ℚ) (us : List ℚ) : Bool :=
  decide (thetaGammaRootGridEligible
    q (thetaGammaAutoRootGrid steps q) L us)

/-- Soundness is immediately reused from the already checked generic
grid theorem. The rational Boolean check is the only numerical input. -/
theorem thetaGammaAutoRootGrid_containsReal
    (steps k : ℕ) (q L : ℚ) (us : List ℚ)
    (hq : 0 ≤ q)
    (hcheck : thetaGammaAutoRootGridCheck steps q L us = true) :
    QInterval.ContainsReal
      ⟨(thetaGammaLowerGridBox k q
          (thetaGammaAutoRootGrid steps q) L us).lo,
        (thetaGammaUpperGridBox k q
          (thetaGammaAutoRootGrid steps q) L us).hi⟩
      (∫ w in (L:ℝ)..thetaGammaBinLast (L:ℝ)
          (us.map (fun x : ℚ => (x:ℝ))),
        thetaGammaBinDensity k w *
          thetaGammaBinOriginalRoot (q:ℝ) w) := by
  apply thetaGammaOriginalTruncatedGrid_containsReal k q
  · exact hq
  · exact of_decide_eq_true hcheck

end W5
