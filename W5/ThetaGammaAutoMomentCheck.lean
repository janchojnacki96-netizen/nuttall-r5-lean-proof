import W5.ThetaGammaAutoFullMomentGrid

/-!
# Single executable rational check for every full original theta moment

This removes the last external real equality of a w-grid endpoint:
the final rational endpoint is computed by a single list recursion and
proved identical to the real endpoint in the existing Mathlib
integral-chain theorem.

One Boolean predicate now verifies all root, Gamma-bin, exp(-H), and
range premises. Its true value gives a REAL enclosure of the original
thetaAuditedOneWeightedMoment at any rational x and every k.
-/

namespace W5

/-- Rational final endpoint of a finite list of adjacent w-bins. -/
def thetaGammaRationalLast (L : ℚ) : List ℚ → ℚ
  | [] => L
  | U :: us => thetaGammaRationalLast U us

/-- The executable rational endpoint is definitionally the same
recursion as the already verified real Gamma integration chain. -/
theorem thetaGammaRationalLast_cast (L : ℚ) (us : List ℚ) :
    ((thetaGammaRationalLast L us):ℝ) =
      thetaGammaBinLast (L:ℝ)
        (us.map (fun x : ℚ => (x:ℝ))) := by
  induction us generalizing L with
  | nil => rfl
  | cons U us ih =>
      simpa [thetaGammaRationalLast, thetaGammaBinLast] using ih U

/-- Fully generated rational original theta moment enclosure. -/
def thetaGammaAutoMomentBox (steps k : ℕ)
    (y : ℚ) (us : List ℚ) : QInterval :=
  thetaGammaAutoFullMomentGridBox steps k y
    (thetaGammaRationalLast 0 us) us

/-- ONE finite Boolean eligibility test, including endpoint and tail
validity, for every k. No classical or untrusted real decision. -/
def thetaGammaAutoMomentCheck
    (steps : ℕ) (y : ℚ) (us : List ℚ) : Bool :=
  let H := thetaGammaRationalLast 0 us
  decide ((0:ℚ) ≤ y ∧ y ≤ 1 ∧
    (0:ℚ) ≤ H ∧ H ≤ (1024:ℚ)/3 ∧
    0 < (thetaBulkExpTaylorBox
      (QInterval.point (H/1024))).lo) &&
  thetaGammaAutoRootGridCheck steps (y^2) 0 us

/-- All analytic obligations for a full theta Gamma moment collapse
to this ONE checked rational Boolean. One proof works for all k. -/
theorem thetaGammaAutoMomentBox_containsReal_of_check
    (steps k : ℕ) (y : ℚ) (us : List ℚ)
    (hcheck : thetaGammaAutoMomentCheck steps y us = true) :
    QInterval.ContainsReal (thetaGammaAutoMomentBox steps k y us)
      (thetaAuditedOneWeightedMoment (y:ℝ) k) := by
  simp only [thetaGammaAutoMomentCheck,
    Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hnumeric, hgrid⟩
  have hp : (0:ℚ) ≤ y ∧ y ≤ 1 ∧
      (0:ℚ) ≤ thetaGammaRationalLast 0 us ∧
      thetaGammaRationalLast 0 us ≤ (1024:ℚ)/3 ∧
      0 < (thetaBulkExpTaylorBox
        (QInterval.point
          (thetaGammaRationalLast 0 us / 1024))).lo :=
    of_decide_eq_true hnumeric
  rcases hp with ⟨hy, hy1, hH, hHmax, hexp⟩
  unfold thetaGammaAutoMomentBox
  exact thetaGammaAutoFullMomentGridBox_containsReal
    steps k y (thetaGammaRationalLast 0 us) us
    hy hy1 hgrid (thetaGammaRationalLast_cast 0 us).symm
    hH hHmax hexp

end W5
