import W5.ThetaEarlyRoundedGammaMoments

/-!
# Bounded-denominator running sums for genuine original Gamma bins

The previous certified Gamma grid sums exact rationals across every
w-bin before rounding, causing denominator growth in late-cell Lean
numerical evaluations. This module performs an already-verified
outward 2^768 rounding after EACH bin addition, with one reusable
finite induction showing that the result encloses the old exact sum.

The original real-integral soundness proof is REUSED in full: the new
moment encloses the old certified moment, so no new measure theory,
integral axiom, or external numeric trust is introduced.
-/

namespace W5

/-- Rounding DOWN cannot raise the rational lower endpoint. -/
private theorem thetaGammaRunningRound_lo_le (I : QInterval) :
    (thetaBulkRoundedQInterval I).lo ≤ I.lo := by
  have hDq : (0 : ℚ) < (thetaAuditScale : ℚ) := by
    exact_mod_cast thetaAuditScale_pos
  change (((⌊I.lo * (thetaAuditScale : ℚ)⌋ : ℤ) : ℚ) /
    (thetaAuditScale : ℚ)) ≤ I.lo
  exact (div_le_iff₀ hDq).2 (Int.floor_le _)

/-- Rounding UP cannot lower the rational upper endpoint. -/
private theorem thetaGammaRunningRound_hi_ge (I : QInterval) :
    I.hi ≤ (thetaBulkRoundedQInterval I).hi := by
  have hDq : (0 : ℚ) < (thetaAuditScale : ℚ) := by
    exact_mod_cast thetaAuditScale_pos
  change I.hi ≤ (((⌈I.hi * (thetaAuditScale : ℚ)⌉ : ℤ) : ℚ) /
    (thetaAuditScale : ℚ))
  exact (le_div_iff₀ hDq).2 (Int.le_ceil _)

/-- Abstract exact bin sum: the same recursion used by the earlier
lower/upper Gamma-grid integrators. -/
def thetaGammaPlainBinSum (f : ℚ → ℚ → QInterval) :
    ℚ → List ℚ → QInterval
  | _, [] => QInterval.point 0
  | a, b :: bs =>
      QInterval.add (f a b) (thetaGammaPlainBinSum f b bs)

/-- Bounded-denominator version. The intermediate sum is rounded
outward after every bin, not just at the end. -/
def thetaGammaRoundedBinSum (f : ℚ → ℚ → QInterval) :
    ℚ → List ℚ → QInterval
  | _, [] => QInterval.point 0
  | a, b :: bs =>
      thetaBulkRoundedQInterval
        (QInterval.add (f a b) (thetaGammaRoundedBinSum f b bs))

/-- One rational induction proves outward containment for EVERY
signed bin generator, every grid and every moment order. -/
theorem thetaGammaRoundedBinSum_encloses_plain
    (f : ℚ → ℚ → QInterval) :
    ∀ a bs,
      (thetaGammaRoundedBinSum f a bs).lo ≤
        (thetaGammaPlainBinSum f a bs).lo ∧
      (thetaGammaPlainBinSum f a bs).hi ≤
        (thetaGammaRoundedBinSum f a bs).hi := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      exact ⟨le_rfl, le_rfl⟩
  | cons b bs ih =>
      obtain ⟨hlo, hhi⟩ := ih b
      constructor
      · change
          (thetaBulkRoundedQInterval
            (QInterval.add (f a b)
              (thetaGammaRoundedBinSum f b bs))).lo ≤
          (QInterval.add (f a b)
            (thetaGammaPlainBinSum f b bs)).lo
        calc
          _ ≤ (QInterval.add (f a b)
              (thetaGammaRoundedBinSum f b bs)).lo :=
            thetaGammaRunningRound_lo_le _
          _ ≤ (QInterval.add (f a b)
              (thetaGammaPlainBinSum f b bs)).lo := by
            simpa only [QInterval.add] using
              (add_le_add_right hlo (f a b).lo)
      · change
          (QInterval.add (f a b)
            (thetaGammaPlainBinSum f b bs)).hi ≤
          (thetaBulkRoundedQInterval
            (QInterval.add (f a b)
              (thetaGammaRoundedBinSum f b bs))).hi
        calc
          _ ≤ (QInterval.add (f a b)
              (thetaGammaRoundedBinSum f b bs)).hi := by
            simpa only [QInterval.add] using
              (add_le_add_right hhi (f a b).hi)
          _ ≤ _ := thetaGammaRunningRound_hi_ge _

/-- The exact original signed lower-root w-bin. -/
def thetaGammaLowerRunningBin (steps k : ℕ) (q L U : ℚ) :
    QInterval :=
  thetaGammaLowerRootSignedBinBox k q L U
    (thetaGammaAutoRootGrid steps q L).1
    (thetaGammaAutoRootGrid steps q L).2

/-- The exact original signed upper-root w-bin. -/
def thetaGammaUpperRunningBin (steps k : ℕ) (q L U : ℚ) :
    QInterval :=
  thetaGammaUpperRootSignedBinBox k q L U
    (thetaGammaAutoRootGrid steps q L).1
    (thetaGammaAutoRootGrid steps q L).2

theorem thetaGammaPlainLower_eq (steps k : ℕ) (q : ℚ) :
    ∀ a bs,
      thetaGammaPlainBinSum (thetaGammaLowerRunningBin steps k q)
        a bs =
      thetaGammaLowerGridBox k q (thetaGammaAutoRootGrid steps q) a bs := by
  intro a bs
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      change
        QInterval.add (thetaGammaLowerRunningBin steps k q a b)
          (thetaGammaPlainBinSum
            (thetaGammaLowerRunningBin steps k q) b bs) =
        QInterval.add (thetaGammaLowerRunningBin steps k q a b)
          (thetaGammaLowerGridBox k q
            (thetaGammaAutoRootGrid steps q) b bs)
      rw [ih b]

theorem thetaGammaPlainUpper_eq (steps k : ℕ) (q : ℚ) :
    ∀ a bs,
      thetaGammaPlainBinSum (thetaGammaUpperRunningBin steps k q)
        a bs =
      thetaGammaUpperGridBox k q (thetaGammaAutoRootGrid steps q) a bs := by
  intro a bs
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
      change
        QInterval.add (thetaGammaUpperRunningBin steps k q a b)
          (thetaGammaPlainBinSum
            (thetaGammaUpperRunningBin steps k q) b bs) =
        QInterval.add (thetaGammaUpperRunningBin steps k q a b)
          (thetaGammaUpperGridBox k q
            (thetaGammaAutoRootGrid steps q) b bs)
      rw [ih b]

/-- Full weighted Gamma moment: only the grid accumulator changes,
while the existing rigorous infinite-tail enclosure is untouched. -/
def thetaGammaRunningAutoMomentBox
    (steps k : ℕ) (y : ℚ) (us : List ℚ) : QInterval :=
  let L := thetaGammaRoundedBinSum
    (thetaGammaLowerRunningBin steps k (y^2)) 0 us
  let U := thetaGammaRoundedBinSum
    (thetaGammaUpperRunningBin steps k (y^2)) 0 us
  QInterval.add ⟨L.lo, U.hi⟩
    (thetaGammaWeightedExactTailBox k y (thetaGammaRationalLast 0 us))

/-- This rounded-running moment encloses the exact expression already
proved real-sound by the original full Gamma integral bridge. -/
theorem thetaGammaRunningAutoMomentBox_encloses_old
    (steps k : ℕ) (y : ℚ) (us : List ℚ) :
    (thetaGammaRunningAutoMomentBox steps k y us).lo ≤
      (thetaGammaAutoMomentBox steps k y us).lo ∧
    (thetaGammaAutoMomentBox steps k y us).hi ≤
      (thetaGammaRunningAutoMomentBox steps k y us).hi := by
  have hL := (thetaGammaRoundedBinSum_encloses_plain
    (thetaGammaLowerRunningBin steps k (y^2)) 0 us).1
  have hU := (thetaGammaRoundedBinSum_encloses_plain
    (thetaGammaUpperRunningBin steps k (y^2)) 0 us).2
  rw [thetaGammaPlainLower_eq] at hL
  rw [thetaGammaPlainUpper_eq] at hU
  constructor
  · change
      (thetaGammaRoundedBinSum
        (thetaGammaLowerRunningBin steps k (y^2)) 0 us).lo +
        (thetaGammaWeightedExactTailBox k y
          (thetaGammaRationalLast 0 us)).lo ≤
      (thetaGammaLowerGridBox k (y^2)
        (thetaGammaAutoRootGrid steps (y^2)) 0 us).lo +
        (thetaGammaWeightedExactTailBox k y
          (thetaGammaRationalLast 0 us)).lo
    exact add_le_add_left hL _
  · change
      (thetaGammaUpperGridBox k (y^2)
        (thetaGammaAutoRootGrid steps (y^2)) 0 us).hi +
        (thetaGammaWeightedExactTailBox k y
          (thetaGammaRationalLast 0 us)).hi ≤
      (thetaGammaRoundedBinSum
        (thetaGammaUpperRunningBin steps k (y^2)) 0 us).hi +
        (thetaGammaWeightedExactTailBox k y
          (thetaGammaRationalLast 0 us)).hi
    exact add_le_add_left hU _

/-- TRUE original Gamma-integral soundness, without re-proving any
integrals: verified exact grid and outward fixedpoint inclusion. -/
theorem thetaGammaRunningAutoMomentBox_containsReal_of_check
    (steps k : ℕ) (y : ℚ) (us : List ℚ)
    (hcheck : thetaGammaAutoMomentCheck steps y us = true) :
    QInterval.ContainsReal
      (thetaGammaRunningAutoMomentBox steps k y us)
      (thetaAuditedOneWeightedMoment (y : ℝ) k) := by
  obtain ⟨hlo, hhi⟩ :=
    thetaGammaRunningAutoMomentBox_encloses_old steps k y us
  have hOld :=
    thetaGammaAutoMomentBox_containsReal_of_check steps k y us hcheck
  have hloR : ((thetaGammaRunningAutoMomentBox
      steps k y us).lo : ℝ) ≤
      ((thetaGammaAutoMomentBox steps k y us).lo : ℝ) := by
    exact_mod_cast hlo
  have hhiR : ((thetaGammaAutoMomentBox
      steps k y us).hi : ℝ) ≤
      ((thetaGammaRunningAutoMomentBox steps k y us).hi : ℝ) := by
    exact_mod_cast hhi
  exact ⟨hloR.trans hOld.1, hOld.2.trans hhiR⟩

end W5
