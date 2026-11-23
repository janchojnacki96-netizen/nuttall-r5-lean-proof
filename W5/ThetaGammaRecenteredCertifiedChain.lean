import W5.ThetaGammaRecenteredCertifiedBin
import W5.ThetaGammaArbitraryBinChain

/-!
# One REAL certificate over an arbitrarily fine rational Gamma grid

This module composes, without repeating their proofs:
* one exact rational lower/upper signed Gamma enclosure per bin;
* QInterval.add_containsReal, including negative coefficients;
* the Mathlib-backed arbitrary-bin real integral chain.

A single induction handles every k and any rational list of w-bins.
The result is a genuine enclosure of the ORIGINAL truncated weighted
Gamma moment integral, not just the polynomial envelope.
-/

namespace W5

/-- Eligibility of an entire finite rational w-partition, with one
rational fourth-root interval R L for each local recentering origin. -/
def thetaGammaRootGridEligible (q : ℚ) (R : ℚ → ℚ × ℚ) :
    ℚ → List ℚ → Prop
  | L, [] => 0 ≤ L
  | L, U :: us =>
      thetaGammaCertifiedBinEligible L U ∧
      0 ≤ (R L).1 ∧ 0 ≤ (R L).2 ∧
      (R L).1^4 ≤ 1+q*L ∧ 1+q*L ≤ (R L).2^4 ∧
      thetaGammaRootGridEligible q R U us

/-- One constructive decision procedure for eligibility of an
arbitrary-length rational Gamma grid. The recursion is on the list,
and each local requirement uses exact decidable rational inequalities. -/
def thetaGammaRootGridEligible_decidable (q : ℚ)
    (R : ℚ → ℚ × ℚ) :
    ∀ (L : ℚ) (us : List ℚ),
      Decidable (thetaGammaRootGridEligible q R L us)
  | L, [] => by
      change Decidable ((0:ℚ) ≤ L)
      infer_instance
  | L, U :: us => by
      change Decidable
        (thetaGammaCertifiedBinEligible L U ∧
          0 ≤ (R L).1 ∧ 0 ≤ (R L).2 ∧
          (R L).1^4 ≤ 1+q*L ∧ 1+q*L ≤ (R L).2^4 ∧
          thetaGammaRootGridEligible q R U us)
      letI : Decidable (thetaGammaRootGridEligible q R U us) :=
        thetaGammaRootGridEligible_decidable q R U us
      infer_instance

instance thetaGammaRootGridEligible_instDecidable
    (q : ℚ) (R : ℚ → ℚ × ℚ) (L : ℚ) (us : List ℚ) :
    Decidable (thetaGammaRootGridEligible q R L us) :=
  thetaGammaRootGridEligible_decidable q R L us

/-- Computable sum of rational intervals enclosing the true
quadratic-LOWER recentered integrals over a w-grid. -/
def thetaGammaLowerGridBox (k : ℕ) (q : ℚ)
    (R : ℚ → ℚ × ℚ) : ℚ → List ℚ → QInterval
  | _, [] => QInterval.point 0
  | L, U :: us =>
      QInterval.add
        (thetaGammaLowerRootSignedBinBox k q L U (R L).1 (R L).2)
        (thetaGammaLowerGridBox k q R U us)

/-- Computable sum of rational intervals enclosing the true
cubic-UPPER recentered integrals over the same w-grid. -/
def thetaGammaUpperGridBox (k : ℕ) (q : ℚ)
    (R : ℚ → ℚ × ℚ) : ℚ → List ℚ → QInterval
  | _, [] => QInterval.point 0
  | L, U :: us =>
      QInterval.add
        (thetaGammaUpperRootSignedBinBox k q L U (R L).1 (R L).2)
        (thetaGammaUpperGridBox k q R U us)

/-- The lower grid certificate encloses the ACTUAL sum of local
lower-root Gamma integrals. No finite numerical tables are assumed. -/
theorem thetaGammaLowerGridBox_containsReal
    (k : ℕ) (q : ℚ) (R : ℚ → ℚ × ℚ)
    (hq : 0 ≤ q) :
    ∀ (L : ℚ) (us : List ℚ),
      thetaGammaRootGridEligible q R L us →
      QInterval.ContainsReal (thetaGammaLowerGridBox k q R L us)
        (thetaGammaBinLowerChain (q:ℝ) k (L:ℝ)
          (us.map (fun x : ℚ => (x:ℝ)))) := by
  intro L us
  induction us generalizing L with
  | nil =>
      intro _
      simp [thetaGammaLowerGridBox, thetaGammaBinLowerChain,
        QInterval.ContainsReal, QInterval.point]
  | cons U us ih =>
      intro h
      rcases h with ⟨hEligible, hl, hu, hlo, hhi, hrest⟩
      have hbin :=
        thetaGammaLowerRootSignedBinBox_containsReal
          k q L U (R L).1 (R L).2
          hq hEligible.1 hEligible hl hu hlo hhi
      have htail := ih U hrest
      change QInterval.ContainsReal
        (QInterval.add
          (thetaGammaLowerRootSignedBinBox k q L U (R L).1 (R L).2)
          (thetaGammaLowerGridBox k q R U us))
        ((∫ w in (L:ℝ)..(U:ℝ),
            thetaGammaBinDensity k w *
              thetaGammaBinLowerRoot (q:ℝ) (L:ℝ) w) +
          thetaGammaBinLowerChain (q:ℝ) k (U:ℝ)
            (us.map (fun x : ℚ => (x:ℝ))))
      exact QInterval.add_containsReal hbin htail

/-- Same uniform REAL certificate for the cubic-upper integral chain. -/
theorem thetaGammaUpperGridBox_containsReal
    (k : ℕ) (q : ℚ) (R : ℚ → ℚ × ℚ)
    (hq : 0 ≤ q) :
    ∀ (L : ℚ) (us : List ℚ),
      thetaGammaRootGridEligible q R L us →
      QInterval.ContainsReal (thetaGammaUpperGridBox k q R L us)
        (thetaGammaBinUpperChain (q:ℝ) k (L:ℝ)
          (us.map (fun x : ℚ => (x:ℝ)))) := by
  intro L us
  induction us generalizing L with
  | nil =>
      intro _
      simp [thetaGammaUpperGridBox, thetaGammaBinUpperChain,
        QInterval.ContainsReal, QInterval.point]
  | cons U us ih =>
      intro h
      rcases h with ⟨hEligible, hl, hu, hlo, hhi, hrest⟩
      have hbin :=
        thetaGammaUpperRootSignedBinBox_containsReal
          k q L U (R L).1 (R L).2
          hq hEligible.1 hEligible hl hu hlo hhi
      have htail := ih U hrest
      change QInterval.ContainsReal
        (QInterval.add
          (thetaGammaUpperRootSignedBinBox k q L U (R L).1 (R L).2)
          (thetaGammaUpperGridBox k q R U us))
        ((∫ w in (L:ℝ)..(U:ℝ),
            thetaGammaBinDensity k w *
              thetaGammaBinUpperRoot (q:ℝ) (L:ℝ) w) +
          thetaGammaBinUpperChain (q:ℝ) k (U:ℝ)
            (us.map (fun x : ℚ => (x:ℝ))))
      exact QInterval.add_containsReal hbin htail

/-- The rational-grid eligibility conditions imply exactly the
nonnegative monotone REAL endpoint conditions of the existing
arbitrary Gamma-bin chain theorem. -/
theorem thetaGammaRootGridEligible_increasing
    (q : ℚ) (R : ℚ → ℚ × ℚ) :
    ∀ (L : ℚ) (us : List ℚ),
      thetaGammaRootGridEligible q R L us →
      thetaGammaBinIncreasing (L:ℝ)
        (us.map (fun x : ℚ => (x:ℝ))) := by
  intro L us
  induction us generalizing L with
  | nil =>
      intro h
      change 0 ≤ (L:ℝ)
      exact_mod_cast h
  | cons U us ih =>
      intro h
      rcases h with ⟨hEligible, _, _, _, _, hrest⟩
      change 0 ≤ (L:ℝ) ∧ (L:ℝ) ≤ (U:ℝ) ∧
        thetaGammaBinIncreasing (U:ℝ)
          (us.map (fun x : ℚ => (x:ℝ)))
      exact ⟨by exact_mod_cast hEligible.1,
        by exact_mod_cast hEligible.2.1, ih U hrest⟩

/-- SINGLE sound truncated moment enclosure on an arbitrary rational
grid. The lower/upper endpoints are generated, not handwritten.
After adding the existing certified infinite-tail bound this gives
the complete endpoint-Gamma moment interval for every theta cell. -/
theorem thetaGammaOriginalTruncatedGrid_containsReal
    (k : ℕ) (q : ℚ) (R : ℚ → ℚ × ℚ)
    (L : ℚ) (us : List ℚ)
    (hq : 0 ≤ q)
    (hgrid : thetaGammaRootGridEligible q R L us) :
    QInterval.ContainsReal
      ⟨(thetaGammaLowerGridBox k q R L us).lo,
        (thetaGammaUpperGridBox k q R L us).hi⟩
      (∫ w in (L:ℝ)..thetaGammaBinLast (L:ℝ)
            (us.map (fun x : ℚ => (x:ℝ))),
        thetaGammaBinDensity k w *
          thetaGammaBinOriginalRoot (q:ℝ) w) := by
  have hL :=
    thetaGammaLowerGridBox_containsReal k q R hq L us hgrid
  have hU :=
    thetaGammaUpperGridBox_containsReal k q R hq L us hgrid
  have hmono := thetaGammaRootGridEligible_increasing q R L us hgrid
  have hqR : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hbounds :=
    thetaGammaBinArbitraryChain_bounds
      (q:ℝ) k hqR (L:ℝ)
      (us.map (fun x : ℚ => (x:ℝ))) hmono
  exact ⟨hL.1.trans hbounds.1, hbounds.2.trans hU.2⟩

end W5
