import W5.ThetaGammaRecenteredBinIntegral

/-!
# One arbitrarily fine Gamma integration partition theorem

The pointwise proof for a single finite w-bin is already verified.
This module uses exactly Mathlib's existing adjacent-interval
integral identity to propagate that real-sound lower/upper bound
to ANY finite LIST of w-bin endpoints in one induction.

No "one PR per cell", no new Gamma integral, and no extra analytic
assumptions. Refining the w-grid to gain accuracy no longer changes
the mathematical formalization workload.

For the original infinite weighted Gamma moment, the remaining
analytic step is one uniform bound on the w>H tail. The finite
truncated domain is completely covered by this one chain theorem.
-/

namespace W5

/-- Final endpoint of any finite list of consecutive w-bins. -/
def thetaGammaBinLast : ℝ → List ℝ → ℝ
  | L, [] => L
  | _, U :: us => thetaGammaBinLast U us

/-- All w-bin endpoints are nonnegative and nondecreasing. -/
def thetaGammaBinIncreasing : ℝ → List ℝ → Prop
  | L, [] => 0 ≤ L
  | L, U :: us =>
      0 ≤ L ∧ L ≤ U ∧ thetaGammaBinIncreasing U us

/-- Sum of the recentered quadratic LOWER integral over the bins.
Integrals are genuine Lebesgue/interval integrals, not generated
numerical numbers. -/
noncomputable def thetaGammaBinLowerChain
    (q : ℝ) (k : ℕ) : ℝ → List ℝ → ℝ
  | _, [] => 0
  | L, U :: us =>
      (∫ w in L..U,
        thetaGammaBinDensity k w *
          thetaGammaBinLowerRoot q L w) +
        thetaGammaBinLowerChain q k U us

/-- Sum of the recentered cubic UPPER integral over the bins. -/
noncomputable def thetaGammaBinUpperChain
    (q : ℝ) (k : ℕ) : ℝ → List ℝ → ℝ
  | _, [] => 0
  | L, U :: us =>
      (∫ w in L..U,
        thetaGammaBinDensity k w *
          thetaGammaBinUpperRoot q L w) +
        thetaGammaBinUpperChain q k U us

/-- ONE real-semantic proof covering any number of consecutive
w-bins: the true original truncated Gamma moment is sandwiched
between the sums of the local quadratic/cubic envelopes.

The proof ONLY reuses:
* the verified local original integral lower/upper theorem;
* Mathlib's integral_add_adjacent_intervals;
* induction on the endpoint list.
-/
theorem thetaGammaBinArbitraryChain_bounds
    (q : ℝ) (k : ℕ) (hq : 0 ≤ q) :
    ∀ (L : ℝ) (us : List ℝ),
      thetaGammaBinIncreasing L us →
      thetaGammaBinLowerChain q k L us ≤
        (∫ w in L..thetaGammaBinLast L us,
          thetaGammaBinDensity k w *
            thetaGammaBinOriginalRoot q w) ∧
      (∫ w in L..thetaGammaBinLast L us,
          thetaGammaBinDensity k w *
            thetaGammaBinOriginalRoot q w) ≤
        thetaGammaBinUpperChain q k L us := by
  intro L us
  induction us generalizing L with
  | nil =>
      intro _
      simp [thetaGammaBinLast,
        thetaGammaBinLowerChain, thetaGammaBinUpperChain]
  | cons U us ih =>
      intro hmono
      change 0 ≤ L ∧ L ≤ U ∧
        thetaGammaBinIncreasing U us at hmono
      rcases hmono with ⟨hL, hLU, hrest⟩
      have hBin :=
        thetaGammaBinWeightedIntegral_bounds q L U k hq hL hLU
      have hChain := ih U hrest
      have hMid : Continuous (fun w : ℝ =>
          thetaGammaBinDensity k w *
            thetaGammaBinOriginalRoot q w) :=
        (thetaGammaBinDensity_continuous k).mul
          (thetaGammaBinOriginalRoot_continuous q)
      have hSplit :
          (∫ w in L..thetaGammaBinLast U us,
            thetaGammaBinDensity k w *
              thetaGammaBinOriginalRoot q w) =
          (∫ w in L..U,
            thetaGammaBinDensity k w *
              thetaGammaBinOriginalRoot q w) +
          (∫ w in U..thetaGammaBinLast U us,
            thetaGammaBinDensity k w *
              thetaGammaBinOriginalRoot q w) :=
        intervalIntegral.integral_add_adjacent_intervals
          (hMid.intervalIntegrable L U)
          (hMid.intervalIntegrable U (thetaGammaBinLast U us)) |>.symm
      change
        (∫ w in L..U, thetaGammaBinDensity k w *
          thetaGammaBinLowerRoot q L w) +
            thetaGammaBinLowerChain q k U us ≤
          (∫ w in L..thetaGammaBinLast U us,
            thetaGammaBinDensity k w *
              thetaGammaBinOriginalRoot q w) ∧
        (∫ w in L..thetaGammaBinLast U us,
          thetaGammaBinDensity k w *
            thetaGammaBinOriginalRoot q w) ≤
          (∫ w in L..U, thetaGammaBinDensity k w *
            thetaGammaBinUpperRoot q L w) +
            thetaGammaBinUpperChain q k U us
      rw [hSplit]
      exact ⟨add_le_add hBin.1 hChain.1,
        add_le_add hBin.2 hChain.2⟩

end W5
