import W5.ThetaGammaRunningCellMoments

/-!
# One shared fourth-root grid for all nine Gamma moment degrees

The original running-interval evaluator recomputed each expensive
fourth-root chord/tangent bound separately for k=0,...,8.
The root bound on a fixed w-bin depends on (steps,q,L), NOT k.

Here a vector of nine independently certified moment intervals is
accumulated in ONE recursion over the w-grid. Each bin computes
the common root bounds once, then all nine k-specific bins reuse them.

The exact original 768-bit rounded interval for every k<9 is
definitionally the SAME as in the original scalar implementation.
This proof is independent of the numerical grid and requires no
new analytic integration or assumptions about the original theta.
-/

namespace W5

/-- A vectorized version of the already-certified rounded grid
recursion, parameterized by any per-bin family of nine intervals. -/
def thetaGammaRoundedNineBinSum
    (f : ℚ → ℚ → Fin 9 → QInterval) :
    ℚ → List ℚ → Fin 9 → QInterval
  | _, [] => fun _ => QInterval.point 0
  | a, b :: bs =>
      let tail := thetaGammaRoundedNineBinSum f b bs
      let bin := f a b
      fun k => thetaBulkRoundedQInterval
        (QInterval.add (bin k) (tail k))

/-- Every one of the nine vector entries is EXACTLY the previously
certified scalar running sum, not merely a wider enclosure. -/
theorem thetaGammaRoundedNineBinSum_apply
    (f : ℚ → ℚ → Fin 9 → QInterval) :
    ∀ (a : ℚ) (bs : List ℚ) (k : Fin 9),
      thetaGammaRoundedNineBinSum f a bs k =
        thetaGammaRoundedBinSum
          (fun a b => f a b k) a bs := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      intro k
      rfl
  | cons b bs ih =>
      intro k
      change thetaBulkRoundedQInterval
        (QInterval.add (f a b k)
          (thetaGammaRoundedNineBinSum f b bs k)) =
        thetaBulkRoundedQInterval
          (QInterval.add (f a b k)
            (thetaGammaRoundedBinSum (fun a b => f a b k) b bs))
      rw [ih b k]

/-- Compute the expensive common root bound ONCE per left w-endpoint
and reuse it for all nine k-specific lower signed bin intervals. -/
def thetaGammaLowerNineBin
    (steps : ℕ) (q L U : ℚ) : Fin 9 → QInterval :=
  let root := thetaGammaAutoRootGrid steps q L
  fun k => thetaGammaLowerRootSignedBinBox k.val q L U
    root.1 root.2

def thetaGammaUpperNineBin
    (steps : ℕ) (q L U : ℚ) : Fin 9 → QInterval :=
  let root := thetaGammaAutoRootGrid steps q L
  fun k => thetaGammaUpperRootSignedBinBox k.val q L U
    root.1 root.2

theorem thetaGammaLowerNineBin_apply
    (steps : ℕ) (q L U : ℚ) (k : Fin 9) :
    thetaGammaLowerNineBin steps q L U k =
      thetaGammaLowerRunningBin steps k.val q L U := by
  rfl

theorem thetaGammaUpperNineBin_apply
    (steps : ℕ) (q L U : ℚ) (k : Fin 9) :
    thetaGammaUpperNineBin steps q L U k =
      thetaGammaUpperRunningBin steps k.val q L U := by
  rfl

/-- Entire verified original Gamma moment at ONE rational y,
but with all nine k-values computed against shared root bins. -/
def thetaGammaRunningAutoMomentNine
    (steps : ℕ) (y : ℚ) (us : List ℚ) : Fin 9 → QInterval :=
  let lower := thetaGammaRoundedNineBinSum
    (thetaGammaLowerNineBin steps (y^2)) 0 us
  let upper := thetaGammaRoundedNineBinSum
    (thetaGammaUpperNineBin steps (y^2)) 0 us
  fun k => QInterval.add
    ⟨(lower k).lo, (upper k).hi⟩
    (thetaGammaWeightedExactTailBox k.val y
      (thetaGammaRationalLast 0 us))

theorem thetaGammaRunningAutoMomentNine_apply
    (steps : ℕ) (y : ℚ) (us : List ℚ) (k : Fin 9) :
    thetaGammaRunningAutoMomentNine steps y us k =
      thetaGammaRunningAutoMomentBox steps k.val y us := by
  simp only [thetaGammaRunningAutoMomentNine,
    thetaGammaRunningAutoMomentBox,
    thetaGammaRoundedNineBinSum_apply,
    thetaGammaLowerNineBin_apply,
    thetaGammaUpperNineBin_apply]

/-- Share each endpoint's fourth-root grid over all nine moments.
The final cell enclosure uses the SAME verified old rounding. -/
def thetaGammaRunningCellNine
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) : Fin 9 → QInterval :=
  let left := thetaGammaRunningAutoMomentNine
    steps (a/(n:ℚ)) us
  let right := thetaGammaRunningAutoMomentNine
    steps (b/(n:ℚ)) us
  fun k => thetaBulkRoundedQInterval
    ⟨(left k).lo, (right k).hi⟩

/-- Equality, not a new analytic estimate: unchanged REAL theta
moment enclosure follows from the existing soundness lemma. -/
theorem thetaGammaRunningCellNine_apply
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (k : Fin 9) :
    thetaGammaRunningCellNine steps a b n us k =
      thetaGammaRunningRoundedCellMomentBox
        steps k.val a b n us := by
  simp only [thetaGammaRunningCellNine,
    thetaGammaRunningRoundedCellMomentBox,
    thetaGammaRunningAutoCellMomentBox,
    thetaGammaRunningAutoMomentNine_apply]

end W5
