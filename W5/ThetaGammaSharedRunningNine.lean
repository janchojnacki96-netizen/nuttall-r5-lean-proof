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

/-- Lookup a precomputed rational endpoint exponential, with a
definitionally correct fallback for endpoints not in the table. -/
def thetaGammaMemoExpLookup (f : ℚ → QInterval) :
    List (ℚ × QInterval) → ℚ → QInterval
  | [], t => f t
  | p :: ps, t =>
      if t = p.1 then p.2 else thetaGammaMemoExpLookup f ps t

theorem thetaGammaMemoExpLookup_map_eq (f : ℚ → QInterval)
    (xs : List ℚ) (t : ℚ) :
    thetaGammaMemoExpLookup f (xs.map (fun a => (a, f a))) t = f t := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : t = a
      · simp [thetaGammaMemoExpLookup, h]
      · simp [thetaGammaMemoExpLookup, h, ih]

/-- The expensive endpoint exponentials are evaluated once per grid,
not once for each shifted moment and each polynomial coefficient. -/
def thetaGammaMemoExp (us : List ℚ) : ℚ → QInterval :=
  let table := ((0:ℚ) :: us).map (fun t => (t, thetaGammaBinExpNegBox t))
  thetaGammaMemoExpLookup thetaGammaBinExpNegBox table

theorem thetaGammaMemoExp_eq (us : List ℚ) (t : ℚ) :
    thetaGammaMemoExp us t = thetaGammaBinExpNegBox t :=
  thetaGammaMemoExpLookup_map_eq _ _ _

/-- Degrees 0..11 suffice for k=0..8 and cubic envelopes.
Both endpoint exponentials and all twelve Gamma masses are materialized. -/
def thetaGammaMemoMass (E : ℚ → QInterval) (L U : ℚ) : ℕ → QInterval :=
  let eL := E L
  let eU := E U
  let cached : Array QInterval := Array.ofFn (fun k : Fin 12 =>
    thetaGammaBinMassBox k.val L U eL eU)
  fun k =>
    if hk : k < 12 then cached[k]'(by simpa [cached] using hk)
    else thetaGammaBinMassBox k L U eL eU

theorem thetaGammaMemoMass_eq (E : ℚ → QInterval)
    (L U : ℚ) (k : ℕ) :
    thetaGammaMemoMass E L U k = thetaGammaBinMassBox k L U (E L) (E U) := by
  by_cases hk : k < 12
  · simp [thetaGammaMemoMass, hk]
  · simp [thetaGammaMemoMass, hk]

def thetaGammaMemoSignedBin (M : ℕ → QInterval)
    (k N : ℕ) (c : Fin N → ℚ) : QInterval :=
  QInterval.finsetSum (Finset.univ : Finset (Fin N))
    (fun i => QInterval.mul (QInterval.point (c i)) (M (k+i.val)))

theorem thetaGammaMemoSignedBin_eq (E : ℚ → QInterval)
    (hE : ∀ t, E t = thetaGammaBinExpNegBox t)
    (L U : ℚ) (k N : ℕ) (c : Fin N → ℚ) :
    thetaGammaMemoSignedBin (thetaGammaMemoMass E L U) k N c =
      thetaGammaShiftedSignedBinBox k N c L U := by
  simp only [thetaGammaMemoSignedBin, thetaGammaShiftedSignedBinBox,
    thetaGammaMemoMass_eq, hE, thetaGammaCertifiedBinMassBox]

def thetaGammaMemoLowerNineBin (E : ℚ → QInterval)
    (steps : ℕ) (q L U : ℚ) : Fin 9 → QInterval :=
  let root := thetaGammaAutoRootGrid steps q L
  let M := thetaGammaMemoMass E L U
  fun k => QInterval.mul ⟨root.1, root.2⟩
    (thetaGammaMemoSignedBin M k.val 3
      (thetaGammaRecenteredLowerCoeffs (q/(1+q*L)) L))

def thetaGammaMemoUpperNineBin (E : ℚ → QInterval)
    (steps : ℕ) (q L U : ℚ) : Fin 9 → QInterval :=
  let root := thetaGammaAutoRootGrid steps q L
  let M := thetaGammaMemoMass E L U
  fun k => QInterval.mul ⟨root.1, root.2⟩
    (thetaGammaMemoSignedBin M k.val 4
      (thetaGammaRecenteredUpperCoeffs (q/(1+q*L)) L))

theorem thetaGammaMemoLowerNineBin_eq (E : ℚ → QInterval)
    (hE : ∀ t, E t = thetaGammaBinExpNegBox t)
    (steps : ℕ) (q L U : ℚ) :
    thetaGammaMemoLowerNineBin E steps q L U =
      thetaGammaLowerNineBin steps q L U := by
  funext k
  simp only [thetaGammaMemoLowerNineBin, thetaGammaLowerNineBin,
    thetaGammaLowerRootSignedBinBox, thetaGammaMemoSignedBin_eq E hE]

theorem thetaGammaMemoUpperNineBin_eq (E : ℚ → QInterval)
    (hE : ∀ t, E t = thetaGammaBinExpNegBox t)
    (steps : ℕ) (q L U : ℚ) :
    thetaGammaMemoUpperNineBin E steps q L U =
      thetaGammaUpperNineBin steps q L U := by
  funext k
  simp only [thetaGammaMemoUpperNineBin, thetaGammaUpperNineBin,
    thetaGammaUpperRootSignedBinBox, thetaGammaMemoSignedBin_eq E hE]

/-- Entire verified original Gamma moment at ONE rational y,
but with all nine k-values computed against shared root bins. -/
def thetaGammaRunningAutoMomentNine
    (steps : ℕ) (y : ℚ) (us : List ℚ) : Fin 9 → QInterval :=
  let E := thetaGammaMemoExp us
  let lower := thetaGammaRoundedNineBinSum
    (thetaGammaMemoLowerNineBin E steps (y^2)) 0 us
  let upper := thetaGammaRoundedNineBinSum
    (thetaGammaMemoUpperNineBin E steps (y^2)) 0 us
  let H := thetaGammaRationalLast 0 us
  let eH := E H
  fun k => QInterval.add
    ⟨(lower k).lo, (upper k).hi⟩
    ⟨0, eH.hi * (thetaGammaBinPolyQ k.val H +
      (y^2/4) * thetaGammaBinPolyQ (k.val+1) H)⟩

theorem thetaGammaRunningAutoMomentNine_apply
    (steps : ℕ) (y : ℚ) (us : List ℚ) (k : Fin 9) :
    thetaGammaRunningAutoMomentNine steps y us k =
      thetaGammaRunningAutoMomentBox steps k.val y us := by
  have hE := thetaGammaMemoExp_eq us
  have hL : thetaGammaMemoLowerNineBin (thetaGammaMemoExp us) steps (y^2) =
      thetaGammaLowerNineBin steps (y^2) := by
    funext L U
    exact thetaGammaMemoLowerNineBin_eq _ hE steps _ L U
  have hU : thetaGammaMemoUpperNineBin (thetaGammaMemoExp us) steps (y^2) =
      thetaGammaUpperNineBin steps (y^2) := by
    funext L U
    exact thetaGammaMemoUpperNineBin_eq _ hE steps _ L U
  simp only [thetaGammaRunningAutoMomentNine,
    thetaGammaRunningAutoMomentBox, hL, hU,
    thetaGammaMemoExp_eq, thetaGammaWeightedExactTailBox,
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
