import W5.ThetaBulkParameterizedGammaTerm

/-!
# Share the nine certified Gamma moment boxes across signed expansions

A naive evaluation of the original signed double-binomial formula
recomputes the SAME expensive rational Gamma-grid moment once per
appearance in the polynomial expansion, and once more for each matrix
entry. A 9-element array caches all moment degrees needed by
the 5x5 signed correction (k = 0,...,8).

The array is a pure implementation detail: the pointwise equality
below proves that the cached oracle returns PRECISELY the same
rational interval as the already-certified gamma generator, for
EVERY k including k >= 9. Therefore the existing exact-real
soundness theorem transfers without any new analytic assumption.

The evaluation optimization is separate from the formal proof and
does not assert any numerical fifth-pivot result.
-/

namespace W5

/-- Cache the first nine exact-rational Gamma-grid moment intervals
once; degrees >=9 fall back to the original evaluator. -/
def thetaGammaMemoNine (steps : ℕ) (a b : ℚ)
    (n : ℕ) (us : List ℚ) : ℕ → QInterval :=
  let cached : Array QInterval :=
    Array.ofFn (fun k : Fin 9 =>
      thetaGammaAutoCellMomentBox steps k.val a b n us)
  fun k =>
    if hk : k < 9 then
      cached[k]'(by simpa [cached] using hk)
    else thetaGammaAutoCellMomentBox steps k a b n us

/-- An exact equality, not merely a wider numerical enclosure.
This makes all the existing real-soundness theorems reusable. -/
theorem thetaGammaMemoNine_eq (steps : ℕ)
    (a b : ℚ) (n : ℕ) (us : List ℚ) (k : ℕ) :
    thetaGammaMemoNine steps a b n us k =
      thetaGammaAutoCellMomentBox steps k a b n us := by
  by_cases hk : k < 9
  · simp [thetaGammaMemoNine, hk]
  · simp [thetaGammaMemoNine, hk]

/-- The genuinely unchanged original n-th signed theta term,
with cached exact Gamma moments and the same certified exponential. -/
def thetaBulkMemoSharpHigherSquareTermBox
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  thetaBulkSignedParameterizedTermBox a b n i j
    (thetaBulkFixedGaussianExpBox a b n)
    (thetaGammaMemoNine steps a b n us)

/-- Pointwise extensional equality of all Gamma moment requests
proves that the cached and original n-th interval expressions
are EXACTLY equal, with no extra rounding or tolerance. -/
theorem thetaBulkMemoSharpHigherSquareTermBox_eq
    (steps : ℕ) (us : List ℚ) (a b : ℚ)
    (i j : Fin 5) (n : ℕ) :
    thetaBulkMemoSharpHigherSquareTermBox steps us a b i j n =
      thetaBulkSharpHigherSquareTermBox steps us a b i j n := by
  have hM :
      thetaGammaMemoNine steps a b n us =
        (fun k => thetaGammaAutoCellMomentBox steps k a b n us) := by
    funext k
    exact thetaGammaMemoNine_eq steps a b n us k
  simp only [thetaBulkMemoSharpHigherSquareTermBox,
    thetaBulkSharpHigherSquareTermBox, hM]

/-- The existing genuine-real Gamma and Gaussian soundness theorem
carries over literally, without repeating its analytic proof. -/
theorem thetaBulkMemoSharpHigherSquareTermBox_containsReal
    (steps : ℕ) (us : List ℚ) (a b : ℚ) (x : ℝ)
    (ha : (0 : ℚ) < a) (hx : 0 < x)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ (145 : ℝ) / 256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (i j : Fin 5) (n : ℕ)
    (hn2 : 2 ≤ n) (hn7 : n < 7)
    (hA : thetaGammaAutoMomentCheck
      steps (a/(n:ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b/(n:ℚ)) us = true) :
    QInterval.ContainsReal
      (thetaBulkMemoSharpHigherSquareTermBox steps us a b i j n)
      (thetaAuditedSeriesTerm x i j n) := by
  rw [thetaBulkMemoSharpHigherSquareTermBox_eq]
  exact thetaBulkSharpHigherSquareTermBox_containsReal
    steps us a b x ha hx hax hxb hb hExp i j n
    hn2 hn7 hA hB

/-- Construct the entire n-th 5x5 matrix with ONE shared
nine-moment array and ONE Gaussian exponential interval. The
mathematical entry formula is identical to the original term box;
the outer let-bindings avoid recomputing Gamma-grid quadratures
for every independent coefficient. -/
def thetaBulkMemoSharpHigherSquareMatrix
    (steps : ℕ) (us : List ℚ) (a b : ℚ)
    (n : ℕ) : ThetaIntervalMatrix :=
  let E := thetaBulkFixedGaussianExpBox a b n
  let M := thetaGammaMemoNine steps a b n us
  Matrix.of (fun i j =>
    thetaBulkSignedParameterizedTermBox a b n i j E M)

/-- Exact equality of each entry, proved using the existing
pointwise cached-term equality. No extra numerical checker. -/
theorem thetaBulkMemoSharpHigherSquareMatrix_apply
    (steps : ℕ) (us : List ℚ) (a b : ℚ)
    (n : ℕ) (i j : Fin 5) :
    thetaBulkMemoSharpHigherSquareMatrix steps us a b n i j =
      thetaBulkSharpHigherSquareTermBox steps us a b i j n := by
  change thetaBulkMemoSharpHigherSquareTermBox
      steps us a b i j n =
    thetaBulkSharpHigherSquareTermBox steps us a b i j n
  exact thetaBulkMemoSharpHigherSquareTermBox_eq
    steps us a b i j n

/-- The original real-soundness result transfers to the entire
shared-array matrix without copying any analytic derivative,
Gamma-integral or signed-polynomial proof. -/
theorem thetaBulkMemoSharpHigherSquareMatrix_containsReal
    (steps : ℕ) (us : List ℚ) (a b : ℚ) (x : ℝ)
    (ha : (0 : ℚ) < a) (hx : 0 < x)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ (145 : ℝ) / 256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (n : ℕ) (hn2 : 2 ≤ n) (hn7 : n < 7)
    (hA : thetaGammaAutoMomentCheck
      steps (a/(n:ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b/(n:ℚ)) us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaBulkMemoSharpHigherSquareMatrix steps us a b n i j)
      (thetaAuditedSeriesTerm x i j n) := by
  rw [thetaBulkMemoSharpHigherSquareMatrix_apply]
  exact thetaBulkSharpHigherSquareTermBox_containsReal
    steps us a b x ha hx hax hxb hb hExp i j n
    hn2 hn7 hA hB

end W5
