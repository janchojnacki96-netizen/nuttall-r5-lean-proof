import W5.ThetaBulk48GeneratedVerifier
import W5.ThetaGammaAutoCellMomentBox

/-!
# Parameterized signed original-theta term with certified Gamma moments

The existing signed double-binomial evaluator already accepts an arbitrary
moment generator for its correction integral. Its outer n-th term wrapper,
however, hard-coded the coarse cubic moment enclosure. This module removes
that restriction without changing the original base polynomial, Gaussian
factor, signed coefficients, or analytic identity.

One real-soundness theorem works for EVERY n > 0, every i,j : Fin 5,
and ANY supplied moment enclosures. A specialization below plugs in the
sharp recentered finite-grid plus exact exponential-tail Gamma moments
for the previously coarse n = 2,...,6 terms.

No new numerical assumption is trusted: the only numerical hypotheses
are the already-proved rational endpoint Boolean checks.
-/

namespace W5

/-- The original signed n-th theta summand, with an arbitrary
rational interval oracle for each TRUE Gamma moment. -/
def thetaBulkSignedParameterizedTermBox
    (a b : ℚ) (n : ℕ) (i j : Fin 5)
    (E : QInterval) (M : ℕ → QInterval) : QInterval :=
  let D := thetaBulkInverseAffineBox a b n
  let X : QInterval := ⟨a,b⟩
  let p : ℚ := (n:ℚ)^2
  QInterval.sub
    (QInterval.mul (QInterval.point p)
      (QInterval.mul E (thetaBulkSignedBasePolynomialBox D p i j)))
    (QInterval.mul (thetaOneSquareCellScaleBox a b)
      (QInterval.mul E
        (thetaBulkSignedMomentInterval D X p M i j)))

/-- Generic REAL soundness: the original n-th signed theta term is
enclosed for all 25 entries whenever each true Gamma moment is
enclosed. No special property of cubic or grid moments is assumed. -/
theorem thetaBulkSignedParameterizedTermBox_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a)
    (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 0 < n)
    (E : QInterval)
    (hE : QInterval.ContainsReal E
      (Real.exp (-((n:ℝ)^2-1)/x^2)))
    (M : ℕ → QInterval)
    (hM : ∀ k : ℕ,
      QInterval.ContainsReal (M k)
        (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k)) :
    QInterval.ContainsReal
      (thetaBulkSignedParameterizedTermBox a b n i j E M)
      (thetaAuditedSeriesTerm x i j n) := by
  let D := thetaBulkInverseAffineBox a b n
  let X : QInterval := ⟨a,b⟩
  let p : ℚ := (n:ℚ)^2
  let d : ℝ := ((n:ℝ)^2-1)/x
  let y : ℝ := x/(n:ℝ)
  have hD : QInterval.ContainsReal D d :=
    thetaBulkInverseAffineBox_containsReal a b n x ha hax hxb
  have hX : QInterval.ContainsReal X x := ⟨hax,hxb⟩
  have hp : (p:ℝ) = (n:ℝ)^2 := by
    simp only [p, Rat.cast_pow, Rat.cast_natCast]
  have hcoef := thetaBulkSignedBasePolynomialBox_containsReal
    D p d hD i j
  have hB0 := QInterval.mul_containsReal
    (thetaRationalPoint_containsReal p)
    (QInterval.mul_containsReal hE hcoef)
  have hB :
      QInterval.ContainsReal
        (QInterval.mul (QInterval.point p)
          (QInterval.mul E (thetaBulkSignedBasePolynomialBox D p i j)))
        (thetaCertificateBaseTerm x i j n) := by
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    simpa only [thetaCertificateBaseTerm, if_neg hn0,
      hp, d, mul_assoc] using hB0
  have hIntegral := thetaBulkSignedMomentInterval_containsReal
    D X p M y d x hD hX (fun k => hM k) i j
  have hScale := thetaOneSquareCellScaleBox_containsReal
    a b x hax hxb
  have hCorr0 := QInterval.mul_containsReal hScale
    (QInterval.mul_containsReal hE hIntegral)
  have hCorr :
      QInterval.ContainsReal
        (QInterval.mul (thetaOneSquareCellScaleBox a b)
          (QInterval.mul E
            (thetaBulkSignedMomentInterval D X p M i j)))
        ((x^2/4)*Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaSignedWeightedMomentExpansion y x d (p:ℝ) i j) := by
    convert hCorr0 using 1
    · ring
  have hOut := QInterval.sub_containsReal hB hCorr
  rw [thetaAuditedSeriesTerm_eq_signed_moment_expansion
    x hx (hxb.trans hb1) i j n hn]
  simpa only [thetaBulkSignedParameterizedTermBox, D, X, p, d, y,
    Rat.cast_pow, Rat.cast_natCast] using hOut

/-- A direct specialization using the fully certified finite Gamma
grid and the exact exponential tail at BOTH rational x-cell endpoints.
This works for arbitrary n and k, not just the first square. -/
def thetaBulkSharpHigherSquareTermBox
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  thetaBulkSignedParameterizedTermBox a b n i j
    (thetaBulkFixedGaussianExpBox a b n)
    (fun k => thetaGammaAutoCellMomentBox steps k a b n us)

/-- Uniform real soundness for the original sharp Gamma n-th
term: the n = 2,...,6 Gaussian factor and BOTH moment endpoint
checks are independently decidable exact-rational requirements. -/
theorem thetaBulkSharpHigherSquareTermBox_containsReal
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (i j : Fin 5) (n : ℕ)
    (hn2 : 2 ≤ n) (hn7 : n < 7)
    (hA : thetaGammaAutoMomentCheck
      steps (a/(n:ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b/(n:ℚ)) us = true) :
    QInterval.ContainsReal
      (thetaBulkSharpHigherSquareTermBox steps us a b i j n)
      (thetaAuditedSeriesTerm x i j n) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hEl := hExp ⟨n, hn7⟩ hn2
  have hE := thetaBulkFixedGaussianExpBox_containsReal
    a b x n ha hax hxb hn2 hEl.1 hEl.2
  have hMom : ∀ k : ℕ,
      QInterval.ContainsReal
        (thetaGammaAutoCellMomentBox steps k a b n us)
        (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
    intro k
    exact thetaGammaAutoCellMomentBox_containsReal
      steps k a b n us x ha.le (by omega)
      hax hxb hb1 hA hB
  exact thetaBulkSignedParameterizedTermBox_containsReal
    a b x ha hx hax hxb hb1 i j n (by omega)
    (thetaBulkFixedGaussianExpBox a b n) hE
    (fun k => thetaGammaAutoCellMomentBox steps k a b n us)
    hMom

end W5
