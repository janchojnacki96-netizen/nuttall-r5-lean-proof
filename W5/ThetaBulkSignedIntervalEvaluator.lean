import W5.ThetaBulkSignedMomentExpansion
import W5.VerifiedIntervalRealSemantics
import W5.ThetaAuditedMomentGammaCubicCellBox

/-!
# Exact rational SIGNED interval evaluator for every original theta n-term

All arithmetic in the signed double-binomial formula is encoded in
verified QInterval.add/mul/finsetSum/pow, never a floating-point
substitution or a positive absolute-value envelope. The only
additional numerical input is a rational enclosure for the
Gaussian exponential exp(-(n²-1)/x²).

This reuses PR #148's exact ORIGINAL signed integral equality,
the preexisting cubic-Gamma moment enclosures for arbitrary n,
the signed four-corner QInterval real semantics, and polynomial
coefficientPolynomial's original factorial definition.

No 48 separate theorem instantiations, and no new integral.
-/

namespace W5

/-- Exact original signed factorial coefficient as a rational. -/
def thetaBulkSignedFactor (i j : Fin 5) (t : ℕ) : ℚ :=
  ((-1:ℚ)^(i.val+j.val-t)) /
    ((Nat.factorial t : ℚ) *
      (Nat.factorial (i.val-t) : ℚ) *
      (Nat.factorial (j.val-t) : ℚ))

/-- One positive denominator/sign cast identity, reused in both
the base polynomial and the correction moment expansion. -/
private theorem thetaBulkSignedFactor_cast
    (i j : Fin 5) (t : ℕ) :
    (thetaBulkSignedFactor i j t : ℝ) =
      ((-1:ℝ)^(i.val+j.val-t)) /
        ((Nat.factorial t : ℝ) *
          (Nat.factorial (i.val-t) : ℝ) *
          (Nat.factorial (j.val-t) : ℝ)) := by
  simp only [thetaBulkSignedFactor, Rat.cast_div,
    Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_mul,
    Rat.cast_natCast]

/-- Interval for d=(n²-1)/x, valid when 0<a≤x≤b.
It is a single signed interval multiplication + the already
verified REAL reciprocal interval, not a new division algorithm. -/
def thetaBulkInverseAffineBox (a b : ℚ) (n : ℕ) : QInterval :=
  QInterval.mul
    (QInterval.point ((n:ℚ)^2-1))
    (QInterval.inversePositive ⟨a,b⟩)

theorem thetaBulkInverseAffineBox_containsReal
    (a b : ℚ) (n : ℕ) (x : ℝ)
    (ha : (0:ℚ) < a)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ)) :
    QInterval.ContainsReal (thetaBulkInverseAffineBox a b n)
      (((n:ℝ)^2-1)/x) := by
  have hX : QInterval.ContainsReal (⟨a,b⟩:QInterval) x :=
    ⟨hax,hxb⟩
  have hRec := QInterval.inversePositive_containsReal hX ha
  have hNum := thetaRationalPoint_containsReal ((n:ℚ)^2-1)
  have hProd := QInterval.mul_containsReal hNum hRec
  simpa only [thetaBulkInverseAffineBox, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_one,
    div_eq_mul_inv] using hProd

/-- A SIGNED endpoint enclosure for one original base polynomial.
Unlike the coarse thetaHeadPositiveMajorant, it keeps the
(-1)^(i+j-t) factor and hence the cancellation. -/
def thetaBulkSignedBasePolynomialBox
    (D : QInterval) (p : ℚ) (i j : Fin 5) : QInterval :=
  QInterval.finsetSum (Finset.range (min i.val j.val+1))
    (fun t =>
      QInterval.mul
        (QInterval.point (thetaBulkSignedFactor i j t))
        (QInterval.mul
          (QInterval.pow D (i.val+j.val-2*t))
          (QInterval.point (p^t))))

theorem thetaBulkSignedBasePolynomialBox_containsReal
    (D : QInterval) (p : ℚ) (d : ℝ)
    (hD : QInterval.ContainsReal D d)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaBulkSignedBasePolynomialBox D p i j)
      (coefficientPolynomial i j d (p:ℝ)) := by
  unfold coefficientPolynomial thetaBulkSignedBasePolynomialBox
  apply QInterval.finsetSum_containsReal
    (Finset.range (min i.val j.val+1))
    (fun t =>
      QInterval.mul
        (QInterval.point (thetaBulkSignedFactor i j t))
        (QInterval.mul
          (QInterval.pow D (i.val+j.val-2*t))
          (QInterval.point (p^t))))
    (fun t =>
      (((-1:ℝ)^(i.val+j.val-t) *
        d^(i.val+j.val-2*t) * (p:ℝ)^t) /
        ((Nat.factorial t : ℝ) *
          (Nat.factorial (i.val-t) : ℝ) *
          (Nat.factorial (j.val-t) : ℝ))))
    (by
      intro t ht
      have hf := thetaRationalPoint_containsReal
        (thetaBulkSignedFactor i j t)
      have hd := thetaRationalIntervalPow_containsReal
        D d hD (i.val+j.val-2*t)
      have hp := thetaRationalPoint_containsReal (p^t)
      have hprod := QInterval.mul_containsReal hf
        (QInterval.mul_containsReal hd hp)
      convert hprod using 1
      · rw [thetaBulkSignedFactor_cast]
        simp only [Rat.cast_pow]
        ring)

/-- One double-binomial/Gamma scalar summand in SIGNED
rational interval arithmetic. The moment M is an interval
enclosing a GENUINE weighted Gamma moment. -/
def thetaBulkSignedAffineMomentBox
    (D X : QInterval) (p : ℚ)
    (m t s u : ℕ) (M : QInterval) : QInterval :=
  QInterval.mul
    (QInterval.point
      ((m.choose s:ℚ) * (t.choose u:ℚ) * p^(t-u)))
    (QInterval.mul
      (QInterval.pow D (m-s))
      (QInterval.mul
        (QInterval.pow X (s+2*u)) M))

theorem thetaBulkSignedAffineMomentBox_containsReal
    (D X : QInterval) (p : ℚ)
    (d x moment : ℝ)
    (hD : QInterval.ContainsReal D d)
    (hX : QInterval.ContainsReal X x)
    (M : QInterval) (hM : QInterval.ContainsReal M moment)
    (m t s u : ℕ) :
    QInterval.ContainsReal
      (thetaBulkSignedAffineMomentBox D X p m t s u M)
      (((m.choose s:ℝ) * (t.choose u:ℝ) *
        d^(m-s) * x^s * (p:ℝ)^(t-u) * x^(2*u)) * moment) := by
  have hc := thetaRationalPoint_containsReal
    ((m.choose s:ℚ) * (t.choose u:ℚ) * p^(t-u))
  have hd := thetaRationalIntervalPow_containsReal D d hD (m-s)
  have hx := thetaRationalIntervalPow_containsReal X x hX (s+2*u)
  have hprod := QInterval.mul_containsReal hc
    (QInterval.mul_containsReal hd
      (QInterval.mul_containsReal hx hM))
  convert hprod using 1
  · simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    rw [pow_add]
    ring

/-- Exact finite rational interval evaluator of the original
SIGNED double-binomial weighted Gamma integral. This is a
computable formula, not an externally supplied endpoint matrix. -/
def thetaBulkSignedMomentInterval
    (D X : QInterval) (p : ℚ)
    (M : ℕ → QInterval) (i j : Fin 5) : QInterval :=
  QInterval.finsetSum (Finset.range (min i.val j.val+1))
    (fun t =>
      QInterval.mul
        (QInterval.point (thetaBulkSignedFactor i j t))
        (QInterval.finsetSum
          (Finset.range (i.val+j.val-2*t+1))
          (fun s =>
            QInterval.finsetSum (Finset.range (t+1))
              (fun u =>
                thetaBulkSignedAffineMomentBox
                  D X p (i.val+j.val-2*t) t s u (M (s+u))))))

/-- ONE generic proof that the computable signed rational
interval encloses the EXACT original correction integral.
Applies to all 25 entries and all square indices at once. -/
theorem thetaBulkSignedMomentInterval_containsReal
    (D X : QInterval) (p : ℚ)
    (M : ℕ → QInterval) (y d x : ℝ)
    (hD : QInterval.ContainsReal D d)
    (hX : QInterval.ContainsReal X x)
    (hM : ∀ k : ℕ,
      QInterval.ContainsReal (M k)
        (thetaAuditedOneWeightedMoment y k))
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaBulkSignedMomentInterval D X p M i j)
      (thetaSignedWeightedMomentExpansion y x d (p:ℝ) i j) := by
  unfold thetaSignedWeightedMomentExpansion thetaBulkSignedMomentInterval
  apply QInterval.finsetSum_containsReal
    (Finset.range (min i.val j.val+1))
    (fun t =>
      QInterval.mul
        (QInterval.point (thetaBulkSignedFactor i j t))
        (QInterval.finsetSum (Finset.range (i.val+j.val-2*t+1))
          (fun s =>
            QInterval.finsetSum (Finset.range (t+1))
              (fun u => thetaBulkSignedAffineMomentBox D X p
                (i.val+j.val-2*t) t s u (M (s+u))))))
    (fun t =>
      (((-1:ℝ)^(i.val+j.val-t)) /
        ((Nat.factorial t : ℝ) *
          (Nat.factorial (i.val-t) : ℝ) *
          (Nat.factorial (j.val-t) : ℝ))) *
        (∑ s ∈ Finset.range (i.val+j.val-2*t+1),
          ∑ u ∈ Finset.range (t+1),
            (((i.val+j.val-2*t).choose s : ℝ) *
              (t.choose u : ℝ) *
              d^(i.val+j.val-2*t-s) *
              x^s * (p:ℝ)^(t-u) * x^(2*u)) *
                thetaAuditedOneWeightedMoment y (s+u)))
    (by
      intro t ht
      have hsum :
          QInterval.ContainsReal
            (QInterval.finsetSum (Finset.range (i.val+j.val-2*t+1))
              (fun s =>
                QInterval.finsetSum (Finset.range (t+1))
                  (fun u => thetaBulkSignedAffineMomentBox
                    D X p (i.val+j.val-2*t) t s u (M (s+u)))))
            (∑ s ∈ Finset.range (i.val+j.val-2*t+1),
              ∑ u ∈ Finset.range (t+1),
                (((i.val+j.val-2*t).choose s : ℝ) *
                  (t.choose u : ℝ) *
                  d^(i.val+j.val-2*t-s) *
                  x^s * (p:ℝ)^(t-u) * x^(2*u)) *
                    thetaAuditedOneWeightedMoment y (s+u)) := by
        apply QInterval.finsetSum_containsReal
          (Finset.range (i.val+j.val-2*t+1))
          (fun s => QInterval.finsetSum (Finset.range (t+1))
            (fun u => thetaBulkSignedAffineMomentBox
              D X p (i.val+j.val-2*t) t s u (M (s+u))))
          (fun s => ∑ u ∈ Finset.range (t+1),
            (((i.val+j.val-2*t).choose s : ℝ) *
              (t.choose u : ℝ) *
              d^(i.val+j.val-2*t-s) *
              x^s * (p:ℝ)^(t-u) * x^(2*u)) *
                thetaAuditedOneWeightedMoment y (s+u))
          (by
            intro s hs
            apply QInterval.finsetSum_containsReal
              (Finset.range (t+1))
              (fun u => thetaBulkSignedAffineMomentBox
                D X p (i.val+j.val-2*t) t s u (M (s+u)))
              (fun u =>
                (((i.val+j.val-2*t).choose s : ℝ) *
                  (t.choose u : ℝ) *
                  d^(i.val+j.val-2*t-s) *
                  x^s * (p:ℝ)^(t-u) * x^(2*u)) *
                    thetaAuditedOneWeightedMoment y (s+u))
              (by
                intro u hu
                exact thetaBulkSignedAffineMomentBox_containsReal
                  D X p d x
                    (thetaAuditedOneWeightedMoment y (s+u))
                  hD hX (M (s+u)) (hM (s+u))
                  (i.val+j.val-2*t) t s u))
      have hf := thetaRationalPoint_containsReal
        (thetaBulkSignedFactor i j t)
      have htotal := QInterval.mul_containsReal hf hsum
      convert htotal using 1
      · rw [thetaBulkSignedFactor_cast])

/-- One finite fully computable signed n-th original theta box,
parameterized only by a rational Gaussian exponential interval.
The cubic Gamma moment box and reciprocal/polynomial arithmetic
are fixed by existing verified algorithms. -/
def thetaBulkSignedOriginalTermBox
    (a b : ℚ) (n : ℕ) (i j : Fin 5)
    (E : QInterval) : QInterval :=
  let D := thetaBulkInverseAffineBox a b n
  let X : QInterval := ⟨a,b⟩
  let p : ℚ := (n:ℚ)^2
  QInterval.sub
    (QInterval.mul (QInterval.point p)
      (QInterval.mul E (thetaBulkSignedBasePolynomialBox D p i j)))
    (QInterval.mul (thetaOneSquareCellScaleBox a b)
      (QInterval.mul E
        (thetaBulkSignedMomentInterval D X p
          (thetaNthCubicGammaMomentBox a b n) i j)))

/-- All 25 entries and n=2,...,6 share ONE correctness proof.
Only E's certified original Gaussian factor enclosure is supplied,
in addition to positive x-cell endpoints. -/
theorem thetaBulkSignedOriginalTermBox_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a)
    (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 0 < n)
    (E : QInterval)
    (hE : QInterval.ContainsReal E
      (Real.exp (-((n:ℝ)^2-1)/x^2))) :
    QInterval.ContainsReal
      (thetaBulkSignedOriginalTermBox a b n i j E)
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
  have haR : (0:ℝ) ≤ (a:ℝ) := by
    exact_mod_cast ha.le
  have hM : ∀ k : ℕ,
      QInterval.ContainsReal (thetaNthCubicGammaMomentBox a b n k)
        (thetaAuditedOneWeightedMoment y k) := by
    intro k
    exact thetaNthCubicGammaMomentBox_containsReal
      a b x haR hax hxb hb1 n k hn
  have hIntegral := thetaBulkSignedMomentInterval_containsReal
    D X p (thetaNthCubicGammaMomentBox a b n)
    y d x hD hX hM i j
  have hScale := thetaOneSquareCellScaleBox_containsReal
    a b x hax hxb
  have hCorr0 := QInterval.mul_containsReal hScale
    (QInterval.mul_containsReal hE hIntegral)
  have hCorr :
      QInterval.ContainsReal
        (QInterval.mul (thetaOneSquareCellScaleBox a b)
          (QInterval.mul E
            (thetaBulkSignedMomentInterval D X p
              (thetaNthCubicGammaMomentBox a b n) i j)))
        ((x^2/4)*Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaSignedWeightedMomentExpansion y x d (p:ℝ) i j) := by
    convert hCorr0 using 1
    · ring
  have hOut := QInterval.sub_containsReal hB hCorr
  rw [thetaAuditedSeriesTerm_eq_signed_moment_expansion
    x hx (hxb.trans hb1) i j n hn]
  simpa only [thetaBulkSignedOriginalTermBox, D, X, p, d, y,
    Rat.cast_pow, Rat.cast_natCast] using hOut

end W5
