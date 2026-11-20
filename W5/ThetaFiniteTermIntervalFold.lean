import W5.ThetaSeriesPrefixTailEnclosure

/-!
# Verified finite folding of the genuine theta series' term intervals

The independent 768-bit auditor bounds each explicitly evaluated
square-index term by an exact rational interval and adds these
intervals before adding an analytic tail enclosure.

This module proves the FINITE term-accumulation step for arbitrary
rational intervals using Mathlib's `Finset.sum_le_sum`, then connects
it to the original thetaCoefficient prefix/tail theorem from #126.

There is no floating-point arithmetic or duplication of interval
multiplication, signed division, or LDL proofs. Unlike an assumed
prefix bound, the new theorem accepts individual n-th-term interval
enclosures, which is the concrete proof target for formalizing the
Python auditor's exponential and weighted-moment calculations.

We do NOT claim that those termwise numerical enclosures or the
infinite tail estimates have yet been proved in Lean.
-/

namespace W5

namespace QInterval

/-- Exact finite addition of rational interval endpoints. -/
def finsetSum {α : Type*} (s : Finset α)
    (I : α → QInterval) : QInterval :=
  ⟨∑ k ∈ s, (I k).lo, ∑ k ∈ s, (I k).hi⟩

/-- A genuinely generic soundness statement for finite interval
sums of REAL numbers. It reuses Mathlib's monotonicity for finite
sums, rather than introducing a custom interval induction. -/
theorem finsetSum_containsReal {α : Type*}
    (s : Finset α) (I : α → QInterval) (f : α → ℝ)
    (h : ∀ k ∈ s, ContainsReal (I k) (f k)) :
    ContainsReal (finsetSum s I) (∑ k ∈ s, f k) := by
  have hlo :
      (∑ k ∈ s, ((I k).lo : ℝ)) ≤ ∑ k ∈ s, f k := by
    apply Finset.sum_le_sum
    intro k hk
    exact (h k hk).1
  have hhi :
      (∑ k ∈ s, f k) ≤ ∑ k ∈ s, ((I k).hi : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    exact (h k hk).2
  simpa only [ContainsReal, finsetSum, Rat.cast_sum] using
    (show
      (∑ k ∈ s, ((I k).lo : ℝ)) ≤ ∑ k ∈ s, f k ∧
      (∑ k ∈ s, f k) ≤ ∑ k ∈ s, ((I k).hi : ℝ) from
      ⟨hlo, hhi⟩)

end QInterval

/-- A fixed exact-rational enclosure for the first N square-index
contributions. Each J n can in turn be produced by the existing
verified rational interval arithmetic and analytic moment bounds. -/
def thetaAuditedPrefixInterval
    (N : ℕ) (J : ℕ → QInterval) : QInterval :=
  QInterval.finsetSum (Finset.range N) J

/-- Individual term enclosures imply an enclosure for the exact
finite original theta coefficient prefix. -/
theorem thetaAuditedPrefixInterval_containsReal
    (N : ℕ) (x : ℝ) (i j : Fin 5)
    (J : ℕ → QInterval)
    (hterm : ∀ n ∈ Finset.range N,
      QInterval.ContainsReal (J n) (thetaAuditedSeriesTerm x i j n)) :
    QInterval.ContainsReal (thetaAuditedPrefixInterval N J)
      (thetaAuditedPrefix N x i j) := by
  exact QInterval.finsetSum_containsReal
    (Finset.range N) J
    (fun n => thetaAuditedSeriesTerm x i j n) hterm

/-- FULL soundness of the finite n-term fold + rigorous remaining
infinite tail + checked inclusion inside a target rational interval.
The genuine thetaCoefficient, not a proxy, is the conclusion.

Still-open analytic inputs: each evaluated term's real enclosure,
summability of the correction series, and a real enclosure of the
infinite tail. The finite interval addition is proved here. -/
theorem thetaCoefficient_containsReal_of_termwise_bounds_and_tail
    (N : ℕ) (x : ℝ) (hx : 0 < x) (i j : Fin 5)
    (J : ℕ → QInterval) (C T : QInterval)
    (hc : Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x i j n))
    (hterm : ∀ n ∈ Finset.range N,
      QInterval.ContainsReal (J n) (thetaAuditedSeriesTerm x i j n))
    (htail : QInterval.ContainsReal T (thetaAuditedTail N x i j))
    (hlo : C.lo ≤
      (QInterval.add (thetaAuditedPrefixInterval N J) T).lo)
    (hhi : (QInterval.add
      (thetaAuditedPrefixInterval N J) T).hi ≤ C.hi) :
    QInterval.ContainsReal C (thetaCoefficient x i j) := by
  exact thetaCoefficient_containsReal_of_audited_prefix_tail
    N x hx i j C (thetaAuditedPrefixInterval N J) T
    hc (thetaAuditedPrefixInterval_containsReal
      N x i j J hterm) htail hlo hhi

end W5
