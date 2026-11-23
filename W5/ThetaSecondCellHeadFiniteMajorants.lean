import W5.ThetaSecondCellAllEntriesTailFour

/-!
# Second-cell n=2 and n=3: one finite rational majorant

The only remaining non-Gaussian-negligible indices on cell 2 are 2
and 3. Split the original cell into [1/8, 1/4] and [1/4,177/512].

For p=n², D=(p-1)/a, this computable expression is the positive
binomial/Gamma upper bound for the original base+correction summands
once the real-semantic monotonicity is proved:
  |T_n(x)| <= exp(-(n²-1)/x²) * K(a,b,n,i,j).

The finite rational inequalities below are genuinely decidable and
DO NOT themselves prove the analytic domination theorem. This is
designed as a single sound interface for ALL i,j:Fin5, with no
bespoke entrywise proof and no extra exponential Taylor library.

Use existing Mathlib factorial Gamma integrals to discharge the
analytic bridge in the next module.
-/

namespace W5

/-- Gamma factorial moment of the quarter-root tangent upper
bound at parameter x/n, uniformly for x<=b. -/
def thetaHeadMomentUpper (b : ℚ) (n k : ℕ) : ℚ :=
  (Nat.factorial k : ℚ) +
    (b^2 / (4*(n:ℚ)^2)) * (Nat.factorial (k+1) : ℚ)

/-- One positive binomial term: expand both original affine
correction factors, then integrate w^(s+u) using Gamma. -/
def thetaHeadPositiveIntegralTerm
    (a b : ℚ) (n : ℕ) (i j : Fin 5) (t : ℕ) : ℚ :=
  let p : ℚ := (n:ℚ)^2
  let D : ℚ := (p-1)/a
  let m : ℕ := i.val+j.val-2*t
  ∑ s ∈ Finset.range (m+1),
    ∑ u ∈ Finset.range (t+1),
      (m.choose s : ℚ) * (t.choose u : ℚ) *
        D^(m-s) * b^s * p^(t-u) * b^(2*u) *
          thetaHeadMomentUpper b n (s+u)

/-- Uniform finite arithmetic majorant for one true theta summand
over a rational cell [a,b]. The analytic implication must still
be proved; no semantic inclusion is built into this definition. -/
def thetaHeadPositiveMajorant
    (a b : ℚ) (n : ℕ) (i j : Fin 5) : ℚ :=
  let p : ℚ := (n:ℚ)^2
  let D : ℚ := (p-1)/a
  let coeff (t : ℕ) : ℚ :=
    1 / ((Nat.factorial t : ℚ) *
      (Nat.factorial (i.val-t) : ℚ) *
      (Nat.factorial (j.val-t) : ℚ))
  let base : ℚ :=
    ∑ t ∈ Finset.range (min i.val j.val + 1),
      coeff t * D^(i.val+j.val-2*t) * p^t
  let correction : ℚ :=
    ∑ t ∈ Finset.range (min i.val j.val + 1),
      coeff t * thetaHeadPositiveIntegralTerm a b n i j t
  p*base + (b^2/4)*correction

/-- Four reusable exact rational checks for ALL 25 matrix
entries, including the diagonal/highest-order (4,4) entry.
These are intentionally generous integer caps. -/
theorem thetaSecondCellHeadPositiveMajorants_checked :
    ∀ i j : Fin 5,
      thetaHeadPositiveMajorant (1/8) (1/4) 2 i j ≤
        (1000000000:ℚ) ∧
      thetaHeadPositiveMajorant (1/4) (177/512) 2 i j ≤
        (5000000:ℚ) ∧
      thetaHeadPositiveMajorant (1/8) (1/4) 3 i j ≤
        (5000000000000:ℚ) ∧
      thetaHeadPositiveMajorant (1/4) (177/512) 3 i j ≤
        (20000000000:ℚ) := by
  native_decide

/-- Reuse Mathlib's Taylor lower bound for the exponential
rather than implementing a transcendental rational checker. -/
private theorem thetaExpNeg_small_of_one_factorial
    (E B : ℝ) (N : ℕ) (hE : 0 ≤ E) (hB : 0 < B)
    (hfinite : B < E^N / (Nat.factorial N : ℝ)) :
    Real.exp (-E) < 1/B := by
  have hExp : B < Real.exp E :=
    hfinite.trans_le (Real.pow_div_factorial_le_exp E hE N)
  have hinv : (1:ℝ)/Real.exp E < 1/B := by
    apply (div_lt_div_iff₀ (Real.exp_pos E) hB).2
    simpa only [one_mul] using hExp
  simpa only [Real.exp_neg, one_div] using hinv

theorem thetaExpNeg48_lt_oneE18 :
    Real.exp (-48) < 1/(10:ℝ)^18 :=
  thetaExpNeg_small_of_one_factorial 48 (10:ℝ)^18 48
    (by norm_num) (by positivity) (by norm_num)

theorem thetaExpNeg25_lt_oneE9 :
    Real.exp (-25) < 1/(10:ℝ)^9 :=
  thetaExpNeg_small_of_one_factorial 25 (10:ℝ)^9 25
    (by norm_num) (by positivity) (by norm_num)

theorem thetaExpNeg64_lt_oneE25 :
    Real.exp (-64) < 1/(10:ℝ)^25 :=
  thetaExpNeg_small_of_one_factorial 64 (10:ℝ)^25 64
    (by norm_num) (by positivity) (by norm_num)

end W5
