import W5.ThetaBulkSignedIntervalEvaluator
import W5.ThetaExpTaylor65Remainder

/-!
# One rational exponential evaluator for ALL R5 cells and n=2,...,6

Never assume a non-rational exp endpoint. For a genuine x-cell
[a,b] and n>1 set z=(n²-1)/(1024*x²). On the entire compact R5
numerical domain, 0≤z≤1/3 for n≤6 once a≥821/2048.

* The existing Mathlib-proved 65-term Taylor bound encloses exp(z).
* We compute that finite sum with already proved real-sound QInterval
  arithmetic for each rational cell, without floating point.
* We invert that positive interval using the VERIFIED signed-real
  reciprocal interval.
* Ten interval squarings give exp(-1024*z), the original Gaussian
  factor exp(-(n²-1)/x²).

Soundness is one analytic argument for ALL parameters. The only
finite checker premises are that the range-reduced input satisfies
z.hi≤1/3 and the lower computed exp endpoint is >0. Those are exact
rational inequalities for n=2,...,6 and the original endpoint list.

No numerical values are assumed or invented, and no separate cell
proof is required. The cost/width of the final 48-cell LDL check
remains an independent computational question.
-/

namespace W5

/-- The exact reduced interval for the original REAL exponent
at a fixed square index n, across an entire positive x-cell. -/
def thetaBulkReducedExpArgBox (a b : ℚ) (n : ℕ) : QInterval :=
  ⟨(((n:ℚ)^2-1)/(1024*b^2)),
   (((n:ℚ)^2-1)/(1024*a^2))⟩

theorem thetaBulkReducedExpArgBox_containsReal
    (a b : ℚ) (x : ℝ) (n : ℕ)
    (ha : (0:ℚ) < a)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hn : 2 ≤ n) :
    QInterval.ContainsReal (thetaBulkReducedExpArgBox a b n)
      (((n:ℝ)^2-1)/(1024*x^2)) := by
  have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have hx : 0 < x := haR.trans_le hax
  have hb : (0:ℝ) < (b:ℝ) := hx.trans_le hxb
  have hN : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnum : (0:ℝ) ≤ (n:ℝ)^2-1 := by
    nlinarith
  have hAX : (a:ℝ)^2 ≤ x^2 :=
    pow_le_pow_left₀ haR.le hax 2
  have hXB : x^2 ≤ (b:ℝ)^2 :=
    pow_le_pow_left₀ hx.le hxb 2
  have hlow :
      ((n:ℝ)^2-1)/(1024*(b:ℝ)^2) ≤
        ((n:ℝ)^2-1)/(1024*x^2) := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) (sq_pos_of_pos hb))
      (mul_pos (by norm_num) (sq_pos_of_pos hx))).2
    nlinarith [mul_le_mul_of_nonneg_left hXB hnum]
  have hhi :
      ((n:ℝ)^2-1)/(1024*x^2) ≤
        ((n:ℝ)^2-1)/(1024*(a:ℝ)^2) := by
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) (sq_pos_of_pos hx))
      (mul_pos (by norm_num) (sq_pos_of_pos haR))).2
    nlinarith [mul_le_mul_of_nonneg_left hAX hnum]
  simpa only [thetaBulkReducedExpArgBox, QInterval.ContainsReal,
    Rat.cast_div, Rat.cast_sub, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using
    (show
      ((n:ℝ)^2-1)/(1024*(b:ℝ)^2) ≤
        ((n:ℝ)^2-1)/(1024*x^2) ∧
      ((n:ℝ)^2-1)/(1024*x^2) ≤
        ((n:ℝ)^2-1)/(1024*(a:ℝ)^2)
      from ⟨hlow,hhi⟩)

/-- The actual 65-term Taylor polynomial, evaluated by the
EXISTING signed 4-corner QInterval arithmetic with rationals. -/
def thetaBulkExpTaylorPolynomialBox (Z : QInterval) : QInterval :=
  QInterval.finsetSum (Finset.range 65)
    (fun k =>
      QInterval.mul
        (QInterval.point (1/(Nat.factorial k:ℚ)))
        (QInterval.pow Z k))

theorem thetaBulkExpTaylorPolynomialBox_containsReal
    (Z : QInterval) (z : ℝ)
    (hz : QInterval.ContainsReal Z z) :
    QInterval.ContainsReal (thetaBulkExpTaylorPolynomialBox Z)
      (thetaExpTaylor65 z) := by
  unfold thetaBulkExpTaylorPolynomialBox thetaExpTaylor65
  apply QInterval.finsetSum_containsReal
    (Finset.range 65)
    (fun k =>
      QInterval.mul
        (QInterval.point (1/(Nat.factorial k:ℚ)))
        (QInterval.pow Z k))
    (fun k => z^k/(Nat.factorial k:ℝ))
    (by
      intro k hk
      have hc := thetaRationalPoint_containsReal
        (1/(Nat.factorial k:ℚ))
      have hp := thetaRationalIntervalPow_containsReal Z z hz k
      have h := QInterval.mul_containsReal hc hp
      convert h using 1
      · simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
        ring)

/-- Exactly the old Mathlib 65-term Taylor absolute remainder,
expressed as a fixed positive rational. -/
def thetaBulkExpTaylorError : ℚ :=
  2 / ((3:ℚ)^65 * (Nat.factorial 65:ℚ))

/-- A computable rational interval for exp(z), 0≤z≤1/3. -/
def thetaBulkExpTaylorBox (Z : QInterval) : QInterval :=
  let P := thetaBulkExpTaylorPolynomialBox Z
  ⟨P.lo, P.hi + thetaBulkExpTaylorError⟩

theorem thetaBulkExpTaylorBox_containsReal
    (Z : QInterval) (z : ℝ)
    (hz : QInterval.ContainsReal Z z)
    (hz0 : 0 ≤ z) (hz3 : z ≤ (1:ℝ)/3) :
    QInterval.ContainsReal (thetaBulkExpTaylorBox Z)
      (Real.exp z) := by
  have hP := thetaBulkExpTaylorPolynomialBox_containsReal Z z hz
  have hBounds := thetaExpTaylor65_bounds z hz0 hz3
  have hresult :
      ((thetaBulkExpTaylorPolynomialBox Z).lo:ℝ) ≤ Real.exp z ∧
      Real.exp z ≤
        ((thetaBulkExpTaylorPolynomialBox Z).hi:ℝ) +
          (thetaBulkExpTaylorError:ℝ) := by
    constructor
    · exact hP.1.trans hBounds.1
    · calc
        Real.exp z ≤ thetaExpTaylor65 z +
          2 / ((3:ℝ)^65 * (Nat.factorial 65:ℝ)) := hBounds.2
        _ ≤ ((thetaBulkExpTaylorPolynomialBox Z).hi:ℝ) +
            2 / ((3:ℝ)^65 * (Nat.factorial 65:ℝ)) :=
              add_le_add_right hP.2 _
        _ = ((thetaBulkExpTaylorPolynomialBox Z).hi:ℝ) +
            (thetaBulkExpTaylorError:ℝ) := by
              simp only [thetaBulkExpTaylorError, Rat.cast_div,
                Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  simpa only [thetaBulkExpTaylorBox, QInterval.ContainsReal,
    Rat.cast_add] using hresult

/-- Repeated SQUARING, not 1024 separate interval multiplications.
The computation is O(log 1024) interval operations, and its
real-number containment is proved by one induction. -/
def thetaBulkPow2 : ℕ → QInterval → QInterval
  | 0, I => I
  | k+1, I =>
      let J := thetaBulkPow2 k I
      QInterval.mul J J

theorem thetaBulkPow2_containsReal
    (I : QInterval) (x : ℝ)
    (hx : QInterval.ContainsReal I x) :
    ∀ k : ℕ,
      QInterval.ContainsReal (thetaBulkPow2 k I)
        (x^(2^k)) := by
  intro k
  induction k with
  | zero =>
      simpa only [thetaBulkPow2, pow_zero, pow_one] using hx
  | succ k ih =>
      have hh := QInterval.mul_containsReal ih ih
      have hpow : x^(2^(k+1)) = x^(2^k)*x^(2^k) := by
        rw [pow_succ, pow_mul, pow_two]
      simpa only [thetaBulkPow2, hpow] using hh

/-- The one executable real exponential interval for any rational
x-cell and positive square index, with no floating point. -/
def thetaBulkOriginalGaussianExpBox (a b : ℚ) (n : ℕ) : QInterval :=
  thetaBulkPow2 10
    (QInterval.inversePositive
      (thetaBulkExpTaylorBox (thetaBulkReducedExpArgBox a b n)))

/-- REAL enclosure for exp(-(n²-1)/x²) from only two DECIDABLE
rational checks on each n-cell: z.hi≤1/3 and expBox.lo>0.
One theorem for ALL square indices and x-cells, not 48 copies. -/
theorem thetaBulkOriginalGaussianExpBox_containsReal
    (a b : ℚ) (x : ℝ) (n : ℕ)
    (ha : (0:ℚ) < a)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hn : 2 ≤ n)
    (hRange : (thetaBulkReducedExpArgBox a b n).hi ≤ (1:ℚ)/3)
    (hPos : 0 <
      (thetaBulkExpTaylorBox (thetaBulkReducedExpArgBox a b n)).lo) :
    QInterval.ContainsReal (thetaBulkOriginalGaussianExpBox a b n)
      (Real.exp (-((n:ℝ)^2-1)/x^2)) := by
  let Z := thetaBulkReducedExpArgBox a b n
  let z : ℝ := ((n:ℝ)^2-1)/(1024*x^2)
  have hz : QInterval.ContainsReal Z z :=
    thetaBulkReducedExpArgBox_containsReal a b x n ha hax hxb hn
  have hx : 0 < x := by
    have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
    exact haR.trans_le hax
  have hN : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (by nlinarith)
      (mul_nonneg (by norm_num) (sq_nonneg x))
  have hz3 : z ≤ (1:ℝ)/3 := by
    have hQ :
        ((thetaBulkReducedExpArgBox a b n).hi:ℝ) ≤ (1:ℝ)/3 := by
      exact_mod_cast hRange
    exact hz.2.trans hQ
  have hExp := thetaBulkExpTaylorBox_containsReal Z z hz hz0 hz3
  have hInv :=
    QInterval.inversePositive_containsReal hExp hPos
  have hPower := thetaBulkPow2_containsReal
    (QInterval.inversePositive (thetaBulkExpTaylorBox Z))
    (Real.exp z)⁻¹ hInv 10
  have hscale : (1024:ℝ)*z = ((n:ℝ)^2-1)/x^2 := by
    dsimp [z]
    have hx2 : x^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hx)
    field_simp [hx2]
    ring
  have hEpow :
      (Real.exp z)^1024 =
        Real.exp (((n:ℝ)^2-1)/x^2) := by
    rw [← Real.exp_nat_mul, hscale]
  have hEq :
      (Real.exp z)⁻¹ ^ (2^10) =
        Real.exp (-((n:ℝ)^2-1)/x^2) := by
    calc
      (Real.exp z)⁻¹ ^ (2^10) =
          ((Real.exp z)^1024)⁻¹ := by norm_num [inv_pow]
      _ = (Real.exp (((n:ℝ)^2-1)/x^2))⁻¹ := by rw [hEpow]
      _ = Real.exp (-((n:ℝ)^2-1)/x^2) := by
        rw [Real.exp_neg, neg_div]
  simpa only [thetaBulkOriginalGaussianExpBox, Z, hEq] using hPower

end W5
