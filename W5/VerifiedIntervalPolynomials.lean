import W5.VerifiedIntervalMultiplication

/-!
# Sound rational interval evaluation of polynomials

This file extends the exact rational interval core with signed scalar
multiplication, natural powers, and Horner evaluation of finite
polynomials. Every containment result is proved in Lean.

This is a generic *rational* polynomial checker. It does not certify
the transcendental theta terms, their tails, or the 255 numerical pivot
signs from the external certificate.
-/

namespace W5.QInterval

/-- An exact one-point interval. -/
def point (x : ℚ) : QInterval := ⟨x, x⟩

theorem point_contains (x : ℚ) : Contains (point x) x :=
  ⟨le_refl x, le_refl x⟩

/-- Scaling by any rational coefficient, including negative ones. -/
def scaleAny (c : ℚ) (a : QInterval) : QInterval :=
  if hc : 0 ≤ c then scaleNonneg c a else neg (scaleNonneg (-c) a)

theorem scaleAny_contains (c : ℚ) {a : QInterval} {x : ℚ}
    (ha : Contains a x) :
    Contains (scaleAny c a) (c * x) := by
  by_cases hc : 0 ≤ c
  · simpa [scaleAny, hc] using scaleNonneg_contains c hc ha
  · have hminus : 0 ≤ -c := by
      linarith
    have h := neg_contains (scaleNonneg_contains (-c) hminus ha)
    simpa [scaleAny, hc] using h

/-- A power enclosure, using the previously proved signed four-corner
interval multiplication at every step. -/
def pow (a : QInterval) : ℕ → QInterval
  | 0 => point 1
  | k + 1 => mul (pow a k) a

theorem pow_contains (a : QInterval) (x : ℚ)
    (ha : Contains a x) (n : ℕ) :
    Contains (pow a n) (x ^ n) := by
  induction n with
  | zero =>
      simpa [pow] using point_contains (1 : ℚ)
  | succ n ih =>
      simpa [pow, pow_succ] using (mul_contains ih ha)

/-- Evaluation of coefficients from constant to highest degree. -/
def eval (coeffs : List ℚ) (x : ℚ) : ℚ :=
  match coeffs with
  | [] => 0
  | c :: cs => c + x * eval cs x

/-- Horner evaluation with an exact interval enclosure. -/
def evalInterval (coeffs : List ℚ) (a : QInterval) : QInterval :=
  match coeffs with
  | [] => point 0
  | c :: cs => add (point c) (mul a (evalInterval cs a))

/-- Soundness of arbitrary finite rational polynomial evaluation. -/
theorem evalInterval_contains (a : QInterval) (x : ℚ)
    (ha : Contains a x) (coeffs : List ℚ) :
    Contains (evalInterval coeffs a) (eval coeffs x) := by
  induction coeffs with
  | nil =>
      simpa [evalInterval, eval] using point_contains (0 : ℚ)
  | cons c cs ih =>
      simpa [evalInterval, eval] using
        (add_contains (point_contains c) (mul_contains ha ih))

/-- The lower endpoint is a trusted certificate of strict positivity
for every argument in the input interval. -/
theorem eval_positive_of_lo_positive
    (a : QInterval) (x : ℚ) (ha : Contains a x)
    (coeffs : List ℚ)
    (hlo : 0 < (evalInterval coeffs a).lo) :
    0 < eval coeffs x :=
  lt_of_lt_of_le hlo (evalInterval_contains a x ha coeffs).1

/-- The upper endpoint is a trusted certificate of strict negativity
for every argument in the input interval. -/
theorem eval_negative_of_hi_negative
    (a : QInterval) (x : ℚ) (ha : Contains a x)
    (coeffs : List ℚ)
    (hhi : (evalInterval coeffs a).hi < 0) :
    eval coeffs x < 0 :=
  lt_of_le_of_lt (evalInterval_contains a x ha coeffs).2 hhi

end W5.QInterval
