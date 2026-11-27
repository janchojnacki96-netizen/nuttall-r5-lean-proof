import Nuttall.CompactFixedCongruence

namespace Nuttall

open W5

private def fixedPoint (D c : ℤ) : FixedIntInterval := ⟨c*D,c*D⟩

private theorem fixedPoint_containsReal (D c : ℤ) (hD : 0 < D) :
    ((fixedPoint D c).asQInterval D).ContainsReal (c:ℝ) := by
  have hDq : (D:ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have he : ((c*D:ℤ):ℚ)/(D:ℚ) = (c:ℚ) := by
    rw [Int.cast_mul, mul_div_cancel_right₀ _ hDq]
  simp [fixedPoint, FixedIntInterval.asQInterval, QInterval.ContainsReal, he]

def compactFixedRealEval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c:ℝ) + x*compactFixedRealEval cs x

/-- Horner evaluation with outward integer rounding after each product. -/
def compactFixedHorner (D : ℤ) (a : FixedIntInterval) : List ℚ → FixedIntInterval
  | [] => fixedPoint D 0
  | c :: cs => (compactFixedRound D (QInterval.point c)).add
      (a.mul D (compactFixedHorner D a cs))

theorem compactFixedHorner_containsReal (D : ℤ) (hD : 0 < D)
    {a : FixedIntInterval} {x : ℝ} (hx : (a.asQInterval D).ContainsReal x)
    (coefficients : List ℚ) :
    ((compactFixedHorner D a coefficients).asQInterval D).ContainsReal
      (compactFixedRealEval coefficients x) := by
  induction coefficients with
  | nil =>
    simpa only [compactFixedHorner, compactFixedRealEval, Int.cast_zero] using
      fixedPoint_containsReal D 0 hD
  | cons c cs ih =>
    rw [compactFixedHorner, FixedIntInterval.asQInterval_add, compactFixedRealEval]
    exact QInterval.add_containsReal
      (compactFixedRound_containsReal hD (I := QInterval.point c) ⟨le_rfl, le_rfl⟩)
      (FixedIntInterval.mul_containsReal D hD a (compactFixedHorner D a cs)
        x (compactFixedRealEval cs x) hx ih)

theorem compactFixedRealEval_ofFn (x : ℝ) {n : ℕ} (c : Fin n → ℚ) :
    compactFixedRealEval (List.ofFn c) x = ∑ i : Fin n, (c i:ℝ)*x^i.val := by
  induction n with
  | zero => simp [compactFixedRealEval]
  | succ n ih =>
    rw [List.ofFn_succ, compactFixedRealEval, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Repeated products keep power enclosures on the same integer grid. -/
def compactFixedPow (D : ℤ) (a : FixedIntInterval) : ℕ → FixedIntInterval
  | 0 => fixedPoint D 1
  | n+1 => (compactFixedPow D a n).mul D a

theorem compactFixedPow_containsReal (D : ℤ) (hD : 0 < D)
    {a : FixedIntInterval} {x : ℝ} (hx : (a.asQInterval D).ContainsReal x) (n : ℕ) :
    ((compactFixedPow D a n).asQInterval D).ContainsReal (x^n) := by
  induction n with
  | zero =>
    simpa only [compactFixedPow, pow_zero, Int.cast_one] using
      fixedPoint_containsReal D 1 hD
  | succ n ih =>
    rw [compactFixedPow, pow_succ]
    exact FixedIntInterval.mul_containsReal D hD (compactFixedPow D a n) a (x^n) x ih hx

#print axioms compactFixedHorner_containsReal
#print axioms compactFixedPow_containsReal

end Nuttall
