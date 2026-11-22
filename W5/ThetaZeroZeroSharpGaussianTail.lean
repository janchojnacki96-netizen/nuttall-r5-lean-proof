import W5.ThetaZeroZeroAllSquareGaussianTerm
import W5.ThetaAuditedOriginalFullTail

/-!
# Sharp Gaussian tail for the GENUINE theta coefficient (0,0)

The verified all-entry bound uses n^26. For B00, the actual
term has the smaller n² prefactor and is nonnegative.

KEY REUSE: for EVERY n>=2, n² <= n^26 / 2^24.
Thus we can reuse the EXISTING Mathlib-based geometric summability
and half-ratio proof for the original n^26 majorant, multiplied
by a constant. We do not reprove a Gaussian ratio or geometric sum.

On the whole second x-cell [1/8,177/512], 1/x² >= 8.
Consequently the genuine infinite n>=2 remainder is positive
and <= 8*exp(-24), much sharper than the generic all-entry bound.
-/

namespace W5

/-- A uniform rescaling of the ALREADY verified index-26 majorant;
the large polynomial factor cancels down to the exact index-2
coefficient 8 at the first omitted square. -/
theorem thetaZeroZeroGaussian_le_scaledMajorant
    (y : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ)^2 * Real.exp (-((n:ℝ)^2-1)*y) ≤
      (1/(2:ℝ)^24) * thetaMajorantTerm y n := by
  have hnr : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hpow : (2:ℝ)^24 ≤ (n:ℝ)^24 :=
    pow_le_pow_left₀ (by norm_num) hnr 24
  have hfactor : (n:ℝ)^2 ≤ (n:ℝ)^26 / (2:ℝ)^24 := by
    apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^24)).2
    calc
      (n:ℝ)^2 * (2:ℝ)^24 ≤ (n:ℝ)^2 * (n:ℝ)^24 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (n:ℝ)^26 := by ring
  dsimp [thetaMajorantTerm]
  calc
    _ ≤ ((n:ℝ)^26/(2:ℝ)^24) *
          Real.exp (-((n:ℝ)^2-1)*y) :=
      mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    _ = _ := by ring

/-- True original B00 infinite tail, with no new series
convergence theorem or quadrature assumption.
The reuse of the degree-26 bound automatically gives 8*exp(-3y). -/
theorem thetaZeroZeroTail_nonneg_and_le_eight_exp
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : (3:ℝ) ≤ 1/x^2) :
    0 ≤ thetaAuditedTail 2 x (0 : Fin 5) (0 : Fin 5) ∧
    thetaAuditedTail 2 x (0 : Fin 5) (0 : Fin 5) ≤
      8 * Real.exp (-3*(1/x^2)) := by
  let y : ℝ := 1/x^2
  let f : ℕ → ℝ := fun k =>
    thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) (k+2)
  let g : ℕ → ℝ := fun k =>
    (1/(2:ℝ)^24) * thetaMajorantTerm y (2+k)
  have hy' : (3:ℝ) ≤ y := hy
  have hnonneg : ∀ k : ℕ, 0 ≤ f k := by
    intro k
    exact (thetaAuditedSeriesTerm_zero_zero_nonneg_le_gaussian
      x hx hx1 (k+2) (by omega)).1
  have hpoint : ∀ k : ℕ, f k ≤ g k := by
    intro k
    have hterm := (thetaAuditedSeriesTerm_zero_zero_nonneg_le_gaussian
      x hx hx1 (k+2) (by omega)).2
    have hmajor := thetaZeroZeroGaussian_le_scaledMajorant
      y (k+2) (by omega)
    dsimp [f, g]
    calc
      thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) (k+2) ≤
          ((k+2:ℕ) : ℝ)^2 *
            Real.exp (-(((k+2:ℕ):ℝ)^2-1)/x^2) := hterm
      _ ≤ (1/(2:ℝ)^24) * thetaMajorantTerm y (k+2) := by
        simpa only [y, div_eq_mul_inv, neg_mul] using hmajor
      _ = (1/(2:ℝ)^24) * thetaMajorantTerm y (2+k) := by
        rw [Nat.add_comm]
  have hg : Summable g :=
    (thetaMajorantTerm_tail_summable 2 (by norm_num) y hy').mul_left _
  have hf : Summable f :=
    Summable.of_nonneg_of_le hnonneg hpoint hg
  have hle : (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k :=
    hf.tsum_le_tsum hpoint hg
  change 0 ≤ (∑' k : ℕ, f k) ∧
    (∑' k : ℕ, f k) ≤ 8 * Real.exp (-3*y)
  constructor
  · exact tsum_nonneg hnonneg
  · calc
      (∑' k : ℕ, f k) ≤ ∑' k : ℕ, g k := hle
      _ = (1/(2:ℝ)^24) *
          (∑' k : ℕ, thetaMajorantTerm y (2+k)) := by
            simp only [g, tsum_mul_left]
      _ ≤ (1/(2:ℝ)^24) * (2 * thetaMajorantTerm y 2) :=
        mul_le_mul_of_nonneg_left
          (thetaMajorantTerm_tsum_tail_le_twice_first
            2 (by norm_num) y hy') (by positivity)
      _ = 8 * Real.exp (-3*y) := by
        norm_num [thetaMajorantTerm]
        ring

/-- Every x in the original second audited cell has y=1/x² >=8.
Therefore the ENTIRE true nonnegative tail after n=1 is uniformly
bounded by the ONE explicit exponential 8*exp(-24). -/
theorem thetaSecondCellZeroZeroTail_nonneg_le_exp24
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512) :
    0 ≤ thetaAuditedTail 2 x (0 : Fin 5) (0 : Fin 5) ∧
    thetaAuditedTail 2 x (0 : Fin 5) (0 : Fin 5) ≤
      8 * Real.exp (-24) := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
  have hproduct : 0 ≤ (((177:ℝ)/512)-x)*(((177:ℝ)/512)+x) :=
    mul_nonneg (by linarith) (by linarith)
  have hy : (8:ℝ) ≤ 1/x^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hx)).2
    nlinarith [hproduct]
  have hy3 : (3:ℝ) ≤ 1/x^2 := by linarith
  obtain ⟨h0, hsum⟩ :=
    thetaZeroZeroTail_nonneg_and_le_eight_exp x hx hx1 hy3
  refine ⟨h0, hsum.trans ?_⟩
  have hExp : Real.exp (-3*(1/x^2)) ≤ Real.exp (-24) :=
    Real.exp_le_exp.mpr (by nlinarith)
  exact mul_le_mul_of_nonneg_left hExp (by norm_num)

end W5
