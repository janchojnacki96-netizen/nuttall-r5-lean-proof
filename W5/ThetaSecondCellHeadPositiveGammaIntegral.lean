import W5.ThetaSecondCellHeadPositiveWPolynomial
import W5.ThetaSecondCellHeadMomentReuse
import W5.ThetaAllSquareIndexNineMoments

/-!
# Coefficientwise positivity and one weighted-Gamma bound

The original positive factorial envelope has nonnegative coefficients
as a polynomial in the integration variable. Prove this ONCE for every
i,j : Fin 5 by closing Mathlib's coefficientwise-positive polynomials
under addition, multiplication, powers, and finite sums.

Then reuse the already compiled exact weighted-polynomial integral
identity and quarter-Gamma moment upper endpoints to bound the actual
weighted Lebesgue integral by ONE finite coefficient sum. This is a
non-conditional analytic part of the n=2,3 majorant; identifying this
sum with the computable rational K remains a separate algebraic step.
-/

namespace W5
open MeasureTheory

private theorem headCoeffNonneg_C (a : ℝ) (ha : 0 ≤ a) :
    ∀ k : ℕ, 0 ≤ (Polynomial.C a : Polynomial ℝ).coeff k := by
  intro k
  by_cases hk : k = 0
  · subst k
    simpa using ha
  · simp [Polynomial.coeff_C, hk]

private theorem headCoeffNonneg_X :
    ∀ k : ℕ, 0 ≤ (Polynomial.X : Polynomial ℝ).coeff k := by
  intro k
  by_cases hk : k = 1
  · subst k
    norm_num
  · have h : 1 ≠ k := Ne.symm hk
    simp [Polynomial.coeff_X, h]

private theorem headCoeffNonneg_add
    (P Q : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k)
    (hQ : ∀ k, 0 ≤ Q.coeff k) :
    ∀ k, 0 ≤ (P + Q).coeff k := by
  intro k
  rw [Polynomial.coeff_add]
  exact add_nonneg (hP k) (hQ k)

private theorem headCoeffNonneg_mul
    (P Q : Polynomial ℝ)
    (hP : ∀ k, 0 ≤ P.coeff k)
    (hQ : ∀ k, 0 ≤ Q.coeff k) :
    ∀ k, 0 ≤ (P * Q).coeff k := by
  intro k
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun z _ => mul_nonneg (hP z.1) (hQ z.2))

private theorem headCoeffNonneg_pow
    (P : Polynomial ℝ) (hP : ∀ k, 0 ≤ P.coeff k) :
    ∀ m k : ℕ, 0 ≤ (P ^ m).coeff k := by
  intro m
  induction m with
  | zero =>
      intro k
      by_cases hk : k = 0
      · subst k
        norm_num
      · simp [Polynomial.coeff_one, hk]
  | succ m ih =>
      intro k
      simpa only [pow_succ] using
        headCoeffNonneg_mul (P ^ m) P ih hP k

/-- The positive factorial envelope has nonnegative coefficients
as a polynomial in w, for all 25 original matrix entries. -/
theorem thetaHeadPositiveWPolynomial_coeff_nonneg
    (D p b : ℝ) (hD : 0 ≤ D) (hp : 0 ≤ p) (hb : 0 ≤ b)
    (i j : Fin 5) :
    ∀ k : ℕ, 0 ≤ (thetaHeadPositiveWPolynomial D p b i j).coeff k := by
  classical
  have hDb : ∀ k : ℕ,
      0 ≤ (Polynomial.C D + Polynomial.C b * Polynomial.X :
        Polynomial ℝ).coeff k :=
    headCoeffNonneg_add _ _
      (headCoeffNonneg_C D hD)
      (headCoeffNonneg_mul _ _
        (headCoeffNonneg_C b hb) headCoeffNonneg_X)
  have hpb : ∀ k : ℕ,
      0 ≤ (Polynomial.C p + Polynomial.C (b^2) * Polynomial.X :
        Polynomial ℝ).coeff k :=
    headCoeffNonneg_add _ _
      (headCoeffNonneg_C p hp)
      (headCoeffNonneg_mul _ _
        (headCoeffNonneg_C (b^2) (sq_nonneg b)) headCoeffNonneg_X)
  intro k
  unfold thetaHeadPositiveWPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro t ht
  have hweight : 0 ≤
      (1 / ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) := by positivity
  exact headCoeffNonneg_mul _ _
    (headCoeffNonneg_mul _ _
      (headCoeffNonneg_C _ hweight)
      (headCoeffNonneg_pow _ hDb _))
    (headCoeffNonneg_pow _ hpb _) k

/-- A coefficientwise nonnegative polynomial is dominated under the
true Lebesgue weighted integral by ANY upper bounds on its moments.
This is a reusable functional lemma, not an interval assumption. -/
theorem thetaWeightedPolynomialIntegral_le_moment_caps
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (P : Polynomial ℝ) (M : ℕ → ℝ)
    (hcoeff : ∀ k : ℕ, 0 ≤ P.coeff k)
    (hM : ∀ k : ℕ, thetaAuditedOneWeightedMoment y k ≤ M k) :
    (∫ w in Set.Ici (0 : ℝ),
      (Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)) * P.eval w
      ∂volume) ≤
      ∑ k ∈ Finset.range (P.natDegree+1), P.coeff k * M k := by
  rw [thetaWeightedPolynomialIntegral_eq_coeffSum y hy hy1 P]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (hM k) (hcoeff k)

/-- The ACTUAL weighted integral of the original positive
factorial envelope is bounded by proved rational Gamma moments.
No new Gamma integral, exact numeric certificate or individual
coefficient case is used. -/
theorem thetaHeadPositiveIntegral_le_coeffMomentCaps
    (b : ℚ) (D p x : ℝ) (n : ℕ) (i j : Fin 5)
    (hD : 0 ≤ D) (hp : 0 ≤ p)
    (hx : 0 < x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ 1) (hn : 0 < n) :
    (∫ w in Set.Ici (0 : ℝ),
      (Real.exp (-w) * (1+w*(x/(n:ℝ))^2)^((1:ℝ)/4)) *
        (thetaHeadPositiveWPolynomial D p (b:ℝ) i j).eval w
      ∂volume) ≤
      ∑ k ∈ Finset.range
          ((thetaHeadPositiveWPolynomial D p (b:ℝ) i j).natDegree+1),
        (thetaHeadPositiveWPolynomial D p (b:ℝ) i j).coeff k *
          (thetaHeadMomentUpper b n k : ℝ) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have h : 1 ≤ n := by omega
    exact_mod_cast h
  have hy : 0 < x/(n:ℝ) := div_pos hx hnR
  have hy1 : x/(n:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    linarith
  have hb0 : (0:ℝ) ≤ (b:ℝ) := (le_of_lt hx).trans hxb
  exact thetaWeightedPolynomialIntegral_le_moment_caps
    (x/(n:ℝ)) hy hy1
    (thetaHeadPositiveWPolynomial D p (b:ℝ) i j)
    (fun k => (thetaHeadMomentUpper b n k : ℝ))
    (thetaHeadPositiveWPolynomial_coeff_nonneg D p (b:ℝ)
      hD hp hb0 i j)
    (fun k => thetaHeadMomentUpper_real_sound
      b x hx.le hxb hb n k hn)

end W5
