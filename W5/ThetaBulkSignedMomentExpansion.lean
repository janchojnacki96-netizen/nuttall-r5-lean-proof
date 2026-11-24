import W5.ThetaBulk48SevenTermEngine
import W5.ThetaSecondCellHeadDoubleBinomialGammaIntegral
import W5.ThetaSecondCellHeadOriginalIntegralComparison

/-!
# One EXACT signed Gaussian/Gamma expansion for all original theta terms

The earlier K majorant drops alternating coefficient signs and is
therefore too wide for the remaining 48 cells. Instead preserve the
ORIGINAL (-1)^(i+j-t) signs and the exact nine weighted Gamma moments.

Reuse the existing Mathlib double-binomial identity from #136, the
exact finite-integral evaluation from #138, and the genuine original
theta term's polynomial identity from W5.ThetaAllSquareIndexNineMoments.

This theorem is independent of a,b, matrix size 5 entries, or n.
It is the algebraic basis for ONE signed QInterval evaluator rather
than 48 handcrafted cases. No numerical evaluation or approximation.
-/

namespace W5
open MeasureTheory

/-- The signed (NOT positive-majorant) finite double-binomial
expansion of the ORIGINAL weighted theta correction integral. -/
noncomputable def thetaSignedWeightedMomentExpansion
    (y x d p : ℝ) (i j : Fin 5) : ℝ :=
  ∑ t ∈ Finset.range (min i.val j.val + 1),
    (((-1:ℝ)^(i.val+j.val-t)) /
      ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))) *
      (∑ s ∈ Finset.range (i.val+j.val-2*t+1),
        ∑ u ∈ Finset.range (t+1),
          (((i.val+j.val-2*t).choose s : ℝ) *
            (t.choose u : ℝ) *
            d^(i.val+j.val-2*t-s) *
            x^s * p^(t-u) * x^(2*u)) *
              thetaAuditedOneWeightedMoment y (s+u))

/-- One integration identity for ALL 25 original signed
theta coefficients simultaneously. All Lebesgue integrability
is supplied by the previously proved polynomial-Gamma theorem. -/
theorem thetaSignedWeightedMomentExpansion_eq_integral
    (y x d p : ℝ) (i j : Fin 5)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ w in Set.Ici (0:ℝ),
      (Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)) *
        (thetaCorrectionWPolynomial x p d i j).eval w
      ∂volume) =
      thetaSignedWeightedMomentExpansion y x d p i j := by
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)
  let c : ℕ → ℝ := fun t =>
    ((-1:ℝ)^(i.val+j.val-t)) /
      ((Nat.factorial t : ℝ) *
        (Nat.factorial (i.val-t) : ℝ) *
        (Nat.factorial (j.val-t) : ℝ))
  have hexpand (w : ℝ) :
      W w * (thetaCorrectionWPolynomial x p d i j).eval w =
        ∑ t ∈ Finset.range (min i.val j.val + 1),
          c t * (W w *
            ((d+w*x)^(i.val+j.val-2*t) *
              (p+w*x^2)^t)) := by
    unfold thetaCorrectionWPolynomial
    rw [Polynomial.eval_finsetSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    dsimp [c]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hTerm (t : ℕ) :
      IntegrableOn (fun w : ℝ =>
        W w * ((d+w*x)^(i.val+j.val-2*t) *
          (p+w*x^2)^t)) (Set.Ici (0:ℝ)) volume := by
    let P : Polynomial ℝ :=
      (Polynomial.C d + Polynomial.C x * Polynomial.X)^
          (i.val+j.val-2*t) *
      (Polynomial.C p + Polynomial.C (x^2) * Polynomial.X)^t
    have hP := thetaHeadWeightedPolynomial_integrableOn y hy hy1 P
    have heq :
        (fun w : ℝ =>
          W w * ((d+w*x)^(i.val+j.val-2*t) *
            (p+w*x^2)^t)) =
        (fun w : ℝ => W w * P.eval w) := by
      funext w
      dsimp [P]
      simp only [Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      ring
    rw [heq]
    exact hP
  have hTerms :
      ∀ t ∈ Finset.range (min i.val j.val + 1),
      IntegrableOn (fun w : ℝ =>
        c t * (W w *
          ((d+w*x)^(i.val+j.val-2*t) *
            (p+w*x^2)^t))) (Set.Ici (0:ℝ)) volume :=
    fun t _ => (hTerm t).const_mul (c t)
  calc
    (∫ w in Set.Ici (0:ℝ),
      W w * (thetaCorrectionWPolynomial x p d i j).eval w
      ∂volume) =
        ∫ w in Set.Ici (0:ℝ),
          ∑ t ∈ Finset.range (min i.val j.val + 1),
            c t * (W w *
              ((d+w*x)^(i.val+j.val-2*t) *
                (p+w*x^2)^t))
          ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with w
            exact hexpand w
    _ = ∑ t ∈ Finset.range (min i.val j.val + 1),
          (∫ w in Set.Ici (0:ℝ),
            c t * (W w *
              ((d+w*x)^(i.val+j.val-2*t) *
                (p+w*x^2)^t)) ∂volume) := by
            exact integral_finsetSum _ hTerms
    _ = ∑ t ∈ Finset.range (min i.val j.val + 1),
          c t * (∫ w in Set.Ici (0:ℝ),
            W w * ((d+w*x)^(i.val+j.val-2*t) *
              (p+w*x^2)^t) ∂volume) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [integral_const_mul]
    _ = ∑ t ∈ Finset.range (min i.val j.val + 1),
          c t * (∑ s ∈ Finset.range (i.val+j.val-2*t+1),
            ∑ u ∈ Finset.range (t+1),
              (((i.val+j.val-2*t).choose s : ℝ) *
                (t.choose u : ℝ) *
                d^(i.val+j.val-2*t-s) *
                x^s * p^(t-u) * x^(2*u)) *
                  thetaAuditedOneWeightedMoment y (s+u)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [thetaHead_affine_product_weighted_integral_double_binomial
              y hy hy1 d p x (i.val+j.val-2*t) t]
    _ = thetaSignedWeightedMomentExpansion y x d p i j := rfl

/-- The ORIGINAL n-th real theta coefficient is EXACTLY this
finite SIGNED moment expression, without loss of cancellation.
This holds for every nonzero square index, every matrix entry,
and every 0<x<=1, so no cell-specific integration is needed. -/
theorem thetaAuditedSeriesTerm_eq_signed_moment_expansion
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 0 < n) :
    thetaAuditedSeriesTerm x i j n =
      thetaCertificateBaseTerm x i j n -
        (x^2/4) * Real.exp (-((n:ℝ)^2-1)/x^2) *
          thetaSignedWeightedMomentExpansion
            (x/(n:ℝ)) x (((n:ℝ)^2-1)/x) ((n:ℝ)^2) i j := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hy : 0 < x/(n:ℝ) := div_pos hx hnR
  have hy1 : x/(n:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    linarith
  let p : ℝ := (n:ℝ)^2
  let d : ℝ := (p-1)/x
  let y : ℝ := x/(n:ℝ)
  let P : Polynomial ℝ := thetaCorrectionWPolynomial x p d i j
  have hMoment :
      (∑ k ∈ Finset.range 9,
        P.coeff k * thetaAuditedOneWeightedMoment y k) =
      thetaSignedWeightedMomentExpansion y x d p i j := by
    rw [← thetaWeightedPolynomialIntegral_eq_nine
      y hy hy1 P
        (thetaCorrectionWPolynomial_natDegree_le_eight x p d i j)]
    exact thetaSignedWeightedMomentExpansion_eq_integral
      y x d p i j hy hy1
  rw [thetaAuditedSeriesTerm_nine_moments x hx hx1 i j n hn]
  change thetaCertificateBaseTerm x i j n -
      (x^2/4) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∑ k ∈ Finset.range 9,
          P.coeff k * thetaAuditedOneWeightedMoment y k) =
    thetaCertificateBaseTerm x i j n -
      (x^2/4) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        thetaSignedWeightedMomentExpansion y x d p i j
  rw [hMoment]

end W5
