import W5.ThetaFirstCellRemaining50Bridge
import W5.ThetaAuditedCorrectionWPolynomial
import W5.ThetaAuditedMomentMonotonicity

/-!
# One genuine nine-moment identity for every square-index theta term

Rather than repeat an integral-to-finite-polynomial argument eleven
times (or separately for the 15 independent matrix entries), reuse the
verified Gamma integrability and the original Mathlib polynomial
evaluation lemma for an arbitrary polynomial.

For each n > 0, the original weighted correction uses p=n²,
d=(p-1)/x and y=x/n, so the quartic-root moment parameter is y².
The polynomial has degree at most eight for every i,j:Fin 5.
All nine moments are the genuine weighted Lebesgue moments already
defined and proved integrable in ThetaAuditedCorrectionWPolynomial.

No numerical enclosure, extra axiom, or termwise infinite-series
interchange is assumed.
-/

namespace W5
open MeasureTheory

/-- Finite polynomial expansion under a genuine weighted Lebesgue
integral, for an ARBITRARY polynomial and every 0 < y ≤ 1.
The only analytic input is the EXISTING uniform Gamma domination. -/
theorem thetaWeightedPolynomialIntegral_eq_coeffSum
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (P : Polynomial ℝ) :
    (∫ w in Set.Ici (0 : ℝ),
        (Real.exp (-w) * (1+w*y^2)^((1 : ℝ)/4)) * P.eval w
        ∂volume) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * thetaAuditedOneWeightedMoment y k := by
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*y^2)^((1 : ℝ)/4)
  have hexpand (w : ℝ) :
      W w * P.eval w =
        ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * (W w * w^k) := by
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (∫ w in Set.Ici (0 : ℝ), W w * P.eval w ∂volume) =
    ∑ k ∈ Finset.range (P.natDegree + 1),
      P.coeff k * thetaAuditedOneWeightedMoment y k
  calc
    _ = ∫ w in Set.Ici (0 : ℝ),
          ∑ k ∈ Finset.range (P.natDegree + 1),
            P.coeff k * (W w * w^k) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact hexpand w
    _ = ∑ k ∈ Finset.range (P.natDegree + 1),
          (∫ w in Set.Ici (0 : ℝ),
            P.coeff k * (W w * w^k) ∂volume) := by
        exact integral_finsetSum
          (Finset.range (P.natDegree + 1))
          (fun k _ =>
            (thetaAuditedOneWeightedMoment_integrable y hy hy1 k).const_mul
              (P.coeff k))
    _ = ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * thetaAuditedOneWeightedMoment y k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [integral_const_mul]
        rfl

/-- Every polynomial of degree at most eight uses exactly the
same NINE genuine weighted moments. This handles all 25 entries
and every retained nonzero square index with one analytic proof. -/
theorem thetaWeightedPolynomialIntegral_eq_nine
    (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ 8) :
    (∫ w in Set.Ici (0 : ℝ),
        (Real.exp (-w) * (1+w*y^2)^((1 : ℝ)/4)) * P.eval w
        ∂volume) =
      ∑ k ∈ Finset.range 9,
        P.coeff k * thetaAuditedOneWeightedMoment y k := by
  rw [thetaWeightedPolynomialIntegral_eq_coeffSum y hy hy1 P]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk9 hkout
  have hk : P.natDegree < k := by
    have hnot : ¬ k < P.natDegree + 1 := by
      intro hlt
      exact hkout (Finset.mem_range.mpr hlt)
    omega
  simp only [Polynomial.coeff_eq_zero_of_natDegree_lt hk, zero_mul]

/-- The exact n-th ORIGINAL theta series term is its pre-existing
elementary Gaussian base minus a finite sum of nine ORIGINAL
weighted correction moments. All n>0 and i,j:Fin5 are handled
uniformly, without repeating the n=1 calculation. -/
theorem thetaAuditedSeriesTerm_nine_moments
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 0 < n) :
    thetaAuditedSeriesTerm x i j n =
      thetaCertificateBaseTerm x i j n -
      (x^2/4) * Real.exp (-((n:ℝ)^2-1)/x^2) *
        (∑ k ∈ Finset.range 9,
          (thetaCorrectionWPolynomial
             x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) i j).coeff k *
          thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hy : 0 < x/(n:ℝ) := div_pos hx hnR
  have hy1 : x/(n:ℝ) ≤ 1 :=
    (div_le_iff₀ hnR).2 (by linarith)
  let p : ℝ := (n:ℝ)^2
  let d : ℝ := (p-1)/x
  let y : ℝ := x/(n:ℝ)
  let P : Polynomial ℝ := thetaCorrectionWPolynomial x p d i j
  have hweight (w : ℝ) :
      1+w*x^2/p = 1+w*y^2 := by
    dsimp [p, y]
    rw [div_pow]
    ring
  have hintegral :
      (∫ w in Set.Ici (0 : ℝ),
          Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial i j (d+w*x) (p+w*x^2)
          ∂volume) =
        ∑ k ∈ Finset.range 9,
          P.coeff k * thetaAuditedOneWeightedMoment y k := by
    calc
      _ = ∫ w in Set.Ici (0 : ℝ),
            (Real.exp (-w) * (1+w*y^2)^((1:ℝ)/4)) * P.eval w
            ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with w
          rw [hweight w]
          rw [thetaCorrectionWPolynomial_eval]
      _ = _ := thetaWeightedPolynomialIntegral_eq_nine y hy hy1 P
        (thetaCorrectionWPolynomial_natDegree_le_eight x p d i j)
  have hcorr : thetaCertificateCorrectionTerm x i j n =
      (x^2/4) * Real.exp (-(p-1)/x^2) *
        (∑ k ∈ Finset.range 9,
          P.coeff k * thetaAuditedOneWeightedMoment y k) := by
    unfold thetaCertificateCorrectionTerm
    simp only [if_neg hn0]
    change (x^2/4) * Real.exp (-(p-1)/x^2) *
      (∫ w in Set.Ici (0 : ℝ),
        Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          coefficientPolynomial i j (d+w*x) (p+w*x^2)
        ∂volume) =
      (x^2/4) * Real.exp (-(p-1)/x^2) *
        (∑ k ∈ Finset.range 9,
          P.coeff k * thetaAuditedOneWeightedMoment y k)
    rw [hintegral]
  unfold thetaAuditedSeriesTerm
  rw [hcorr]
  rfl


/-- A real-sound, fully parametric rational interval checker for
every ORIGINAL nonzero square-index theta term. Coefficient, moment,
Gaussian factor and x²/4 intervals are the only explicit inputs.

This reuses the EXISTING exact four-corner QInterval arithmetic and
the finite interval sum proof, including signed coefficients.
No independent 768-bit rounding semantics are postulated. -/
theorem thetaAuditedSeriesTerm_nine_moment_box_containsReal
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 0 < n)
    (B X E : QInterval) (C M : ℕ → QInterval)
    (hB : QInterval.ContainsReal B (thetaCertificateBaseTerm x i j n))
    (hX : QInterval.ContainsReal X (x^2/4))
    (hE : QInterval.ContainsReal E
      (Real.exp (-((n:ℝ)^2-1)/x^2)))
    (hC : ∀ k ∈ Finset.range 9,
      QInterval.ContainsReal (C k)
        ((thetaCorrectionWPolynomial
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) i j).coeff k))
    (hM : ∀ k ∈ Finset.range 9,
      QInterval.ContainsReal (M k)
        (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k)) :
    QInterval.ContainsReal
      (QInterval.sub B
        (QInterval.mul X
          (QInterval.mul E
            (QInterval.finsetSum (Finset.range 9)
              (fun k => QInterval.mul (C k) (M k))))))
      (thetaAuditedSeriesTerm x i j n) := by
  have hsum := QInterval.finsetSum_containsReal
    (Finset.range 9)
    (fun k => QInterval.mul (C k) (M k))
    (fun k =>
      (thetaCorrectionWPolynomial
        x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) i j).coeff k *
        thetaAuditedOneWeightedMoment (x/(n:ℝ)) k)
    (fun k hk => QInterval.mul_containsReal (hC k hk) (hM k hk))
  have hresult := QInterval.sub_containsReal hB
    (QInterval.mul_containsReal hX
      (QInterval.mul_containsReal hE hsum))
  rw [thetaAuditedSeriesTerm_nine_moments x hx hx1 i j n hn]
  exact hresult



/-- The n-th moment parameter y=x/n is monotone across every
positive x-cell. Thus two actual endpoint moment enclosures
automatically give a UNIFORM enclosure at every interior x.
Reuses the pre-existing genuine-integral monotonicity theorem,
without re-proving its Gamma or measure-theoretic parts. -/
theorem thetaNthWeightedMoment_endpoint_interval
    (a x b : ℝ) (n : ℕ) (hn : 0 < n)
    (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hb : b ≤ 1)
    (k : ℕ) (A B : QInterval)
    (hA : QInterval.ContainsReal A
      (thetaAuditedOneWeightedMoment (a/(n:ℝ)) k))
    (hB : QInterval.ContainsReal B
      (thetaAuditedOneWeightedMoment (b/(n:ℝ)) k)) :
    QInterval.ContainsReal ⟨A.lo, B.hi⟩
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr hnR.le
  have hax' : a / (n:ℝ) ≤ x / (n:ℝ) := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hax hinv
  have hxb' : x / (n:ℝ) ≤ b / (n:ℝ) := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hxb hinv
  have hb' : b / (n:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnR).2
    nlinarith
  exact thetaAuditedOneWeightedMoment_cell_interval
    (a/(n:ℝ)) (x/(n:ℝ)) (b/(n:ℝ))
    (div_nonneg ha hnR.le) hax' hxb' hb' k A B hA hB


end W5
