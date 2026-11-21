import W5.ThetaAuditedTailRationalEnclosure

/-!
# Original theta correction polynomial in the integration variable w

The certificate's actual correction integrand contains
 B_ij(d+w*x, p+w*x^2)
where B_ij is the original degree-at-most-eight Gaussian
coefficient polynomial. Instead of duplicating its 25 formulae
or the integer auditor's binomial expansion, represent this
expression uniformly as an ordinary Mathlib Polynomial R in w.

The exact evaluation theorem reuses Mathlib's polynomial
finset sum/evaluation laws and ring normalization. This is
the analytic-to-algebraic bridge for the finite weighted moments
computed by the 768-bit auditor, not an assumed numeric bound.
-/

namespace W5

/-- Exact original B_ij after the affine substitution used inside
the weighted correction integral. The parameters x,p,d need
no positivity assumptions: this is purely polynomial algebra. -/
noncomputable def thetaCorrectionWPolynomial
    (x p d : ℝ) (i j : Fin 5) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (min i.val j.val + 1),
    Polynomial.C
      (((-1 : ℝ) ^ (i.val+j.val-k)) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ))) *
      (Polynomial.C d + Polynomial.C x * Polynomial.X) ^
        (i.val+j.val-2*k) *
      (Polynomial.C p + Polynomial.C (x^2) * Polynomial.X)^k

/-- The actual coefficient under EVERY original theta integral
is EXACTLY the value of the new polynomial in w, without
approximation or any assumption about x,p,d,w. -/
theorem thetaCorrectionWPolynomial_eval
    (x p d w : ℝ) (i j : Fin 5) :
    (thetaCorrectionWPolynomial x p d i j).eval w =
      coefficientPolynomial i j (d+w*x) (p+w*x^2) := by
  unfold thetaCorrectionWPolynomial coefficientPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  simp only [div_eq_mul_inv]
  ring


/-!
## Audited finite moment dimension: degree at most eight

The independent integer auditor uses exactly nine moments
k=0,...,8. We prove that this is sufficient for ALL 25
original theta correction polynomials. Only the already
formalized Mathlib natDegree bounds for linear polynomials,
products, powers and finite sums are used.
-/

/-- Every original affine theta correction polynomial has
degree at most eight in the integration variable w, uniformly
over all real x,p,d and all original coefficient indices. -/
theorem thetaCorrectionWPolynomial_natDegree_le_eight
    (x p d : ℝ) (i j : Fin 5) :
    (thetaCorrectionWPolynomial x p d i j).natDegree ≤ 8 := by
  classical
  let D : Polynomial ℝ :=
    Polynomial.C d + Polynomial.C x * Polynomial.X
  let Q : Polynomial ℝ :=
    Polynomial.C p + Polynomial.C (x^2) * Polynomial.X
  let F : ℕ → Polynomial ℝ := fun k =>
    Polynomial.C
      (((-1 : ℝ) ^ (i.val+j.val-k)) /
        ((Nat.factorial k : ℝ) *
         (Nat.factorial (i.val-k) : ℝ) *
         (Nat.factorial (j.val-k) : ℝ))) *
      D ^ (i.val+j.val-2*k) * Q^k
  have hD : D.natDegree ≤ 1 := by
    dsimp [D]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  have hQ : Q.natDegree ≤ 1 := by
    dsimp [Q]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  have hterm (k : ℕ) (hk : k ≤ min i.val j.val) :
      (F k).natDegree ≤ 8 := by
    have hfirst : (D^(i.val+j.val-2*k)).natDegree ≤
        i.val+j.val-2*k := by
      simpa only [mul_one] using
        (Polynomial.natDegree_pow_le_of_le (i.val+j.val-2*k) hD)
    have hsecond : (Q^k).natDegree ≤ k := by
      simpa only [mul_one] using
        (Polynomial.natDegree_pow_le_of_le k hQ)
    have hmul : ((Polynomial.C
        (((-1 : ℝ) ^ (i.val+j.val-k)) /
          ((Nat.factorial k : ℝ) *
           (Nat.factorial (i.val-k) : ℝ) *
           (Nat.factorial (j.val-k) : ℝ)))) *
          D^(i.val+j.val-2*k)).natDegree ≤
        i.val+j.val-2*k := by
      calc
        _ ≤ (Polynomial.C
              (((-1 : ℝ) ^ (i.val+j.val-k)) /
                ((Nat.factorial k : ℝ) *
                 (Nat.factorial (i.val-k) : ℝ) *
                 (Nat.factorial (j.val-k) : ℝ)))).natDegree +
             (D^(i.val+j.val-2*k)).natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ i.val+j.val-2*k := by
          simpa using hfirst
    have hle : (F k).natDegree ≤
        (i.val+j.val-2*k)+k := by
      exact Polynomial.natDegree_mul_le_of_le hmul hsecond
    have hi : i.val < 5 := i.isLt
    have hj : j.val < 5 := j.isLt
    exact hle.trans (by omega)
  have hsum : ∀ s : Finset ℕ,
      (∀ k ∈ s, k ≤ min i.val j.val) →
      (∑ k ∈ s, F k).natDegree ≤ 8 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert k s hnotin ih =>
        intro hs
        rw [Finset.sum_insert hnotin]
        apply Polynomial.natDegree_add_le_of_degree_le
        · exact hterm k (hs k (Finset.mem_insert_self k s))
        · exact ih (fun v hv =>
            hs v (Finset.mem_insert_of_mem hv))
  change (∑ k ∈ Finset.range (min i.val j.val + 1),
    F k).natDegree ≤ 8
  exact hsum _ (by
    intro k hk
    have hk' : k < min i.val j.val + 1 :=
      Finset.mem_range.mp hk
    omega)

/-- Every moment index used by the genuinely evaluated original
theta correction is below nine. This links the generic polynomial
bridge to the independent auditor's nine-moment layout. -/
theorem thetaCorrectionWPolynomial_moment_index_lt_nine
    (x p d : ℝ) (i j : Fin 5) (k : ℕ)
    (hk : k ∈ Finset.range
      ((thetaCorrectionWPolynomial x p d i j).natDegree + 1)) :
    k < 9 := by
  have hdeg := thetaCorrectionWPolynomial_natDegree_le_eight x p d i j
  have h : k < (thetaCorrectionWPolynomial x p d i j).natDegree + 1 :=
    Finset.mem_range.mp hk
  omega

/-- Specialization to the first nonzero square index p=1,d=0:
the integral correction is an exact polynomial-weighted
Lebesgue integral, with no external Gaussian factor. -/
theorem thetaAuditedSeriesTerm_one_polynomial_integral
    (x : ℝ) (i j : Fin 5) :
    thetaAuditedSeriesTerm x i j 1 =
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) -
      (x^2/4) *
        (∫ w in Set.Ici (0 : ℝ),
          Real.exp (-w) *
            (1+w*x^2)^((1 : ℝ)/4) *
              (thetaCorrectionWPolynomial x 1 0 i j).eval w
          ∂MeasureTheory.volume) := by
  rw [thetaAuditedSeriesTerm_one_diagonal_minus_integral]
  simp_rw [thetaCorrectionWPolynomial_eval]
  simp only [zero_add]


/-!
## Exact moment expansion of the original first-term correction

Mathlib already supplies the finite coefficient expansion of any
Polynomial R, so no 25x25 manual binomial expansion is needed.
We integrate this finite expansion using the EXISTING
integral_finsetSum lemma. Integrability of each weighted monomial is
an explicit premise here; proving it by domination and then proving
its auditor-specific rational enclosure are separate obligations.
-/

/-- The true correction polynomial is a FINITE sum of its
actual Mathlib coefficients, for arbitrary original indices. -/
theorem coefficientPolynomial_theta_affine_eq_coefficient_sum
    (x p d w : ℝ) (i j : Fin 5) :
    coefficientPolynomial i j (d+w*x) (p+w*x^2) =
      ∑ k ∈ Finset.range
          ((thetaCorrectionWPolynomial x p d i j).natDegree + 1),
        (thetaCorrectionWPolynomial x p d i j).coeff k * w^k := by
  rw [← thetaCorrectionWPolynomial_eval]
  exact Polynomial.eval_eq_sum_range w

/-- The true weighted moments evaluated by the independent
integer auditor, as ordinary Lebesgue integrals. No enclosures or
symbolic moment evaluations are asserted by this definition. -/
noncomputable def thetaAuditedOneWeightedMoment
    (x : ℝ) (k : ℕ) : ℝ :=
  ∫ w in Set.Ici (0 : ℝ),
    (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k
    ∂MeasureTheory.volume


/-!
## Unconditional integrability of every true weighted moment

Reuse the original quarter-power domination lemma and the Mathlib
Gamma integrability theorem already formalized in
ThetaAuditedCorrectionMoment. The factor
(1+w*x^2)^(1/4) is at most 1+w on 0<x<=1, so the kth
weighted moment is dominated by the sum of the kth and
(k+1)st ordinary exponential Gamma moments. The half-line
Ici/Ioi equivalence is supplied by Mathlib.
-/

/-- Every genuine one-index weighted moment appearing in the original
first-cell theta integral is Lebesgue integrable for 0<x<=1.
No extra integrability assumptions are needed for any k. -/
theorem thetaAuditedOneWeightedMoment_integrable
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k)
      (Set.Ici (0 : ℝ)) MeasureTheory.volume := by
  have hbig : MeasureTheory.Integrable
      (fun w : ℝ =>
        w^k * Real.exp (-w) + w^(k+1) * Real.exp (-w))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (thetaAuditedCorrectionGammaMoment_integrable k).add
      (thetaAuditedCorrectionGammaMoment_integrable (k+1))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    fun_prop
  have hbound : ∀ᵐ w : ℝ
      ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      ‖(Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k‖ ≤
        w^k * Real.exp (-w) + w^(k+1) * Real.exp (-w) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : 0 ≤ w := hw.le
    have hweight : (1+w*x^2)^((1 : ℝ)/4) ≤ w+1 := by
      simpa only [div_one] using
        thetaAuditedCorrectionQuarterPower_le x 1 w hx hx1
          (by norm_num) hw0
    have hnonneg :
        0 ≤ (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k ≤
          (Real.exp (-w) * (w+1)) * w^k := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hweight
                (Real.exp_nonneg _))
              (pow_nonneg hw0 k)
      _ = w^k * Real.exp (-w) +
            w^(k+1) * Real.exp (-w) := by ring
  have hIoi : MeasureTheory.IntegrableOn
      (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k)
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume :=
    hbig.mono' hmeas hbound
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hIoi

/-- Exact integral linearity expresses the original n=1 theta
summand as a finite linear combination of the true moments.
Mathlib supplies polynomial coefficient expansion and finite
integral-sum interchange; only individual moment integrability
is required, never infinite series interchange or unverified data. -/
theorem thetaAuditedSeriesTerm_one_weighted_moment_sum
    (x : ℝ) (i j : Fin 5)
    (hIntegrable : ∀ k ∈ Finset.range
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
      MeasureTheory.IntegrableOn (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k)
        (Set.Ici (0 : ℝ)) MeasureTheory.volume) :
    thetaAuditedSeriesTerm x i j 1 =
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) -
      (x^2/4) *
        (∑ k ∈ Finset.range
            ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
          (thetaCorrectionWPolynomial x 1 0 i j).coeff k *
            thetaAuditedOneWeightedMoment x k) := by
  let P : Polynomial ℝ := thetaCorrectionWPolynomial x 1 0 i j
  let W : ℝ → ℝ := fun w =>
    Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)
  have hexpand (w : ℝ) :
      W w * P.eval w =
        ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * (W w * w^k) := by
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hIntegral :
      (∫ w in Set.Ici (0 : ℝ), W w * P.eval w
        ∂MeasureTheory.volume) =
        ∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * thetaAuditedOneWeightedMoment x k := by
    calc
      _ = ∫ w in Set.Ici (0 : ℝ),
            ∑ k ∈ Finset.range (P.natDegree + 1),
              P.coeff k * (W w * w^k)
            ∂MeasureTheory.volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with w
          exact hexpand w
      _ = ∑ k ∈ Finset.range (P.natDegree + 1),
            (∫ w in Set.Ici (0 : ℝ),
              P.coeff k * (W w * w^k)
              ∂MeasureTheory.volume) := by
          exact MeasureTheory.integral_finsetSum
            (Finset.range (P.natDegree + 1))
            (fun k hk => (hIntegrable k hk).const_mul (P.coeff k))
      _ = ∑ k ∈ Finset.range (P.natDegree + 1),
            P.coeff k * thetaAuditedOneWeightedMoment x k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [MeasureTheory.integral_const_mul]
          rfl
  rw [thetaAuditedSeriesTerm_one_polynomial_integral]
  change
    (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
     else 0) -
      (x^2/4) *
        (∫ w in Set.Ici (0 : ℝ), W w * P.eval w
          ∂MeasureTheory.volume) =
    (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
     else 0) -
      (x^2/4) *
        (∑ k ∈ Finset.range (P.natDegree + 1),
          P.coeff k * thetaAuditedOneWeightedMoment x k)
  rw [hIntegral]


/-- The first true square-index term is a finite moment sum WITHOUT
the provisional termwise-integrability hypotheses. This is the
unconditional analytic reduction needed before importing the
external auditor's rational moment intervals. -/
theorem thetaAuditedSeriesTerm_one_weighted_moment_sum_unconditional
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) :
    thetaAuditedSeriesTerm x i j 1 =
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) -
      (x^2/4) *
        (∑ k ∈ Finset.range
            ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
          (thetaCorrectionWPolynomial x 1 0 i j).coeff k *
            thetaAuditedOneWeightedMoment x k) := by
  exact thetaAuditedSeriesTerm_one_weighted_moment_sum x i j
    (fun k _ => thetaAuditedOneWeightedMoment_integrable x hx hx1 k)

/-- On the full first audited cell, the ORIGINAL theta coefficient
is one finite moment sum plus its separately proved 10^(-35)
tail. There are no convergence or integrability premises left. -/
theorem thetaCoefficient_far_eq_weighted_moment_sum
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) :
    thetaCoefficient x i j =
      ((if i = j then
          (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
        else 0) -
        (x^2/4) *
          (∑ k ∈ Finset.range
              ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
            (thetaCorrectionWPolynomial x 1 0 i j).coeff k *
              thetaAuditedOneWeightedMoment x k)) +
      thetaAuditedTail 2 x i j := by
  have hx1 : x ≤ 1 := by linarith
  rw [thetaCoefficient_far_eq_one_add_tail x hx hxB i j,
    thetaAuditedSeriesTerm_one_weighted_moment_sum_unconditional
      x hx hx1 i j]



/-!
## Canonical nine-moment form, exactly matching the integer auditor

The existing Mathlib polynomial natDegree bound now makes it legal
to pad the finite weighted-moment sum by ZERO high coefficients.
This is an exact identity, not an approximation: all terms with
k > natDegree vanish. The external 768-bit code uses precisely the
same nine indices 0,...,8.
-/

/-- The original polynomial's finite weighted sum may always be
evaluated using exactly nine moments, for *arbitrary* moment data
g k, since all polynomial coefficients above its degree vanish.
No analytic approximation and no individual B_ij expansion. -/
theorem thetaCorrectionWPolynomial_sum_eq_nine
    (x p d : ℝ) (i j : Fin 5) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range
      ((thetaCorrectionWPolynomial x p d i j).natDegree + 1),
      (thetaCorrectionWPolynomial x p d i j).coeff k * g k) =
    ∑ k ∈ Finset.range 9,
      (thetaCorrectionWPolynomial x p d i j).coeff k * g k := by
  let P : Polynomial ℝ := thetaCorrectionWPolynomial x p d i j
  have hdeg : P.natDegree ≤ 8 :=
    thetaCorrectionWPolynomial_natDegree_le_eight x p d i j
  have hsubset : Finset.range (P.natDegree + 1) ⊆
      Finset.range 9 :=
    Finset.range_mono (by omega)
  change (∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * g k) =
      ∑ k ∈ Finset.range 9, P.coeff k * g k
  apply Finset.sum_subset hsubset
  intro k hkbig hkout
  have hkgt : P.natDegree < k := by
    have hn : ¬ k < P.natDegree + 1 := by
      intro hlt
      exact hkout (Finset.mem_range.mpr hlt)
    omega
  simp only [Polynomial.coeff_eq_zero_of_natDegree_lt hkgt, zero_mul]

/-- All 25 true original first-square theta coefficients reduce
to a signed diagonal minus a sum of exactly nine already proved
integrable weighted moments. No hidden convergence assumptions. -/
theorem thetaAuditedSeriesTerm_one_nine_weighted_moments
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) :
    thetaAuditedSeriesTerm x i j 1 =
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) -
      (x^2/4) *
        (∑ k ∈ Finset.range 9,
          (thetaCorrectionWPolynomial x 1 0 i j).coeff k *
            thetaAuditedOneWeightedMoment x k) := by
  rw [thetaAuditedSeriesTerm_one_weighted_moment_sum_unconditional
    x hx hx1 i j]
  rw [thetaCorrectionWPolynomial_sum_eq_nine]

/-- The genuine full theta matrix on the first audited cell is
a NINE-moment finite combination plus the separately proved
10^(-35) original infinite-series tail. -/
theorem thetaCoefficient_far_eq_nine_weighted_moments
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) :
    thetaCoefficient x i j =
      ((if i = j then
          (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
        else 0) -
        (x^2/4) *
          (∑ k ∈ Finset.range 9,
            (thetaCorrectionWPolynomial x 1 0 i j).coeff k *
              thetaAuditedOneWeightedMoment x k)) +
      thetaAuditedTail 2 x i j := by
  have hx1 : x ≤ 1 := by linarith
  rw [thetaCoefficient_far_eq_one_add_tail x hx hxB i j,
    thetaAuditedSeriesTerm_one_nine_weighted_moments x hx hx1 i j]

/-!
## Exact real soundness of the first-cell moment interval composition

The original integer auditor evaluates an interval polynomial and
multiplies its coefficients by moment intervals. We reuse EXISTING
QInterval.mul_containsReal and QInterval.finsetSum_containsReal,
rather than reproducing signed interval arithmetic or 51 LDL tests.

Inputs here are still uniform rational enclosures of x²/4,
the genuine polynomial coefficients and the genuinely weighted
moments. The theorems establish the exact real-semantic bridge,
not their numerical values.
-/

/-- The original auditor's finite signed interval computation:
the first-index diagonal, minus x²/4 times the finite sum of
original affine polynomial coefficients multiplied by true moments.
All products use the already proved signed four-corner arithmetic. -/
def thetaAuditedOneTermMomentInterval
    (D X : QInterval) (C M : ℕ → QInterval) (N : ℕ) : QInterval :=
  QInterval.sub D
    (QInterval.mul X
      (QInterval.finsetSum (Finset.range N)
        (fun k => QInterval.mul (C k) (M k))))

/-- An exact interval for the true first square-index theta term
follows from finite rational coefficient/moment interval inputs.
No analytic summability or integrability hypothesis remains. -/
theorem thetaAuditedOneTermMomentInterval_containsReal
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5)
    (D X : QInterval) (C M : ℕ → QInterval)
    (hdiag : QInterval.ContainsReal D
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0))
    (hscale : QInterval.ContainsReal X (x^2/4))
    (hcoeff : ∀ k ∈ Finset.range
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
      QInterval.ContainsReal (C k)
        ((thetaCorrectionWPolynomial x 1 0 i j).coeff k))
    (hmoment : ∀ k ∈ Finset.range
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
      QInterval.ContainsReal (M k)
        (thetaAuditedOneWeightedMoment x k)) :
    QInterval.ContainsReal
      (thetaAuditedOneTermMomentInterval D X C M
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1))
      (thetaAuditedSeriesTerm x i j 1) := by
  have hsum :=
    QInterval.finsetSum_containsReal
      (Finset.range
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1))
      (fun k => QInterval.mul (C k) (M k))
      (fun k =>
        (thetaCorrectionWPolynomial x 1 0 i j).coeff k *
          thetaAuditedOneWeightedMoment x k)
      (fun k hk => QInterval.mul_containsReal
        (hcoeff k hk) (hmoment k hk))
  have hfinal :=
    QInterval.sub_containsReal hdiag
      (QInterval.mul_containsReal hscale hsum)
  rw [thetaAuditedSeriesTerm_one_weighted_moment_sum_unconditional
    x hx hx1 i j]
  exact hfinal

/-- Reuse the already verified 10^(-35) tail and interval-addition
bridge to enclose the TRUE full theta coefficient on the first cell,
given only finite moment/affine-coefficient rational enclosures.
The remaining two rational endpoint inequalities are explicit. -/
theorem thetaCoefficient_first_cell_containsReal_of_moment_intervals
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5)
    (D X : QInterval) (C M : ℕ → QInterval)
    (Target : QInterval)
    (hdiag : QInterval.ContainsReal D
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0))
    (hscale : QInterval.ContainsReal X (x^2/4))
    (hcoeff : ∀ k ∈ Finset.range
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
      QInterval.ContainsReal (C k)
        ((thetaCorrectionWPolynomial x 1 0 i j).coeff k))
    (hmoment : ∀ k ∈ Finset.range
        ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1),
      QInterval.ContainsReal (M k)
        (thetaAuditedOneWeightedMoment x k))
    (hlo : Target.lo ≤
      (QInterval.add
        (thetaAuditedOneTermMomentInterval D X C M
          ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1))
        thetaAuditedTailErrorInterval).lo)
    (hhi :
      (QInterval.add
        (thetaAuditedOneTermMomentInterval D X C M
          ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1))
        thetaAuditedTailErrorInterval).hi ≤ Target.hi) :
    QInterval.ContainsReal Target (thetaCoefficient x i j) := by
  have hx1 : x ≤ 1 := by linarith
  exact thetaCoefficient_far_containsReal_of_one_term
    x hx hxB i j
    (thetaAuditedOneTermMomentInterval D X C M
      ((thetaCorrectionWPolynomial x 1 0 i j).natDegree + 1))
    Target
    (thetaAuditedOneTermMomentInterval_containsReal
      x hx hx1 i j D X C M hdiag hscale hcoeff hmoment)
    hlo hhi

end W5
