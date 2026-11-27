import Nuttall.ShiftedThetaOrthant
import Nuttall.ShiftedMomentBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Nuttall

open MeasureTheory Set Filter
open scoped BigOperators Topology

/-- The integrand of Section 4.1, with the moment columns supplied explicitly. -/
noncomputable def shiftedOrthantIntegrand {p : ℕ} (X : ℝ)
    (f : Fin p → Fin p → ℝ → ℝ) (u : Fin p → ℝ) : ℝ :=
  (Matrix.of (fun (i j : Fin p) => f i j (u j))).det *
    (Matrix.vandermonde (fun j => Real.exp (4*u j))).det *
    ∏ j : Fin p, thetaOrthantWeight X (u j)

private theorem abs_det_le_column_prod {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ)
    (b : Fin p → ℝ) (hb : ∀ j, 0 ≤ b j) (h : ∀ i j, |M i j| ≤ b j) :
    |M.det| ≤ (Nat.factorial p : ℝ) * ∏ j, b j := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin p),
        |(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * ∏ j, M (σ j) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Equiv.Perm (Fin p), ∏ j, b j := by
      apply Finset.sum_le_sum
      intro σ _
      have hs : |(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ)| = 1 := by
        exact_mod_cast Equiv.Perm.sign_abs σ
      rw [abs_mul, hs, one_mul, Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => h (σ j) j)
    _ = _ := by simp [Fintype.card_perm, nsmul_eq_mul]

private theorem abs_vandermonde_le_prod {p : ℕ} (u : Fin p → ℝ)
    (hu : ∀ j, 0 ≤ u j) :
    |(Matrix.vandermonde (fun j => Real.exp (4*u j))).det| ≤
      (Nat.factorial p : ℝ) * ∏ j, Real.exp (4*(p:ℝ)*u j) := by
  rw [← Matrix.det_transpose]
  apply abs_det_le_column_prod _ _ (fun _ => Real.exp_nonneg _)
  intro i j
  rw [Matrix.transpose_apply, Matrix.vandermonde_apply, abs_of_nonneg (by positivity),
    ← Real.exp_nat_mul, Real.exp_le_exp]
  have hij : (i.val : ℝ) ≤ p := by exact_mod_cast i.isLt.le
  calc
    (i.val : ℝ) * (4*u j) ≤ (p : ℝ) * (4*u j) :=
      mul_le_mul_of_nonneg_right hij (mul_nonneg (by norm_num) (hu j))
    _ = _ := by ring

private noncomputable def shiftedOrthantBound (p : ℕ) (X : ℝ) (u : Fin p → ℝ) : ℝ :=
  (Nat.factorial p : ℝ)^2 *
    ∏ j : Fin p, (4 * Real.exp (((3+4*(p:ℝ))+6)^2/(32*X))) * Real.exp (-u j)

private theorem shiftedOrthantBound_integrable (p : ℕ) (X : ℝ) :
    Integrable (shiftedOrthantBound p X) (positiveOrthant p) :=
  (Integrable.fintype_prod (fun _ : Fin p =>
    (integrableOn_exp_neg_Ioi 0).const_mul (4 * Real.exp (((3+4*(p:ℝ))+6)^2/(32*X))))).const_mul _

private theorem norm_shiftedOrthantIntegrand_le {p : ℕ} {X : ℝ} (hX : 0 < X)
    (f : Fin p → Fin p → ℝ → ℝ) (h : ∀ i j u, 0 ≤ u → |f i j u| ≤ 4 * Real.exp (3*u))
    (u : Fin p → ℝ) (hu : ∀ j, 0 ≤ u j) :
    ‖shiftedOrthantIntegrand X f u‖ ≤ shiftedOrthantBound p X u := by
  have hd := abs_det_le_column_prod (Matrix.of (fun i j => f i j (u j)))
    (fun j => 4 * Real.exp (3*u j)) (fun _ => by positivity) (fun i j => h i j (u j) (hu j))
  have hv := abs_vandermonde_le_prod u hu
  have hw : 0 ≤ ∏ j : Fin p, thetaOrthantWeight X (u j) := by
    unfold thetaOrthantWeight
    positivity
  rw [Real.norm_eq_abs, shiftedOrthantIntegrand, abs_mul, abs_mul, abs_of_nonneg hw]
  calc
    _ ≤ (((Nat.factorial p : ℝ) * ∏ j : Fin p, 4 * Real.exp (3*u j)) *
        ((Nat.factorial p : ℝ) * ∏ j : Fin p, Real.exp (4*(p:ℝ)*u j))) *
        ∏ j : Fin p, thetaOrthantWeight X (u j) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hd hv (abs_nonneg _) (by positivity)) hw
    _ = (Nat.factorial p : ℝ)^2 *
        ∏ j : Fin p, 4 * (Real.exp ((3+4*(p:ℝ))*u j) * thetaOrthantWeight X (u j)) := by
      rw [show ((Nat.factorial p : ℝ) * (∏ j : Fin p, 4 * Real.exp (3*u j))) *
          ((Nat.factorial p : ℝ) * (∏ j : Fin p, Real.exp (4*(p:ℝ)*u j))) *
          (∏ j : Fin p, thetaOrthantWeight X (u j)) =
          (Nat.factorial p : ℝ)^2 *
            (((∏ j : Fin p, 4 * Real.exp (3*u j)) *
              (∏ j : Fin p, Real.exp (4*(p:ℝ)*u j))) *
              (∏ j : Fin p, thetaOrthantWeight X (u j))) by ring]
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      rw [add_mul, Real.exp_add]
      ring
    _ ≤ _ := by
      unfold shiftedOrthantBound
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.prod_le_prod₀
      · intro j _
        unfold thetaOrthantWeight
        positivity
      · intro j _
        have hj := tilted_thetaOrthantWeight_le hX (3+4*(p:ℝ)) (hu j)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hj (by norm_num : (0:ℝ) ≤ 4)

private theorem ae_nonneg_positiveOrthant (p : ℕ) :
    ∀ᵐ u ∂positiveOrthant p, ∀ j, 0 ≤ u j := by
  apply eventually_all.2
  intro j
  apply (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin p => volume.restrict (Ioi (0 : ℝ))) (i := j)).eventually
  exact (ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi).mono
    (fun _ h => (mem_Ioi.mp h).le)

private theorem measurable_shiftedMomentTerm (k n : ℕ) : Measurable (shiftedMomentTerm k n) := by
  unfold shiftedMomentTerm
  have hs : MeasurableSet {u : ℝ | 0 < n ∧ thetaKnot n < u} :=
    MeasurableSet.inter (by
      change MeasurableSet { _ : ℝ | 0 < n }
      by_cases h : 0 < n <;> simp [h]) measurableSet_Ioi
  apply Measurable.ite hs
  · unfold tailMomentWeight
    fun_prop
  · exact measurable_const

private theorem measurable_shiftedOrthantIntegrand {p : ℕ} (X : ℝ)
    (f : Fin p → Fin p → ℝ → ℝ) (h : ∀ i j, Measurable (f i j)) :
    Measurable (shiftedOrthantIntegrand X f) := by
  unfold shiftedOrthantIntegrand
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · simp only [Matrix.det_apply', Matrix.of_apply]
    exact Finset.measurable_sum _ (fun σ _ =>
      measurable_const.mul (Finset.measurable_prod _ (fun j _ => (h (σ j) j).comp (measurable_pi_apply j))))
  · have hc : Continuous (fun u : Fin p → ℝ =>
        (Matrix.vandermonde (fun j => Real.exp (4*u j))).det) := by
      simp only [Matrix.det_apply', Matrix.vandermonde_apply]
      fun_prop
    exact hc.measurable
  · exact (by
      unfold thetaOrthantWeight
      fun_prop : Continuous fun u : Fin p → ℝ => ∏ j : Fin p, thetaOrthantWeight X (u j)).measurable

/-- All fixed tuples, including tuples containing zero, are absolutely integrable on
the common orthant. -/
theorem integrable_shiftedOrthant_term {p : ℕ} {X : ℝ} (hX : 0 < X)
    (k n : Fin p → ℕ) :
    Integrable (shiftedOrthantIntegrand X (fun i j => shiftedMomentTerm (k i) (n j)))
      (positiveOrthant p) := by
  refine (shiftedOrthantBound_integrable p X).mono'
    (measurable_shiftedOrthantIntegrand _ _ (fun i j => measurable_shiftedMomentTerm (k i) (n j))).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_positiveOrthant p] with u hu
  apply norm_shiftedOrthantIntegrand_le hX _ _ u hu
  intro i j v hv
  exact (abs_shiftedMomentTerm_le (k i) (n j) hv).trans (by
    have he := Real.exp_le_exp.mpr (show v ≤ 3*v by linarith)
    linarith [Real.exp_pos (3*v)])

private theorem measurable_shiftedMomentTruncated (j N : ℕ) :
    Measurable (shiftedMomentTruncated j N) :=
  Finset.measurable_sum _ (fun n _ => measurable_shiftedMomentTerm j n)

private theorem measurable_shiftedMoment (j : ℕ) : Measurable (shiftedMoment j) := by
  apply measurable_of_tendsto_metrizable (measurable_shiftedMomentTruncated j)
  apply tendsto_pi_nhds.2
  intro u
  apply tendsto_const_nhds.congr'
  exact eventually_atTop.2 ⟨_, fun N hN => (shiftedMomentTruncated_eq_of_ge_ceil j N u hN).symm⟩

/-- The untruncated integrand is absolutely integrable on the positive orthant. -/
theorem integrable_shiftedOrthant {p : ℕ} {X : ℝ} (hX : 0 < X) (k : Fin p → ℕ) :
    Integrable (shiftedOrthantIntegrand X (fun i _ => shiftedMoment (k i)))
      (positiveOrthant p) := by
  refine (shiftedOrthantBound_integrable p X).mono'
    (measurable_shiftedOrthantIntegrand _ _ (fun i _ => measurable_shiftedMoment (k i))).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_positiveOrthant p] with u hu
  exact norm_shiftedOrthantIntegrand_le hX _ (fun i _ _ hv => abs_shiftedMoment_le (k i) hv) u hu

/-- Finite cutoffs of the shifted theta indices converge under the integral. -/
theorem tendsto_shiftedOrthant_integral {p : ℕ} {X : ℝ} (hX : 0 < X) (k : Fin p → ℕ) :
    Tendsto (fun N => ∫ u, shiftedOrthantIntegrand X (fun i _ => shiftedMomentTruncated (k i) N) u
      ∂positiveOrthant p) atTop
      (𝓝 (∫ u, shiftedOrthantIntegrand X (fun i _ => shiftedMoment (k i)) u ∂positiveOrthant p)) := by
  refine tendsto_integral_of_dominated_convergence (shiftedOrthantBound p X)
    (fun N => (measurable_shiftedOrthantIntegrand _ _ (fun i _ =>
      measurable_shiftedMomentTruncated (k i) N)).aestronglyMeasurable)
    (shiftedOrthantBound_integrable p X) ?_ ?_
  · intro N
    filter_upwards [ae_nonneg_positiveOrthant p] with u hu
    exact norm_shiftedOrthantIntegrand_le hX _ (fun i _ _ hv => abs_shiftedMomentTruncated_le (k i) N hv) u hu
  · filter_upwards with u
    apply tendsto_const_nhds.congr'
    refine eventually_atTop.2 ⟨Finset.univ.sup (fun j : Fin p => ⌈Real.exp (2*u j)⌉₊), ?_⟩
    intro N hN
    have hmat : (Matrix.of (fun (i j : Fin p) => shiftedMoment (k i) (u j))) =
        Matrix.of (fun (i j : Fin p) => shiftedMomentTruncated (k i) N (u j)) := by
      ext i j
      exact (shiftedMomentTruncated_eq_of_ge_ceil (k i) N (u j)
        ((Finset.le_sup (f := fun j : Fin p => ⌈Real.exp (2*u j)⌉₊) (Finset.mem_univ j)).trans hN)).symm
    simp only [shiftedOrthantIntegrand, hmat]

#print axioms integrable_shiftedOrthant_term
#print axioms integrable_shiftedOrthant
#print axioms tendsto_shiftedOrthant_integral

end Nuttall
