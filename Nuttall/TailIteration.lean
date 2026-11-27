import Nuttall.ThetaAuxiliaryIntegral
import W5.PsiFundamentalDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Nuttall

open MeasureTheory Set

/-- Repeated upper-tail integrals, with level zero equal to the input function. -/
noncomputable def tailIterate (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | j + 1 => tailIntegral (tailIterate f j)

private theorem exp_neg_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
  simpa only [Function.comp_def, id_eq, mul_neg_one] using
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg

private theorem exp_neg_integrableOn_Ici (t : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ici t) := by
  have hn : IntegrableOn (fun x : ℝ => -Real.exp (-x)) (Ioi t) :=
    integrableOn_Ioi_deriv_of_nonpos' (fun x _ => exp_neg_hasDerivAt x)
      (fun x _ => neg_nonpos.mpr (Real.exp_pos _).le) Real.tendsto_exp_neg_atTop_nhds_zero
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrable_neg_iff.mp hn)

private theorem tailIntegral_exp_neg (t : ℝ) :
    tailIntegral (fun x : ℝ => Real.exp (-x)) t = Real.exp (-t) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonpos' (a := t) (fun x _ => exp_neg_hasDerivAt x)
    (fun x _ => neg_nonpos.mpr (Real.exp_pos _).le) Real.tendsto_exp_neg_atTop_nhds_zero
  rw [MeasureTheory.integral_neg, zero_sub, neg_inj] at h
  simpa only [tailIntegral, integral_Ici_eq_integral_Ioi] using h

private def TailBound (C : ℝ) (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ f x ∧ f x ≤ C * Real.exp (-x)

private theorem TailBound.integrableOn (h : TailBound C f) (t : ℝ) :
    IntegrableOn f (Ici t) := by
  have h0 : IntegrableOn f (Ici (0 : ℝ)) := by
    refine ((exp_neg_integrableOn_Ici 0).const_mul C).mono' h.1.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (h.2 x hx).1]
    exact (h.2 x hx).2
  have hc : IntegrableOn f (Icc (min t 0) 0) := h.1.integrableOn_Icc
  apply (integrableOn_union.mpr ⟨hc, h0⟩).mono_set
  intro x hx
  exact (le_total x 0).elim
    (fun hle => Or.inl ⟨(min_le_left _ _).trans hx, hle⟩)
    (fun hge => Or.inr hge)

/-- Differentiating a continuous integrable upper tail recovers the integrand
with a minus sign. Integrability on every upper half-line permits the choice
of a common finite reference point. -/
theorem tailIntegral_hasDerivAt {f : ℝ → ℝ} (hc : Continuous f)
    (hi : ∀ t : ℝ, IntegrableOn f (Ici t)) (t : ℝ) :
    HasDerivAt (tailIntegral f) (-f t) t := by
  have hfun :
      (fun u : ℝ => tailIntegral f 0 - ∫ x in (0 : ℝ)..u, f x) = tailIntegral f := by
    funext u
    have h := intervalIntegral.integral_Ici_sub_Ici' (hi 0) (hi u)
    change tailIntegral f 0 - tailIntegral f u = (∫ x in (0 : ℝ)..u, f x) at h
    dsimp
    linarith
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.aestronglyMeasurable.stronglyMeasurableAtFilter) hc.continuousAt
  simpa only [hfun] using hd.const_sub (tailIntegral f 0)

private theorem TailBound.tail (h : TailBound C f) : TailBound C (tailIntegral f) := by
  refine ⟨?_, ?_⟩
  · have hd : Differentiable ℝ (tailIntegral f) :=
      fun t => (tailIntegral_hasDerivAt h.1 h.integrableOn t).differentiableAt
    exact hd.continuous
  · intro t ht
    constructor
    · apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact (h.2 x (ht.trans hx)).1
    · have hi := (exp_neg_integrableOn_Ici t).const_mul C
      have hle : ∀ᵐ x ∂volume.restrict (Ici t), f x ≤ C * Real.exp (-x) := by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact (h.2 x (ht.trans hx)).2
      calc
        tailIntegral f t ≤ ∫ x in Ici t, C * Real.exp (-x) :=
          integral_mono_ae (h.integrableOn t) hi hle
        _ = C * Real.exp (-t) := by
          rw [integral_const_mul]
          exact congrArg (C * ·) (tailIntegral_exp_neg t)

private theorem auxiliaryTheta_tailBound : TailBound (auxiliaryTheta 0) auxiliaryTheta := by
  have hd : Differentiable ℝ auxiliaryTheta :=
    fun x => (auxiliaryTheta_hasDerivAt x).differentiableAt
  exact ⟨hd.continuous, fun x hx => ⟨auxiliaryTheta_nonneg x, auxiliaryTheta_le_exp_decay x hx⟩⟩

private theorem psi_one_tailBound : TailBound (auxiliaryTheta 0 / 2) (psi 1) := by
  refine ⟨?_, ?_⟩
  · rw [psi_one]
    have hd : Differentiable ℝ W5.Psi1 :=
      fun x => (W5.Psi1_hasDerivAt x).differentiableAt
    exact hd.continuous
  · intro t ht
    have hp : 0 ≤ psi 1 t := (W5.Psi1_pos t ht).le
    have htail := (auxiliaryTheta_tailBound.tail.2 t ht).1
    refine ⟨hp, ?_⟩
    have h := twice_psi_one_eq_auxiliary_sub_tail t ht
    have hg := auxiliaryTheta_le_exp_decay t ht
    linarith

private theorem tailIterate_auxiliary_bound (j : ℕ) :
    TailBound (auxiliaryTheta 0) (tailIterate auxiliaryTheta j) := by
  induction j with
  | zero => exact auxiliaryTheta_tailBound
  | succ j ih => exact ih.tail

private theorem psi_succ_bound (j : ℕ) :
    TailBound (auxiliaryTheta 0 / 2) (psi (j+1)) := by
  induction j with
  | zero => exact psi_one_tailBound
  | succ j ih => exact ih.tail

theorem tailIterate_auxiliary_integrableOn (j : ℕ) (t : ℝ) :
    IntegrableOn (tailIterate auxiliaryTheta j) (Ici t) :=
  (tailIterate_auxiliary_bound j).integrableOn t

theorem psi_integrableOn (j : ℕ) (t : ℝ) : IntegrableOn (psi j) (Ici t) := by
  cases j with
  | zero => exact W5.Phi_integrableOn_Ici_all t
  | succ j => exact (psi_succ_bound j).integrableOn t

theorem psi_continuous (j : ℕ) : Continuous (psi j) := by
  cases j with
  | zero => exact W5.Phi_differentiable.continuous
  | succ j => exact (psi_succ_bound j).1

theorem tailIterate_auxiliary_continuous (j : ℕ) :
    Continuous (tailIterate auxiliaryTheta j) :=
  (tailIterate_auxiliary_bound j).1

/-- Section 4.1, after any number of tail integrations. -/
theorem twice_psi_succ_eq_auxiliary_iterate_sub (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    2 * psi (j+1) t = tailIterate auxiliaryTheta j t - tailIterate auxiliaryTheta (j+1) t := by
  induction j generalizing t with
  | zero => exact twice_psi_one_eq_auxiliary_sub_tail t ht
  | succ j ih =>
    let g := tailIterate auxiliaryTheta j
    let gnext := tailIterate auxiliaryTheta (j+1)
    have hEq : ∀ᵐ x ∂volume.restrict (Ici t), 2 * psi (j+1) x = g x - gnext x := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact ih x (ht.trans hx)
    have hi := integral_congr_ae hEq
    rw [integral_const_mul, integral_sub
      (tailIterate_auxiliary_integrableOn j t)
      (tailIterate_auxiliary_integrableOn (j+1) t)] at hi
    exact hi

#print axioms twice_psi_succ_eq_auxiliary_iterate_sub

end Nuttall
