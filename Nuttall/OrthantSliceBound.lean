import Mathlib.MeasureTheory.Integral.Pi

namespace Nuttall

open Filter MeasureTheory Set
open scoped BigOperators

/-- Fubini isolates a single offending coordinate in a finite product. -/
theorem integral_coordinate_compl_le_of_slice {α : Type*} [MeasurableSpace α]
    {n : ℕ} (μ : Measure α) [SigmaFinite μ] (i : Fin (n+1))
    {s : Set α} (hs : MeasurableSet s) {F : (Fin (n+1) → α) → ℝ}
    (hF : Integrable F (Measure.pi (fun _ => μ))) (η : ℝ)
    (hSlice : ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      (∫ x in sᶜ, F (i.insertNth x v) ∂μ) ≤ η * ∫ x, F (i.insertNth x v) ∂μ) :
    (∫ u in {u | u i ∉ s}, F u ∂Measure.pi (fun _ => μ)) ≤
      η * ∫ u, F u ∂Measure.pi (fun _ => μ) := by
  let ν := Measure.pi (fun _ : Fin n => μ)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => α) i).symm
  have he : MeasurePreserving e (μ.prod ν) (Measure.pi (fun _ : Fin (n+1) => μ)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm _
  let T : Set (Fin (n+1) → α) := {u | u i ∉ s}
  have hT : MeasurableSet T :=
    (measurable_pi_apply (X := fun _ : Fin (n+1) => α) i) hs.compl
  let G := F ∘ e
  let H := T.indicator F ∘ e
  have hG : Integrable G (μ.prod ν) := (he.integrable_comp_emb e.measurableEmbedding).2 hF
  have hH : Integrable H (μ.prod ν) :=
    (he.integrable_comp_emb e.measurableEmbedding).2 (hF.indicator hT)
  change (∫ u in T, F u ∂_) ≤ _
  rw [← integral_indicator hT, ← he.integral_comp' (T.indicator F), ← he.integral_comp' F]
  change (∫ z, H z ∂μ.prod ν) ≤ η * ∫ z, G z ∂μ.prod ν
  rw [integral_prod_symm H hH, integral_prod_symm G hG, ← integral_const_mul]
  apply integral_mono_ae hH.integral_prod_right (hG.integral_prod_right.const_mul η)
  filter_upwards [hSlice] with v hv
  have hHx : (fun x => H (x,v)) = sᶜ.indicator (fun x => F (i.insertNth x v)) := by
    funext x
    have heq : e (x,v) = i.insertNth x v := rfl
    by_cases hx : x ∈ s <;> simp [H, T, heq, hx]
  rw [hHx, integral_indicator hs.compl]
  exact hv

/-- The complement of a product set is covered by the individual coordinate
tails. Adding the relative bounds gives one factor for each coordinate. -/
theorem integral_pi_compl_le_of_slices {α : Type*} [MeasurableSpace α]
    {n : ℕ} (μ : Measure α) [SigmaFinite μ] {s : Set α} (hs : MeasurableSet s)
    {F : (Fin (n+1) → α) → ℝ} (hF : Integrable F (Measure.pi (fun _ => μ)))
    (h0 : ∀ u, 0 ≤ F u) (η : ℝ)
    (hSlice : ∀ i : Fin (n+1), ∀ᵐ v ∂Measure.pi (fun _ : Fin n => μ),
      (∫ x in sᶜ, F (i.insertNth x v) ∂μ) ≤ η * ∫ x, F (i.insertNth x v) ∂μ) :
    (∫ u in (univ.pi (fun _ => s))ᶜ, F u ∂Measure.pi (fun _ => μ)) ≤
      ((n+1:ℕ):ℝ)*η * ∫ u, F u ∂Measure.pi (fun _ => μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin (n+1) => μ)
  let T (i : Fin (n+1)) : Set (Fin (n+1) → α) := {u | u i ∉ s}
  let C : Set (Fin (n+1) → α) := univ.pi (fun _ => s)
  have hT (i) : MeasurableSet (T i) :=
    (measurable_pi_apply (X := fun _ : Fin (n+1) => α) i) hs.compl
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _ => hs)
  change (∫ u in Cᶜ, F u ∂ν) ≤ _
  calc
    _ ≤ ∑ i, ∫ u in T i, F u ∂ν := by
      rw [← integral_indicator hC.compl]
      simp_rw [← integral_indicator (hT _)]
      rw [← integral_finsetSum Finset.univ (fun i _ => hF.indicator (hT i))]
      apply integral_mono (hF.indicator hC.compl)
        (integrable_finsetSum _ (fun i _ => hF.indicator (hT i)))
      intro u
      by_cases hu : u ∈ C
      · rw [indicator_of_notMem (not_not_intro hu)]
        exact Finset.sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => h0 _) _)
      · have he : ∃ i : Fin (n+1), u i ∉ s := by
          by_contra hn
          push Not at hn
          exact hu (fun i _ => hn i)
        obtain ⟨i, hi⟩ := he
        rw [indicator_of_mem hu]
        calc
          F u = (T i).indicator F u := (indicator_of_mem (show u ∈ T i from hi) _).symm
          _ ≤ _ := Finset.single_le_sum
            (fun j _ => indicator_nonneg (fun _ _ => h0 _) _) (Finset.mem_univ i)
    _ ≤ ∑ _i : Fin (n+1), η * ∫ u, F u ∂ν :=
      Finset.sum_le_sum (fun i _ => integral_coordinate_compl_le_of_slice μ i hs hF η (hSlice i))
    _ = _ := by simp [nsmul_eq_mul, mul_assoc, ν]

#print axioms integral_pi_compl_le_of_slices

end Nuttall
