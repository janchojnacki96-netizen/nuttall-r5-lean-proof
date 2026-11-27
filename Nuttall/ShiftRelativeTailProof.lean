import Nuttall.ShiftSliceTailUpper
import Nuttall.ShiftSliceFactorization
import Nuttall.ShiftedOrthantSliceBound

namespace Nuttall

open Filter MeasureTheory Set
open scoped BigOperators

/-- Comparison of the upper tail and lower central mass on the normalized
one-coordinate section. The common cofactor scale cancels algebraically,
so no division by that scale is required. -/
theorem shiftSlice_relative_tail_le {r n : ℕ} (hr : 2 ≤ r) (hp : n+1 ≤ r)
    {X : ℝ} (hX : 2 ≤ X) (hB : 0 ≤ shiftCriticalCutoff r)
    (c : Fin (n+1) → ℝ) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    let L := 2*r-(n+1)
    (∫ u in Ioi (shiftCriticalCutoff r), shiftSliceDensity L c v X u) ≤
      shiftRelativeTailRatio r (n+1) X * ∫ u in Ioi (0:ℝ), shiftSliceDensity L c v X u := by
  dsimp only
  let p := n+1
  let m := 2*r
  let L := m-p
  let B := shiftCriticalCutoff r
  let f (j : Fin (n+1)) := |c j / ((L+j.val).factorial:ℝ)|
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hmax (j : Fin (n+1)) : f j ≤ f j₀ := hj₀ j (Finset.mem_univ j)
  let H := f j₀ * ∏ i, (1+Real.exp (4*v i))
  have hL : 2 ≤ L := by dsimp [L,m,p]; omega
  have hm : 2*(n+1) ≤ m := by dsimp [m]; omega
  have hLm : L+(n+1) ≤ m+1 := by dsimp [L,p]; omega
  have hU := shiftSlice_tail_mass_upper hL hm hLm c v (abs_nonneg _) hmax hX hB
  have hD := shiftSlice_central_mass_lower hL (Nat.le_succ n) c j₀ hmax v hv
    (by linarith : 0 ≤ X) hU.1
  let a : ℝ := 8^(L-1)
  let b : ℝ := (192*(p:ℝ))^(2*p)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b,p]; positivity
  have ha' : (1/8:ℝ)^(L-1) = a⁻¹ := by dsimp [a]; rw [one_div, inv_pow]
  have hb' : (1/(192*(p:ℝ)))^(2*p) = b⁻¹ := by dsimp [b]; rw [one_div, inv_pow]
  let E := Real.exp (4*B)
  let e₁ := Real.exp (-X*(E/2-Real.exp 1))
  let e₂ := Real.exp (-Real.exp 1*X)
  have he : Real.exp (-X*E/2) = e₁*e₂ := by
    dsimp [e₁,e₂]
    rw [← Real.exp_add]
    congr 1
    ring
  change (∫ u in Ioi B, shiftSliceDensity L c v X u) ≤
    shiftRelativeTailRatio r p X * ∫ u in Ioi (0:ℝ), shiftSliceDensity L c v X u
  calc
    _ ≤ (m:ℝ)*(p:ℝ)*2^p*H*(m.factorial:ℝ)*Real.exp (-X*E/2) := by
      simpa only [p, Nat.cast_succ] using hU.2
    _ = shiftRelativeTailRatio r p X * (H*a⁻¹*b⁻¹*e₂/16) := by
      rw [he]
      change _ = (16*(m:ℝ)*(p:ℝ)*2^p*a*b*(m.factorial:ℝ)*e₁) * (H*a⁻¹*b⁻¹*e₂/16)
      field_simp [ha.ne', hb.ne']
      <;> ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by unfold shiftRelativeTailRatio; dsimp; positivity)
      rw [← ha', ← hb']
      exact hD

/-- The analytic eventual signed-Wronskian bound at level (2r).
It combines the central sign with the explicit relative estimate on the
complement and uses the existing Andréief identity. -/
theorem eventually_signRegularWronskians_two_mul :
    ∀ᶠ r : ℕ in atTop, signRegularWronskians (2*r) r := by
  apply eventually_signRegularWronskians_two_mul_of_shiftRelativeTailRatio
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    eventually_shiftCriticalCutoff_bounds, eventually_ge_atTop (2:ℕ)] with r hcut hr p hp hpr t ht
  cases p with
  | zero => omega
  | succ n =>
    let X := thetaScale t
    let L := 2*r-(n+1)
    have hX : 2 ≤ X := by
      have hscale : Real.pi ≤ X := by
        unfold X thetaScale
        exact le_mul_of_one_le_right Real.pi_pos.le (Real.one_le_exp (by linarith))
      linarith only [hscale, Real.pi_gt_three]
    apply integral_shiftedOrthant_compl_le_of_slices hcut.2.1 (by linarith : 0 < X)
    intro i
    have hvPos : ∀ᵐ v ∂positiveOrthant n, ∀ j, v j ∈ Ioi (0:ℝ) := by
      rw [ae_all_iff]
      intro j
      exact (Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin n => volume.restrict (Ioi (0:ℝ))) (i := j)).eventually
        (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hvPos] with v hv
    let A (x : ℝ) :=
      |shiftedOrthantIntegrand X (fun (j _ : Fin (n+1)) => shiftedMoment (L+j.val-1))
        (i.insertNth (α := fun _ => ℝ) x v)|
    let C := |(Matrix.vandermonde (fun j => Real.exp (4*v j))).det| *
      ∏ j, thetaOrthantWeight X (v j)
    have hA : A = fun x => C*shiftSliceDensity L (shiftSliceCofactor L i v) v X x :=
      funext (abs_shiftedOrthantIntegrand_insertNth L i v X)
    change (∫ x in Ioi (shiftCriticalCutoff r), A x) ≤
      shiftRelativeTailRatio r (n+1) X * ∫ x in Ioi (0:ℝ), A x
    rw [hA, integral_const_mul, integral_const_mul, mul_left_comm (shiftRelativeTailRatio r (n+1) X)]
    refine mul_le_mul_of_nonneg_left (shiftSlice_relative_tail_le hr hpr hX hcut.2.1.le _ _ ?_) ?_
    · exact fun j => (mem_Ioi.mp (hv j)).le
    · unfold C thetaOrthantWeight
      positivity

/-- For every positive prescribed rank some integration level has all of
the required strict Wronskian signs on the nonnegative half-line. -/
theorem exists_level_signRegularWronskians (r : ℕ) (hr : 1 ≤ r) :
    ∃ m : ℕ, signRegularWronskians m r := by
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 eventually_signRegularWronskians_two_mul
  exact exists_level_of_eventual_two_mul ⟨R₀, fun _ hR _ => hR₀ _ hR⟩ r hr

#print axioms shiftSlice_relative_tail_le
#print axioms eventually_signRegularWronskians_two_mul
#print axioms exists_level_signRegularWronskians

end Nuttall
