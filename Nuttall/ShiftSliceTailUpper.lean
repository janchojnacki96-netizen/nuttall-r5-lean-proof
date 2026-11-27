import Nuttall.ShiftSliceCentralLower
import Nuttall.ShiftSliceGamma
import Nuttall.ShiftSliceMomentUpper
import Nuttall.ShiftedMomentContinuity

namespace Nuttall

open Filter MeasureTheory Set
open scoped BigOperators

private theorem shiftSlice_density_tail_le {n L m : ℕ} (hL : 1 ≤ L)
    (hm : 2*(n+1) ≤ m) (hLm : L+(n+1) ≤ m+1)
    (c : Fin (n+1) → ℝ) (v : Fin n → ℝ) {F X B u : ℝ}
    (hF : 0 ≤ F) (hmax : ∀ j, |c j / ((L+j.val).factorial:ℝ)| ≤ F)
    (hX : 2 ≤ X) (hB : 0 ≤ B) (hu : B < u) :
    shiftSliceDensity L c v X u ≤
      ((m:ℝ)*(n+1)*2^(n+1)* (F*∏ j, (1+Real.exp (4*v j))) *
        Real.exp (-X*Real.exp (4*B)/2)) *
        (4*Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u))) := by
  have hu₀ : 0 ≤ u := hB.trans hu.le
  have hm₀ : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hV : (∏ j : Fin n, |Real.exp (4*u)-Real.exp (4*v j)|) ≤
      Real.exp (4*(n:ℝ)*u) * ∏ j, (1+Real.exp (4*v j)) := by
    calc
      _ ≤ ∏ j : Fin n, Real.exp (4*u)*(1+Real.exp (4*v j)) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_exp_four_sub_le hu₀)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_nat_mul]
        congr 2
        ring
  have hp : ((m:ℝ)+u)*(1+u)^m ≤ (m:ℝ)*Real.exp (((m:ℝ)+1)*u) := by
    have huE : 1+u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hmu : (m:ℝ)+u ≤ (m:ℝ)*Real.exp u := by
      have hmul := mul_le_mul_of_nonneg_left huE (show 0 ≤ (m:ℝ) by positivity)
      nlinarith only [hmul, mul_nonneg (sub_nonneg.2 hm₀) hu₀]
    calc
      _ ≤ ((m:ℝ)*Real.exp u)*(Real.exp u)^m :=
        mul_le_mul hmu (pow_le_pow_left₀ (by positivity) huE _) (by positivity) (by positivity)
      _ = _ := by
        rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hE : Real.exp u * Real.exp (((m:ℝ)+1)*u) * Real.exp (4*(n:ℝ)*u) *
      thetaOrthantWeight X u ≤
        Real.exp (-X*Real.exp (4*B)/2) * Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u)) := by
    simp only [thetaOrthantWeight, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hex := Real.exp_le_exp.2 (show 4*B ≤ 4*u by linarith)
    have h₁ := mul_le_mul_of_nonneg_left hex (show 0 ≤ X/2 by linarith)
    have h₂ := mul_nonneg (show 0 ≤ X/2-1 by linarith) (Real.exp_nonneg (4*u))
    have hn : (2:ℝ)*((n:ℝ)+1) ≤ m := by exact_mod_cast hm
    have hc : (1+((m:ℝ)+1)+4*(n:ℝ)+5) ≤ 4*((m:ℝ)+1) := by linarith
    have h₃ := mul_le_mul_of_nonneg_right hc hu₀
    nlinarith only [h₁,h₂,h₃]
  let H := F*∏ j, (1+Real.exp (4*v j))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hpow : (2:ℝ) ≤ 2^(n+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.succ_pos n)
  have hM := abs_shiftedMoment_linearCombination_le_envelope hL hLm c hu₀ hmax
  rw [Nat.cast_succ] at hM
  have hW : 0 ≤ thetaOrthantWeight X u := Real.exp_nonneg _
  calc
    _ ≤ ((2*Real.exp u)*(n+1)*F * (((m:ℝ)+u)*(1+u)^m)) *
          (Real.exp (4*(n:ℝ)*u)*∏ j, (1+Real.exp (4*v j))) * thetaOrthantWeight X u := by
      unfold shiftSliceDensity
      rw [← mul_assoc ((2*Real.exp u)*(n+1)*F) ((m:ℝ)+u) ((1+u)^m)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hM hV (by positivity) (by positivity))
        (by unfold thetaOrthantWeight; positivity)
    _ ≤ ((2*Real.exp u)*(n+1)*F * ((m:ℝ)*Real.exp (((m:ℝ)+1)*u))) *
          (Real.exp (4*(n:ℝ)*u)*∏ j, (1+Real.exp (4*v j))) * thetaOrthantWeight X u := by
      apply mul_le_mul_of_nonneg_right _ hW
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (2*(m:ℝ)*(n+1)*H) * (Real.exp u * Real.exp (((m:ℝ)+1)*u) *
          Real.exp (4*(n:ℝ)*u) * thetaOrthantWeight X u) := by dsimp [H]; ring
    _ ≤ _ := by
      have hc : 2*(m:ℝ)*(n+1)*H ≤ (m:ℝ)*(n+1)*2^(n+1)*H := by
        calc
          _ = ((m:ℝ)*(n+1)*H)*2 := by ring
          _ ≤ ((m:ℝ)*(n+1)*H)*2^(n+1) := mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = _ := by ring
      have hh := mul_le_mul hc hE (by unfold thetaOrthantWeight; positivity) (by positivity)
      have hpos := Real.exp_pos (4*((m:ℝ)+1)*u-Real.exp (4*u))
      calc
        _ ≤ ((m:ℝ)*(n+1)*2^(n+1)*H) *
            (Real.exp (-X*Real.exp (4*B)/2)*Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u))) := hh
        _ = ((m:ℝ)*(n+1)*2^(n+1)*H * Real.exp (-X*Real.exp (4*B)/2)) *
            Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The tail of the normalized one-coordinate density satisfies the upper
bound in §4.1, with the explicit Gamma factorial. -/
theorem shiftSlice_tail_mass_upper {n L m : ℕ} (hL : 2 ≤ L)
    (hm : 2*(n+1) ≤ m) (hLm : L+(n+1) ≤ m+1)
    (c : Fin (n+1) → ℝ) (v : Fin n → ℝ) {F X B : ℝ}
    (hF : 0 ≤ F) (hmax : ∀ j, |c j / ((L+j.val).factorial:ℝ)| ≤ F)
    (hX : 2 ≤ X) (hB : 0 ≤ B) :
    IntegrableOn (shiftSliceDensity L c v X) (Ioi 0) ∧
    (∫ u in Ioi B, shiftSliceDensity L c v X u) ≤
      (m:ℝ)*(n+1)*2^(n+1)*(F*∏ j, (1+Real.exp (4*v j))) *
        (m.factorial:ℝ)*Real.exp (-X*Real.exp (4*B)/2) := by
  let g (u : ℝ) := 4*Real.exp (4*((m:ℝ)+1)*u-Real.exp (4*u))
  let C (Y : ℝ) := (m:ℝ)*(n+1)*2^(n+1)*(F*∏ j, (1+Real.exp (4*v j))) *
    Real.exp (-X*Real.exp (4*Y)/2)
  have hC (Y : ℝ) : 0 ≤ C Y := by dsimp [C]; positivity
  have hg := exp_four_gamma_envelope m
  have hcont : Continuous (shiftSliceDensity L c v X) := by
    unfold shiftSliceDensity thetaOrthantWeight
    have hM (j : Fin (n+1)) : Continuous (shiftedMoment (L+j.val-1)) := by
      rw [show L+j.val-1 = (L+j.val-2)+1 by omega]
      exact continuous_shiftedMoment_succ _
    fun_prop
  have hInt : IntegrableOn (shiftSliceDensity L c v X) (Ioi 0) := by
    apply (hg.1.const_mul (C 0)).mono' hcont.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (shiftSliceDensity_nonneg L c v X u)]
    exact shiftSlice_density_tail_le (by omega) hm hLm c v hF hmax hX le_rfl hu
  refine ⟨hInt, ?_⟩
  have hsub : Ioi B ⊆ Ioi 0 := fun _ hu => hB.trans_lt hu
  have hCg : IntegrableOn (fun u => (C B)*g u) (Ioi 0) := hg.1.const_mul (C B)
  calc
    _ ≤ ∫ u in Ioi B, (C B)*g u := by
      apply integral_mono_ae (hInt.mono_set hsub) (hCg.mono_set hsub)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact shiftSlice_density_tail_le (by omega) hm hLm c v hF hmax hX hB hu
    _ ≤ ∫ u in Ioi (0:ℝ), (C B)*g u :=
      setIntegral_mono_set hCg
        (Eventually.of_forall (fun _ => mul_nonneg (hC _) (by dsimp [g]; positivity)))
        (Eventually.of_forall hsub)
    _ = (C B) * ∫ u in Ioi (0:ℝ), g u := integral_const_mul _ _
    _ ≤ (C B)*(m.factorial:ℝ) := mul_le_mul_of_nonneg_left hg.2 (hC _)
    _ = _ := by dsimp [C]; ring

#print axioms shiftSlice_tail_mass_upper

end Nuttall
