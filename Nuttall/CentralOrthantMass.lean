import Nuttall.CentralOrthantSign
import Nuttall.RelativeIntegralTail
import Nuttall.ShiftRelativeTailRatio
import Nuttall.ShiftedWronskian

namespace Nuttall

open Filter MeasureTheory Set
open scoped BigOperators

/-- Product of the central open intervals in §4.1. -/
def thetaCentralCube (p : ℕ) (B : ℝ) : Set (Fin p → ℝ) :=
  univ.pi (fun _ => Ioo 0 B)

theorem measurableSet_thetaCentralCube (p : ℕ) (B : ℝ) :
    MeasurableSet (thetaCentralCube p B) := MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

private theorem measure_support_pos_of_central_nodes {p : ℕ} {B : ℝ} (hB : 0 < B)
    {F : (Fin p → ℝ) → ℝ}
    (hF : ∀ u ∈ thetaCentralCube p B, StrictMono u → 0 < F u) :
    0 < positiveOrthant p (Function.support F) := by
  let d := B / (p+1)
  have hd : 0 < d := by dsimp [d]; positivity
  let J (i : Fin p) := Ioo ((i.val:ℝ)*d) (((i.val:ℝ)+1)*d)
  let T := univ.pi J
  have hJpos (i : Fin p) : J i ⊆ Ioi (0:ℝ) := by
    intro x hx
    exact (mul_nonneg (by positivity : 0 ≤ (i.val:ℝ)) hd.le).trans_lt hx.1
  have hTmass : 0 < positiveOrthant p T := by
    rw [positiveOrthant, Measure.pi_pi]
    apply pos_iff_ne_zero.2
    refine Finset.prod_ne_zero_iff.2 (fun i _ => ?_)
    have hJi : MeasurableSet (J i) := measurableSet_Ioo
    rw [Measure.restrict_apply hJi, inter_eq_left.mpr (hJpos i)]
    change volume (Ioo ((i.val:ℝ)*d) (((i.val:ℝ)+1)*d)) ≠ 0
    rw [Real.volume_Ioo, ← pos_iff_ne_zero, ENNReal.ofReal_pos]
    nlinarith only [hd]
  have hsub : T ⊆ Function.support F := by
    intro u hu
    have hju (i : Fin p) : u i ∈ J i := hu i (mem_univ i)
    apply (hF u _ _).ne'
    · intro i _
      refine ⟨hJpos i (hju i), (hju i).2.trans ?_⟩
      have hi : (i.val:ℝ)+1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      have hdp : ((p:ℝ)+1)*d = B := by
        dsimp [d]
        field_simp
      have hi' := mul_le_mul_of_nonneg_right hi hd.le
      linarith
    · intro i j hij
      have hij' : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast Nat.succ_le_of_lt hij
      exact (hju i).2.trans ((mul_le_mul_of_nonneg_right hij' hd.le).trans_lt (hju j).1)
  exact hTmass.trans_le (measure_mono hsub)

/-- Central positivity supplies positive absolute mass. Once the relative
tail bound is given, the signed Wronskian is strictly positive. -/
theorem eventually_signed_wronskian_pos_of_relative_orthant_tail :
    ∀ᶠ r : ℕ in atTop, ∀ p : ℕ, 1 ≤ p → p ≤ r → ∀ t : ℝ, 0 ≤ t →
      let F := shiftedOrthantIntegrand (thetaScale t) (fun i _ : Fin p =>
        shiftedMoment (2*r-p+i.val-1))
      (∃ η < (1/2:ℝ), (∫ u in (thetaCentralCube p (shiftCriticalCutoff r))ᶜ, |F u|
        ∂positiveOrthant p) ≤ η * ∫ u, |F u| ∂positiveOrthant p) →
      0 < (-1 : ℝ)^(p*(p-1)/2) * wronskian (psi (2*r)) p t := by
  filter_upwards [eventually_shiftedOrthantIntegrand_central_sign,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually eventually_shiftCriticalCutoff_bounds] with
    r hr hcut p hp hpr t ht F htail
  obtain ⟨η, hη, htail⟩ := htail
  have hB : 0 < shiftCriticalCutoff r := hcut.2.1
  have hX : 0 < thetaScale t := mul_pos Real.pi_pos (Real.exp_pos _)
  have hF : Integrable F (positiveOrthant p) := integrable_shiftedOrthant hX _
  have hC := measurableSet_thetaCentralCube p (shiftCriticalCutoff r)
  have hcentral (u) (hu : u ∈ thetaCentralCube p (shiftCriticalCutoff r)) :=
    hr p hp hpr (thetaScale t) u (fun i => hu i (mem_univ i))
  have hmass : 0 < ∫ u, |F u| ∂positiveOrthant p := by
    apply (integral_pos_iff_support_of_nonneg (fun u => abs_nonneg (F u)) hF.abs).2
    apply measure_support_pos_of_central_nodes hB
    intro u hu hs
    exact abs_pos.2 ((hcentral u hu).2 hs.injective).ne'
  apply (signed_wronskian_pos_iff_shifted_orthant hp (by omega) t ht).2
  exact integral_pos_of_relative_tail hC hF
    ((ae_restrict_mem hC).mono (fun u hu => (hcentral u hu).1)) hmass hη htail

/-- For the eventual Wronskian bound it suffices to prove the relative mass
estimate with the explicit slice ratio from §4.1. -/
theorem eventually_signRegularWronskians_two_mul_of_shiftRelativeTailRatio
    (htail : ∀ᶠ r : ℕ in atTop, ∀ p : ℕ, 1 ≤ p → p ≤ r → ∀ t : ℝ, 0 ≤ t →
      let F := shiftedOrthantIntegrand (thetaScale t) (fun i _ : Fin p =>
        shiftedMoment (2*r-p+i.val-1))
      (∫ u in (thetaCentralCube p (shiftCriticalCutoff r))ᶜ, |F u| ∂positiveOrthant p) ≤
        ((p:ℝ) * shiftRelativeTailRatio r p (thetaScale t)) * ∫ u, |F u| ∂positiveOrthant p) :
    ∀ᶠ r : ℕ in atTop, signRegularWronskians (2*r) r := by
  filter_upwards [eventually_signed_wronskian_pos_of_relative_orthant_tail, htail,
    eventually_ge_atTop (4:ℕ)] with r hsign htail hr
  intro p hp hpr t ht
  have hX : Real.pi ≤ thetaScale t := by
    unfold thetaScale
    exact le_mul_of_one_le_right Real.pi_pos.le (Real.one_le_exp (by linarith))
  have hη := shiftRelativeTailRatio_mul_lt_quarter hr hpr hX
  exact hsign p hp hpr t ht ⟨_, hη.trans (by norm_num), htail p hp hpr t ht⟩

#print axioms eventually_signRegularWronskians_two_mul_of_shiftRelativeTailRatio

end Nuttall
