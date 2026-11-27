import Nuttall.ShiftCentralSlicePolynomial
import Nuttall.ShiftSliceGeometry
import Nuttall.ShiftSliceRootBound
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Nuttall

open Filter MeasureTheory Polynomial Set
open scoped BigOperators

/-- The absolute one-coordinate density, with all factors independent of that
coordinate removed. The coefficients of the moment combination are cofactors. -/
noncomputable def shiftSliceDensity {p n : ℕ} (L : ℕ) (c : Fin p → ℝ)
    (v : Fin n → ℝ) (X u : ℝ) : ℝ :=
  |∑ j : Fin p, c j * shiftedMoment (L+j.val-1) u| *
    (∏ j : Fin n, |Real.exp (4*u)-Real.exp (4*v j)|) * thetaOrthantWeight X u

theorem shiftSliceDensity_nonneg {p n : ℕ} (L : ℕ) (c : Fin p → ℝ)
    (v : Fin n → ℝ) (X u : ℝ) : 0 ≤ shiftSliceDensity L c v X u := by
  unfold shiftSliceDensity thetaOrthantWeight
  positivity

/-- The short interval contributes the explicit central mass from §4.1.
Here `j₀` is any maximal normalized cofactor index. -/
theorem shiftSlice_central_mass_lower {p n L : ℕ} (hL : 2 ≤ L) (hn : n ≤ p)
    (c : Fin p → ℝ) (j₀ : Fin p)
    (hmax : ∀ j, |c j / ((L+j.val).factorial:ℝ)| ≤ |c j₀ / ((L+j₀.val).factorial:ℝ)|)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) {X : ℝ} (hX : 0 ≤ X)
    (hInt : IntegrableOn (shiftSliceDensity L c v X) (Ioi 0)) :
    (|c j₀ / ((L+j₀.val).factorial:ℝ)| * ∏ i, (1+Real.exp (4*v i))) *
        (1/8:ℝ)^(L-1) * (1/(192*(p:ℝ)))^(2*p) * Real.exp (-Real.exp 1*X) / 16 ≤
      ∫ u in Ioi 0, shiftSliceDensity L c v X u := by
  classical
  let b (j : Fin p) := c j / ((L+j.val).factorial:ℝ)
  let Q := shiftCentralSlicePolynomial L b
  let P := Q.map (algebraMap ℝ ℂ)
  let δ : ℝ := 1/(64*(p:ℝ))
  let d : ℝ := δ/3
  let roots := P.roots.toFinset.image Complex.re
  let nodes := Finset.univ.image v
  let s := shiftSliceGoodSet (roots ∪ nodes) δ
  have hp : (1:ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := j₀.isLt; omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1/4 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < 64*(p:ℝ))).2
    linarith
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hdδ : d ≤ δ := by dsimp [d]; linarith
  have hd₁ : d ≤ 1 := by linarith
  have hd_eq : d = 1/(192*(p:ℝ)) := by dsimp [d,δ]; ring
  have hdeg : P.natDegree ≤ p := by
    dsimp [P]
    rw [natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]
    exact shiftCentralSlicePolynomial_natDegree_le _ _
  have hr : roots.card ≤ p :=
    ((Finset.card_image_le).trans (Multiset.toFinset_card_le _)).trans
      ((Polynomial.card_roots' P).trans hdeg)
  have hvcard : nodes.card ≤ n := Finset.card_image_le.trans (by simp)
  have hcard : ((roots ∪ nodes).card:ℝ) ≤ 2*(p:ℝ) := by
    exact_mod_cast ((Finset.card_union_le roots nodes).trans ((Nat.add_le_add hr hvcard).trans
      (show p+n ≤ 2*p by omega)))
  have hsize : ((roots ∪ nodes).card:ℝ)*(2*δ) ≤ 1/16 := by
    refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans ?_
    dsimp [δ]
    field_simp
  have hmass : 1/16 ≤ volume.real s := shiftSliceGoodSet_volume_lower _ hδ.le hsize
  let K := (|b j₀| * ∏ i, (1+Real.exp (4*v i))) * (1/8:ℝ)^(L-1) * d^(2*p) *
    Real.exp (-Real.exp 1*X)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : MeasurableSet s := measurableSet_shiftSliceGoodSet _ _
  have hsub : s ⊆ Ioi (0:ℝ) := fun u hu => (by norm_num : (0:ℝ) < 1/8).trans_le hu.1.1
  have hpoint (u : ℝ) (hu : u ∈ s) : K ≤ shiftSliceDensity L c v X u := by
    have hu₀ : 0 < u := hsub hu
    have hu₁ : u ≤ 1/4 := hu.1.2
    have hrsep (z : ℂ) (hz : z ∈ P.roots) : d*(1+‖z‖) ≤ ‖(u:ℂ)-z‖ :=
      relative_root_separation hu₀.le hu₁ hδ.le (by linarith) z
        (shiftSliceGoodSet_separates hu
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.2 hz))))
    have hQ : |b j₀| * d^p ≤ |Q.eval u| := by
      have h := coeff_norm_mul_pow_le_eval_norm P j₀.val p hdeg (u:ℂ) hd hd₁ hrsep
      have hc : ‖P.coeff j₀.val‖ = |Q.coeff j₀.val| := by
        simp [P, coeff_map, Complex.norm_real, Real.norm_eq_abs]
      have he : ‖P.eval (u:ℂ)‖ = |Q.eval u| := by
        rw [show (u:ℂ) = algebraMap ℝ ℂ u from rfl]
        simp only [P, eval_map, eval₂_at_apply]
        change ‖((Q.eval u : ℝ) : ℂ)‖ = |Q.eval u|
        rw [Complex.norm_real, Real.norm_eq_abs]
      rw [hc,he] at h
      exact (mul_le_mul_of_nonneg_right
        (abs_le_abs_shiftCentralSlicePolynomial_coeff_of_max hL b j₀ hmax) (pow_nonneg hd _)).trans h
    have hM : (1/8:ℝ)^(L-1) * (|b j₀| * d^p) ≤
        |∑ j : Fin p, c j * shiftedMoment (L+j.val-1) u| := by
      rw [shiftedMoment_linearCombination_eq_polynomial (by omega) c hu₀ hu₁,
        abs_mul, abs_of_nonneg (pow_nonneg hu₀.le _)]
      exact mul_le_mul (pow_le_pow_left₀ (by norm_num) hu.1.1 _) hQ (by positivity)
        (pow_nonneg hu₀.le _)
    have hV : ∏ i : Fin n, (d*(1+Real.exp (4*v i))) ≤
        ∏ i : Fin n, |Real.exp (4*u)-Real.exp (4*v i)| := by
      refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => ?_)
      have hi := shiftSliceGoodSet_separates hu
        (Finset.mem_union_right roots (Finset.mem_image_of_mem v (Finset.mem_univ i)))
      exact (mul_le_mul_of_nonneg_right hdδ (by positivity)).trans
        (separated_exp_four_sub_lower (hv i) hδ.le hδ' hi)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hV
    have hw := central_thetaOrthantWeight_lower hX hu₀.le hu₁
    have hp' : d^(2*p) ≤ d^p*d^n := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one hd hd₁ (by omega)
    calc
      K ≤ ((1/8:ℝ)^(L-1) * (|b j₀| * d^p)) *
          (d^n * ∏ i, (1+Real.exp (4*v i))) * Real.exp (-Real.exp 1*X) := by
        dsimp [K]
        calc
          _ ≤ |b j₀| * (∏ i, (1+Real.exp (4*v i))) * (1/8:ℝ)^(L-1) *
              (d^p*d^n) * Real.exp (-Real.exp 1*X) := by gcongr
          _ = _ := by ring
      _ ≤ _ := by unfold shiftSliceDensity; gcongr
  have hIntS := hInt.mono_set hsub
  have hSf : volume s ≠ ⊤ := measure_ne_top_of_subset (fun _ hu => hu.1) (by simp)
  have hConst : IntegrableOn (fun _ : ℝ => K) s := integrableOn_const hSf
  rw [← hd_eq]
  change K / 16 ≤ _
  calc
    K / 16 ≤ volume.real s * K := by linarith only [mul_le_mul_of_nonneg_right hmass hK]
    _ = ∫ _ in s, K := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ u in s, shiftSliceDensity L c v X u :=
      integral_mono_ae hConst hIntS ((ae_restrict_mem hs).mono hpoint)
    _ ≤ _ := setIntegral_mono_set hInt (Eventually.of_forall (shiftSliceDensity_nonneg _ _ _ _))
      (Eventually.of_forall hsub)

#print axioms shiftSlice_central_mass_lower

end Nuttall
