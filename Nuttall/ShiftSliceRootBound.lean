import Mathlib.Analysis.Complex.Polynomial.Basic

namespace Nuttall

open Polynomial

/-- Multiplying by a linear factor increases a common coefficient bound by
at most one plus the norm of its root. -/
private theorem norm_coeff_product_linear_le (a : ℂ) (roots : Multiset ℂ) (k : ℕ) :
    ‖((C a * (roots.map (X - C ·)).prod).coeff k)‖ ≤
      ‖a‖ * (roots.map (fun z => 1 + ‖z‖)).prod := by
  induction roots using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, coeff_C]
    split <;> simp
  | cons z roots ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    let P := C a * (roots.map (X - C ·)).prod
    let K := ‖a‖ * (roots.map (fun z => 1 + ‖z‖)).prod
    have hK (j) : ‖P.coeff j‖ ≤ K := ih j
    have hP : C a * ((X-C z)*(roots.map (X-C ·)).prod) = P*(X-C z) := by simp [P, mul_comm, mul_left_comm]
    have hmul (j) : ‖P.coeff j‖ * ‖z‖ ≤ K * ‖z‖ := mul_le_mul_of_nonneg_right (hK j) (norm_nonneg _)
    have hR : ‖a‖ * ((1+‖z‖)*(roots.map (fun t => 1+‖t‖)).prod) = K + K*‖z‖ := by
      dsimp [K]
      ring
    rw [hP, hR]
    cases k with
    | zero =>
      rw [mul_sub, coeff_sub, coeff_mul_X_zero, coeff_mul_C, zero_sub, norm_neg, norm_mul]
      exact (hmul 0).trans (le_add_of_nonneg_left ((norm_nonneg _).trans (hK 0)))
    | succ k =>
      rw [coeff_mul_X_sub_C]
      exact (norm_sub_le _ _).trans (by rw [norm_mul]; exact add_le_add (hK k) (hmul (k+1)))

private theorem root_scale_prod_nonneg (r : Multiset ℂ) :
    0 ≤ (r.map (fun z => 1+‖z‖)).prod := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_nonneg (by positivity) ih

private theorem norm_multiset_prod_complex (r : Multiset ℂ) :
    ‖r.prod‖ = (r.map (fun z => ‖z‖)).prod := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons z s ih => simp [ih]

private theorem prod_root_norm_le (roots : Multiset ℂ) (x : ℂ) {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ z ∈ roots, d*(1+‖z‖) ≤ ‖x-z‖) :
    d^roots.card * (roots.map (fun z => 1+‖z‖)).prod ≤ (roots.map (fun z => ‖x-z‖)).prod := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons a roots ih =>
    rw [Multiset.card_cons, pow_succ]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    calc
      _ = (d*(1+‖a‖)) * (d^roots.card * (roots.map (fun z => 1+‖z‖)).prod) := by ring
      _ ≤ ‖x-a‖ * (roots.map (fun z => ‖x-z‖)).prod :=
        mul_le_mul (h a (Multiset.mem_cons_self _ _))
          (ih (fun z hz => h z (Multiset.mem_cons_of_mem hz)))
          (mul_nonneg (pow_nonneg hd _) (root_scale_prod_nonneg _)) (norm_nonneg _)

/-- A coefficient controls the value of a polynomial away from its roots,
with a bound depending only on the degree and the relative root separation. -/
theorem coeff_norm_mul_pow_le_eval_norm (P : ℂ[X]) (k p : ℕ) (hp : P.natDegree ≤ p)
    (x : ℂ) {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1)
    (h : ∀ z ∈ P.roots, d*(1+‖z‖) ≤ ‖x-z‖) :
    ‖P.coeff k‖ * d^p ≤ ‖P.eval x‖ := by
  have hs : P.Splits := IsAlgClosed.splits _
  have hc : ‖P.coeff k‖ ≤ ‖P.leadingCoeff‖ * (P.roots.map (fun z => 1+‖z‖)).prod := by
    conv_lhs => rw [hs.eq_prod_roots]
    exact norm_coeff_product_linear_le _ _ _
  have hpow : d^p ≤ d^P.roots.card :=
    pow_le_pow_of_le_one hd₀ hd₁ (hs.natDegree_eq_card_roots ▸ hp)
  have hev : ‖P.eval x‖ = ‖P.leadingCoeff‖ * (P.roots.map (fun z => ‖x-z‖)).prod := by
    rw [hs.eval_eq_prod_roots, norm_mul, norm_multiset_prod_complex]
    simp [Multiset.map_map]
  calc
    _ ≤ ‖P.coeff k‖ * d^P.roots.card := mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ ≤ (‖P.leadingCoeff‖ * (P.roots.map (fun z => 1+‖z‖)).prod) * d^P.roots.card :=
      mul_le_mul_of_nonneg_right hc (pow_nonneg hd₀ _)
    _ = ‖P.leadingCoeff‖ * (d^P.roots.card * (P.roots.map (fun z => 1+‖z‖)).prod) := by ring
    _ ≤ _ := hev ▸ mul_le_mul_of_nonneg_left (prod_root_norm_le _ _ hd₀ h) (norm_nonneg _)

/-- A real point in the central interval lies at relative distance at least
`δ/3` when its distance to the real part of a root is at least `δ`. -/
theorem relative_root_separation {u δ : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/4)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (z : ℂ) (hz : δ ≤ |u-z.re|) :
    (δ/3)*(1+‖z‖) ≤ ‖(u:ℂ)-z‖ := by
  have h₁ : δ ≤ ‖(u:ℂ)-z‖ :=
    hz.trans (by simpa [Complex.sub_re] using Complex.abs_re_le_norm ((u:ℂ)-z))
  have h₂ : ‖z‖ ≤ ‖(u:ℂ)-z‖ + u := by
    have he : (z-(u:ℂ))+(u:ℂ) = z := sub_add_cancel _ _
    simpa only [he, norm_sub_rev z (u:ℂ), Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hu] using norm_add_le (z-(u:ℂ)) (u:ℂ)
  calc
    _ ≤ (δ/3)*(1+(‖(u:ℂ)-z‖+u)) := by gcongr
    _ ≤ ‖(u:ℂ)-z‖ := by
      have h₃ := mul_le_mul_of_nonneg_left hu' hδ
      have h₄ := mul_le_mul_of_nonneg_right hδ' (norm_nonneg ((u:ℂ)-z))
      nlinarith only [h₁, h₃, h₄]

#print axioms coeff_norm_mul_pow_le_eval_norm
#print axioms relative_root_separation

end Nuttall
