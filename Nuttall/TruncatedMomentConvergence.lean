import Nuttall.ThetaAndreief
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Nuttall

open Filter MeasureTheory Set
open scoped Topology BigOperators

/-- Cut off the same set of theta indices at each auxiliary derivative order. -/
noncomputable def auxiliarySignedJetTruncated (j N : ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, auxiliaryWeightedSummand (auxiliaryDerivativePolynomial j) n s

private theorem auxiliarySignedJetTruncated_continuous (j N : ℕ) :
    Continuous (auxiliarySignedJetTruncated j N) :=
  (show Differentiable ℝ (auxiliarySignedJetTruncated j N) from by
    intro t
    exact (HasDerivAt.fun_sum (u := Finset.range N)
      (fun n _ => auxiliary_polynomial_summand_hasDerivAt j n t)).differentiableAt).continuous

private theorem power_mul_truncation_integrable_and_tendsto (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∀ N : ℕ, IntegrableOn (fun s => (s-t)^k * auxiliarySignedJetTruncated j N s) (Ici t)) ∧
    Tendsto (fun N : ℕ => ∫ s in Ici t, (s-t)^k * auxiliarySignedJetTruncated j N s)
      atTop (𝓝 (∫ s in Ici t, (s-t)^k * auxiliarySignedJet j s)) := by
  obtain ⟨C, hC, hdecay⟩ := auxiliaryWeightedPartialSums_decay (auxiliaryDerivativePolynomial j)
  have hcont (N : ℕ) : Continuous (fun s => (s-t)^k * auxiliarySignedJetTruncated j N s) :=
    ((continuous_id.sub continuous_const).pow k).mul (auxiliarySignedJetTruncated_continuous j N)
  have hB := (polynomial_exp_integrable k ht).const_mul C
  have hb (N : ℕ) : ∀ᵐ s ∂volume.restrict (Ici t),
      ‖(s-t)^k * auxiliarySignedJetTruncated j N s‖ ≤ C * (s^k * Real.exp (-(1/2 : ℝ)*s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have hs0 : 0 ≤ s := ht.trans hs
    have hp : (s-t)^k ≤ s^k := pow_le_pow_left₀ (sub_nonneg.mpr hs) (sub_le_self _ ht) _
    have he : Real.exp (-s) ≤ Real.exp (-(1/2 : ℝ)*s) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr hs) _)]
    calc
      _ ≤ (s-t)^k * (C * Real.exp (-s)) :=
        mul_le_mul_of_nonneg_left (hdecay N s hs0) (pow_nonneg (sub_nonneg.mpr hs) _)
      _ ≤ s^k * (C * Real.exp (-(1/2 : ℝ)*s)) :=
        mul_le_mul hp (mul_le_mul_of_nonneg_left he hC) (by positivity) (pow_nonneg hs0 _)
      _ = _ := by ring
  refine ⟨fun N => hB.mono' (hcont N).aestronglyMeasurable (hb N), ?_⟩
  apply tendsto_integral_of_dominated_convergence _ (fun N => (hcont N).aestronglyMeasurable) hB hb
  exact Eventually.of_forall (fun s => tendsto_const_nhds.mul
    ((auxiliaryWeightedSummand_summable (auxiliaryDerivativePolynomial j) s).hasSum.tendsto_sum_nat))

theorem weighted_truncated_moment_integrable (k j N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s => tailMomentWeight k (s-t) * auxiliarySignedJetTruncated j N s) (Ici t) := by
  have hEq : (fun s => tailMomentWeight k (s-t) * auxiliarySignedJetTruncated j N s) =
      (fun s => (s-t)^k * auxiliarySignedJetTruncated j N s / (k.factorial : ℝ)) -
      (fun s => (s-t)^(k+1) * auxiliarySignedJetTruncated j N s / ((k+1).factorial : ℝ)) := by
    funext s
    simp only [tailMomentWeight, Pi.sub_apply, sub_mul, div_mul_eq_mul_div]
  rw [hEq]
  exact (((power_mul_truncation_integrable_and_tendsto k j ht).1 N).div_const _).sub
    (((power_mul_truncation_integrable_and_tendsto (k+1) j ht).1 N).div_const _)

theorem tendsto_weighted_truncated_moment (k j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ => ∫ s in Ici t, tailMomentWeight k (s-t) * auxiliarySignedJetTruncated j N s)
      atTop (𝓝 (∫ s in Ici t, tailMomentWeight k (s-t) * auxiliarySignedJet j s)) := by
  have normWeight (G : ℝ → ℝ)
      (h : IntegrableOn (fun s => (s-t)^k * G s) (Ici t))
      (h' : IntegrableOn (fun s => (s-t)^(k+1) * G s) (Ici t)) :
      (∫ s in Ici t, tailMomentWeight k (s-t) * G s) =
        (∫ s in Ici t, (s-t)^k * G s) / (k.factorial : ℝ) -
        (∫ s in Ici t, (s-t)^(k+1) * G s) / ((k+1).factorial : ℝ) := by
    simp only [tailMomentWeight, sub_mul, div_mul_eq_mul_div]
    rw [integral_sub (h.div_const _) (h'.div_const _), integral_div, integral_div]
  have h₀ := power_mul_truncation_integrable_and_tendsto k j ht
  have h₁ := power_mul_truncation_integrable_and_tendsto (k+1) j ht
  have heq : (fun N : ℕ => ∫ s in Ici t, tailMomentWeight k (s-t) * auxiliarySignedJetTruncated j N s) =
      fun N : ℕ =>
        (∫ s in Ici t, (s-t)^k * auxiliarySignedJetTruncated j N s) / (k.factorial : ℝ) -
        (∫ s in Ici t, (s-t)^(k+1) * auxiliarySignedJetTruncated j N s) / ((k+1).factorial : ℝ) := by
    funext N
    exact normWeight _ (h₀.1 N) (h₁.1 N)
  rw [heq]
  rw [normWeight _ (power_mul_signedJet_integrable k j ht) (power_mul_signedJet_integrable (k+1) j ht)]
  exact (h₀.2.div_const _).sub (h₁.2.div_const _)

/-- Reduce convergence of the multiple integrals to entrywise dominated
convergence in the paired moment matrices. -/
theorem tendsto_truncated_andreief {p : ℕ} (k : Fin p → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun N : ℕ => ∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySignedJetTruncated i.val N (x j))).det
      ∂Measure.pi (fun _ => volume.restrict (Ici t)))
      atTop (𝓝 (∫ x : Fin p → ℝ,
        (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
        (Matrix.of (fun (i j : Fin p) => auxiliarySignedJet i.val (x j))).det
        ∂Measure.pi (fun _ => volume.restrict (Ici t)))) := by
  let μ := volume.restrict (Ici t)
  let A (N : ℕ) : Matrix (Fin p) (Fin p) ℝ := Matrix.of (fun (i j : Fin p) =>
    ∫ s in Ici t, tailMomentWeight (k i) (s-t) * auxiliarySignedJetTruncated j.val N s)
  let B : Matrix (Fin p) (Fin p) ℝ := Matrix.of (fun (i j : Fin p) =>
    ∫ s in Ici t, tailMomentWeight (k i) (s-t) * auxiliarySignedJet j.val s)
  have hA (N : ℕ) : (p.factorial : ℝ) * (A N).det = ∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySignedJetTruncated i.val N (x j))).det
      ∂Measure.pi (fun _ => μ) :=
    Literature.andreief μ _ _ (fun i j => weighted_truncated_moment_integrable (k i) j.val N ht)
  have hB : (p.factorial : ℝ) * B.det = ∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySignedJet i.val (x j))).det
      ∂Measure.pi (fun _ => μ) :=
    Literature.andreief μ _ _ (fun i j => weight_mul_signedJet_integrable (k i) j.val ht)
  have h : Tendsto A atTop (𝓝 B) := by
    refine tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => ?_))
    exact tendsto_weighted_truncated_moment (k i) j.val ht
  simpa only [hA, hB] using
    (continuous_id.matrix_det.continuousAt.tendsto.comp h).const_mul (p.factorial : ℝ)

#print axioms tendsto_weighted_truncated_moment
#print axioms tendsto_truncated_andreief

end Nuttall
