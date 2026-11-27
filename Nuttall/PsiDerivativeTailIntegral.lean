import Nuttall.PsiHankelJets
import Mathlib.MeasureTheory.Integral.ExpDecay

namespace Nuttall

open Filter MeasureTheory Set
open scoped ContDiff Topology

private theorem phi_iteratedDeriv_exp_bound (d : ℕ) :
    ∃ C : ℝ, ∀ t ≥ 0, ‖iteratedDeriv d W5.Phi t‖ ≤ C * Real.exp (-t) := by
  obtain ⟨C, _, hC⟩ := auxiliaryWeightedSeries_decay (phiJetPolynomial d)
  exact ⟨C, fun t ht => by rw [iteratedDeriv_phi_eq_tsum]; exact hC t ht⟩

theorem integrableOn_iteratedDeriv_psi_Ioi (m d : ℕ) (t : ℝ) :
    IntegrableOn (iteratedDeriv d (psi m)) (Ioi t) := by
  induction m generalizing d with
  | zero =>
    obtain ⟨C, hC⟩ := phi_iteratedDeriv_exp_bound d
    apply integrable_of_isBigO_exp_neg (b := 1) (by norm_num)
      ((contDiff_psi 0).continuous_iteratedDeriv d (by simp)).continuousOn
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    simpa only [psi, neg_mul, one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      using hC s hs
  | succ m ih =>
    cases d with
    | zero =>
      simpa only [iteratedDeriv_zero] using
        (psi_integrableOn (m+1) t).mono_set Ioi_subset_Ici_self
    | succ d =>
      have he : iteratedDeriv (d+1) (psi (m+1)) = fun x => -iteratedDeriv d (psi m) x :=
        funext (iteratedDeriv_succ_psi_succ m d)
      rw [he]
      exact (ih d).neg

theorem iteratedDeriv_psi_tendsto_zero (m d : ℕ) :
    Tendsto (iteratedDeriv d (psi m)) atTop (𝓝 0) := by
  induction m generalizing d with
  | zero =>
    obtain ⟨C, hC⟩ := phi_iteratedDeriv_exp_bound d
    have hlim : Tendsto (fun t => C * Real.exp (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
    exact squeeze_zero_norm' ((eventually_ge_atTop (0:ℝ)).mono hC) hlim
  | succ m ih =>
    cases d with
    | zero =>
      rw [iteratedDeriv_zero]
      have he : psi (m+1) = fun t => ∫ x in Ioi t, psi m x := by
        funext x
        simp only [psi, tailIntegral, integral_Ici_eq_integral_Ioi]
      rw [he]
      exact tendsto_integral_Ioi_zero tendsto_id
    | succ d =>
      have he : iteratedDeriv (d+1) (psi (m+1)) = fun x => -iteratedDeriv d (psi m) x :=
        funext (iteratedDeriv_succ_psi_succ m d)
      rw [he]
      simpa only [neg_zero] using (ih d).neg

/-- Every derivative row of the integrated kernel can be written by integrating
the corresponding derivative row of the preceding level. -/
theorem iteratedDeriv_psi_succ_eq_integral_Ioi (m d : ℕ) (t : ℝ) :
    iteratedDeriv d (psi (m+1)) t = ∫ x in Ioi t, iteratedDeriv d (psi m) x := by
  cases d with
  | zero => simp only [iteratedDeriv_zero, psi, tailIntegral, integral_Ici_eq_integral_Ioi]
  | succ d =>
    have hderiv (x : ℝ) : HasDerivAt (iteratedDeriv d (psi m))
        (iteratedDeriv (d+1) (psi m) x) x := by
      rw [iteratedDeriv_succ]
      exact ((contDiff_psi m).differentiable_iteratedDeriv d
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl d) x).hasDerivAt
    have hf := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x)
      (integrableOn_iteratedDeriv_psi_Ioi m (d+1) t) (iteratedDeriv_psi_tendsto_zero m d)
    rw [iteratedDeriv_succ_psi_succ m d]
    simpa only [zero_sub] using hf.symm

#print axioms iteratedDeriv_psi_succ_eq_integral_Ioi

end Nuttall
