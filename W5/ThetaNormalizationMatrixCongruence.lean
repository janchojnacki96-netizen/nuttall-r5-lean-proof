import W5.ThetaNormalizationJetRows
import W5.ThetaOriginalKernelAllMixedJetsFromLocalEqOn
import W5.ThetaActualAnalyticCoefficientSignsFrom51Cells
import W5.PositiveScalarCongruence

namespace W5
open Filter
open scoped Topology

/-- Exact original kernel on the positive logarithm patch. -/
theorem normalizedKernel_eq_normGauge
    (x u v : ℝ) (hu : 0 < 1+x*u) (hv : 0 < 1+x*v) :
    normalizedKernel x u v =
      kernelNormalization x * thetaNormGauge x u * thetaNormGauge x v *
        Psi1 (thetaTimeOfX x + thetaNormShift x u + thetaNormShift x v) := by
  have hg (z : ℝ) (hz : 0 < 1+x*z) :
      thetaNormGauge x z = Real.exp (z/x)/(1+x*z)^((5:ℝ)/4) := by
    unfold thetaNormGauge
    rw [Real.exp_sub, Real.rpow_def_of_pos hz]
    congr 1
    ring
  rw [hg u hu, hg v hv]
  unfold normalizedKernel kernelNormalization thetaTimeOfX thetaNormShift
  ring

noncomputable def thetaNormWeightedPsi (x : ℝ) (j m : ℕ) (t : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (j+1),
    thetaNormRow x j l * (kernelNormalization x * originalPsiJet (m+l) t)

theorem thetaNormWeightedPsi_hasDerivAt
    (x : ℝ) (j m : ℕ) (hm : m+j < 8) (t : ℝ) :
    HasDerivAt (thetaNormWeightedPsi x j m)
      (thetaNormWeightedPsi x j (m+1) t) t := by
  unfold thetaNormWeightedPsi
  have h : ∀ (S : Finset ℕ), S ⊆ Finset.range (j+1) →
      HasDerivAt
        (fun z : ℝ => ∑ l ∈ S, thetaNormRow x j l *
          (kernelNormalization x * originalPsiJet (m+l) z))
        (∑ l ∈ S, thetaNormRow x j l *
          (kernelNormalization x * originalPsiJet (m+1+l) t)) t := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simpa using hasDerivAt_const t (0:ℝ)
    | @insert l S hl ih =>
        intro hS
        have hlj : l ≤ j := by
          have hmem := hS (Finset.mem_insert_self l S)
          exact Nat.le_of_lt_succ (Finset.mem_range.mp hmem)
        have hs : S ⊆ Finset.range (j+1) := fun a ha =>
          hS (Finset.mem_insert_of_mem ha)
        have hl' := ((thetaNormPsiJet_hasDerivAt (m+l) (by omega) t).const_mul
          (kernelNormalization x)).const_mul (thetaNormRow x j l)
        have hadd := hl'.add (ih hs)
        convert hadd using 1
        · funext z
          simp only [Finset.sum_insert hl, Pi.add_apply]
        · rw [Finset.sum_insert hl]
          rw [show m+l+1 = m+1+l by omega]
  exact h _ (Finset.Subset.refl _)

/-- The right jet is an ordinary gauged left section of a finite linear
combination of the original Psi derivatives. -/
theorem normalizedKernel_right_normRows
    (x u : ℝ) (j : ℕ) (hj : j ≤ 4) (hu : 0 < 1+x*u) :
    iteratedDeriv j (fun v => normalizedKernel x u v) 0 =
      thetaNormGauge x u * thetaNormWeightedPsi x j 0
        (thetaTimeOfX x+thetaNormShift x u) := by
  let f : ℕ → ℝ → ℝ := fun m t =>
    (kernelNormalization x * thetaNormGauge x u) * originalPsiJet m t
  have hf : ∀ m < 8, ∀ t : ℝ, HasDerivAt (f m) (f (m+1) t) t := by
    intro m hm t
    exact (thetaNormPsiJet_hasDerivAt m hm t).const_mul _
  let S : Set ℝ := {z | 0 < 1+x*z}
  have hs : IsOpen S := isOpen_lt continuous_const (by fun_prop)
  have hz : (0:ℝ) ∈ S := by simp [S]
  have he : Set.EqOn (fun v => normalizedKernel x u v)
      (fun v => thetaNormGauge x v *
        f 0 (thetaTimeOfX x+thetaNormShift x u+thetaNormShift x v)) S := by
    intro v hv
    rw [normalizedKernel_eq_normGauge x u v hu hv]
    dsimp [f, originalPsiJet]
    ring
  rw [(he.iteratedDeriv_of_isOpen hs j) hz]
  rw [thetaNormJetSection_iterated f 8 hf x
    (thetaTimeOfX x+thetaNormShift x u) 0 0 j hj (by omega) (by simp)]
  rw [thetaNormJetSection_origin]
  unfold thetaNormWeightedPsi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  dsimp [f]
  ring

/-- Actual mixed derivative in terms of the two triangular rows. -/
theorem normalizedKernel_mixed_normRows
    (x : ℝ) (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) :
    iteratedDeriv i (fun u => iteratedDeriv j
      (fun v => normalizedKernel x u v) 0) 0 =
      ∑ a ∈ Finset.range (i+1), thetaNormRow x i a *
        (∑ b ∈ Finset.range (j+1), thetaNormRow x j b *
          (kernelNormalization x * originalPsiJet (a+b) (thetaTimeOfX x))) := by
  let S : Set ℝ := {z | 0 < 1+x*z}
  have hs : IsOpen S := isOpen_lt continuous_const (by fun_prop)
  have hz : (0:ℝ) ∈ S := by simp [S]
  have he : Set.EqOn
      (fun u => iteratedDeriv j (fun v => normalizedKernel x u v) 0)
      (fun u => thetaNormGauge x u * thetaNormWeightedPsi x j 0
        (thetaTimeOfX x+thetaNormShift x u)) S := by
    intro u hu
    exact normalizedKernel_right_normRows x u j hj hu
  rw [(he.iteratedDeriv_of_isOpen hs i) hz]
  have hf : ∀ m < 8-j, ∀ t : ℝ,
      HasDerivAt (thetaNormWeightedPsi x j m)
        (thetaNormWeightedPsi x j (m+1) t) t := by
    intro m hm t
    exact thetaNormWeightedPsi_hasDerivAt x j m (by omega) t
  rw [thetaNormJetSection_iterated (thetaNormWeightedPsi x j)
    (8-j) hf x (thetaTimeOfX x) 0 0 i hi (by omega) (by simp)]
  rw [thetaNormJetSection_origin]
  simp only [Nat.zero_add, thetaNormWeightedPsi]

noncomputable def thetaNormTriangular (r : ℕ) (x : ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun i a => thetaNormRow x i.val a.val / (Nat.factorial i.val:ℝ))

theorem thetaNormTriangular_lower (r : ℕ) (hr : r ≤ 5) (x : ℝ) :
    (thetaNormTriangular r x).IsLowerTriangular := by
  intro i a h
  change thetaNormRow x i.val a.val / (Nat.factorial i.val:ℝ) = 0
  rw [thetaNormRow_above x i.val a.val (by have := i.isLt; omega) (by exact h)]
  simp

theorem thetaNormTriangular_diag_pos (r : ℕ) (hr : r ≤ 5) (x : ℝ) (hx : 0 < x)
    (i : Fin r) : 0 < thetaNormTriangular r x i i := by
  change 0 < thetaNormRow x i.val i.val / (Nat.factorial i.val:ℝ)
  rw [thetaNormRow_diag x i.val (by have := i.isLt; omega)]
  exact div_pos (pow_pos (by positivity) _) (by positivity)

/-- Finite matrix assembly, with the factorial normalization on the two rows. -/
theorem analyticLeadingMatrix_eq_normalization_congruence
    (r : ℕ) (hr : r ≤ 5) (x : ℝ) :
    analyticLeadingMatrix r hr x =
      kernelNormalization x •
        (thetaNormTriangular r x *
          Matrix.of (fun (a b : Fin r) => originalPsiJet (a.val+b.val) (thetaTimeOfX x)) *
          (thetaNormTriangular r x).transpose) := by
  apply Matrix.ext
  intro i j
  change analyticCoeff x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = _
  unfold analyticCoeff
  rw [normalizedKernel_mixed_normRows x i.val j.val (by have := i.isLt; omega)
    (by have := j.isLt; omega)]
  interval_cases r <;> fin_cases i <;> fin_cases j <;>
    simp [thetaNormTriangular, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Finset.sum_range_succ, thetaNormRow, thetaNormJetPolynomial,
      Matrix.smul_apply, smul_eq_mul, Nat.factorial] <;> ring

end W5
