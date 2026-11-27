import Nuttall.ShiftCorrectionError

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

/-- The last active index uses the strict cutoff, including at a knot. -/
noncomputable def lastActiveTheta (u : ℝ) : ℕ :=
  ⌈Real.exp (2*u)⌉₊-1

theorem activeThetaIndices_eq_Icc (u : ℝ) :
    activeThetaIndices u = Finset.Icc 1 (lastActiveTheta u) := by
  ext n
  rw [mem_activeThetaIndices, Finset.mem_Icc]
  constructor
  · rintro ⟨hn, hkn⟩
    have hl := Nat.lt_ceil.2 ((thetaKnot_lt_iff n hn u).1 hkn)
    exact ⟨hn, by unfold lastActiveTheta; omega⟩
  · rintro ⟨hn, hnK⟩
    have hpos : 0 < ⌈Real.exp (2*u)⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast Real.exp_pos (2*u))
    have hn' : n < ⌈Real.exp (2*u)⌉₊ := by unfold lastActiveTheta at hnK; omega
    exact ⟨hn, (thetaKnot_lt_iff n hn u).2 (Nat.lt_ceil.1 hn')⟩

theorem lastActiveTheta_pos {u : ℝ} (hu : 0 < u) : 0 < lastActiveTheta u := by
  have h : 1 < ⌈Real.exp (2*u)⌉₊ :=
    Nat.lt_ceil.2 (by exact_mod_cast Real.one_lt_exp_iff.mpr (show 0 < 2*u by positivity))
  unfold lastActiveTheta
  omega

theorem activeTheta_shiftFraction {u : ℝ} (hu : 0 < u) {n : ℕ}
    (hn : n ∈ activeThetaIndices u) : 0 ≤ thetaKnot n/u ∧ thetaKnot n/u < 1 := by
  obtain ⟨hn₀, hn'⟩ := mem_activeThetaIndices.mp hn
  exact ⟨div_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hn₀)) (by norm_num)) hu.le,
    (div_lt_one hu).2 hn'⟩

/-- Isolate the zero shift and the last active shift. Only the earlier
positive shifts need the sharper asymptotic bound. -/
theorem norm_summedCorrectedShiftCore_sub_le_split {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {r B u : ℝ} (hr : 0 < r) (hrM : r ≤ (M:ℝ)+1) (hu : 0 < u) (huB : u ≤ B) :
    let E := B*(1/r+Real.sqrt (Real.pi/r))
    ‖summedCorrectedShiftCore M k u - shiftSignMatrix k‖ ≤
      E+(1+E)*(1/Real.sqrt 2+∑ n ∈ Finset.Ico 2 (lastActiveTheta u),
        (Real.sqrt (n:ℝ))⁻¹ * ‖shiftCore M k (thetaKnot n/u)‖) := by
  classical
  let E := B*(1/r+Real.sqrt (Real.pi/r))
  let K := lastActiveTheta u
  let J := shiftSignMatrix k
  let A (n : ℕ) := (Real.sqrt (n:ℝ))⁻¹ • correctedShiftCore M k u (thetaKnot n/u)
  let W (n : ℕ) := (Real.sqrt (n:ℝ))⁻¹ * ‖shiftCore M k (thetaKnot n/u)‖
  have hB := hu.le.trans huB
  have hE : 0 ≤ E := by unfold E; positivity
  have h1E : 0 ≤ 1+E := by positivity
  have hK : 1 ≤ K := lastActiveTheta_pos hu
  have hzero : ‖A 1-J‖ ≤ E := by
    have hC : shiftCore M k 0 = J := shiftCore_zero _ _ (by omega)
    have hA : A 1 = correctedShiftCore M k u 0 := by simp [A, thetaKnot]
    rw [hA, ← hC]
    exact (norm_correctedShiftCore_sub_le_uniform hk hr hrM hu.le huB
      (d := 0) le_rfl zero_le_one).trans
        (mul_le_of_le_one_right hE (norm_shiftCore_le_one (d := 0) le_rfl zero_le_one hk))
  have hterm (n : ℕ) (hn : n ∈ activeThetaIndices u) :
      ‖A n‖ ≤ (1+E)*W n := by
    have hd := activeTheta_shiftFraction hu hn
    have hw : 0 ≤ (Real.sqrt (n:ℝ))⁻¹ := by positivity
    have h := norm_correctedShiftCore_le_uniform hk hr hrM hu.le huB hd.1 hd.2.le
    simp only [A, norm_smul, Real.norm_of_nonneg hw, W]
    exact (mul_le_mul_of_nonneg_left h hw).trans_eq (by ring)
  change ‖summedCorrectedShiftCore M k u-J‖ ≤ E+(1+E)*(1/Real.sqrt 2+∑ n ∈ Finset.Ico 2 K, W n)
  change ‖(∑ n ∈ activeThetaIndices u, A n)-J‖ ≤ _
  rw [activeThetaIndices_eq_Icc]
  change ‖(∑ n ∈ Finset.Icc 1 K, A n)-J‖ ≤ _
  by_cases hK₂ : 2 ≤ K
  · have hset : Finset.Icc 1 K = insert 1 (insert K (Finset.Ico 2 K)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
    rw [show A 1+(A K+∑ n ∈ Finset.Ico 2 K, A n)-J =
      (A 1-J)+(A K+∑ n ∈ Finset.Ico 2 K, A n) by abel]
    have hnK : K ∈ activeThetaIndices u := by
      rw [activeThetaIndices_eq_Icc]
      exact Finset.mem_Icc.mpr ⟨hK, le_rfl⟩
    have hlast : W K ≤ 1/Real.sqrt 2 := by
      have hd := activeTheta_shiftFraction hu hnK
      have hroot : Real.sqrt 2 ≤ Real.sqrt (K:ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hK₂)
      calc
        _ ≤ (Real.sqrt (K:ℝ))⁻¹ := mul_le_of_le_one_right (by positivity)
          (norm_shiftCore_le_one hd.1 hd.2.le hk)
        _ ≤ _ := by rw [← one_div]; exact one_div_le_one_div_of_le (by positivity) hroot
    have hsum : ‖∑ n ∈ Finset.Ico 2 K, A n‖ ≤ (1+E)*∑ n ∈ Finset.Ico 2 K, W n := by
      rw [Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      have ⟨h₂, hlt⟩ := Finset.mem_Ico.mp hn
      apply hterm
      rw [activeThetaIndices_eq_Icc]
      exact Finset.mem_Icc.mpr ⟨by omega, hlt.le⟩
    have hl : ‖A K‖ ≤ (1+E)*(1/Real.sqrt 2) :=
      (hterm K hnK).trans (mul_le_mul_of_nonneg_left hlast h1E)
    calc
      _ ≤ ‖A 1-J‖+(‖A K‖+‖∑ n ∈ Finset.Ico 2 K, A n‖) :=
        (norm_add_le _ _).trans (add_le_add (le_refl _) (norm_add_le _ _))
      _ ≤ E+((1+E)*(1/Real.sqrt 2)+(1+E)*∑ n ∈ Finset.Ico 2 K, W n) :=
        add_le_add hzero (add_le_add hl hsum)
      _ = _ := by rw [mul_add]
  · have heq : K = 1 := by omega
    rw [heq, Finset.Icc_self, Finset.sum_singleton]
    exact hzero.trans (le_add_of_nonneg_right (mul_nonneg h1E (by
      apply add_nonneg (by positivity)
      exact Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (norm_nonneg _)))))

#print axioms activeThetaIndices_eq_Icc
#print axioms norm_summedCorrectedShiftCore_sub_le_split

end Nuttall
