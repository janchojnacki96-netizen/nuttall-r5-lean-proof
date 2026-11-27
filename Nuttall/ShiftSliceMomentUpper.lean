import Nuttall.ShiftEarlierSum

namespace Nuttall

open scoped BigOperators

theorem activeTheta_invSqrt_sum_le (u : ℝ) :
    (∑ n ∈ activeThetaIndices u, 1/Real.sqrt (n:ℝ)) ≤ 2*Real.exp u := by
  let K := lastActiveTheta u
  rw [activeThetaIndices_eq_Icc]
  change (∑ n ∈ Finset.Icc 1 K, _) ≤ _
  rw [show Finset.Icc 1 K = Finset.Ico 1 (K+1) by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range]
  have hsum := sum_inv_sqrt_succ_le K
  have hK := Real.sqrt_le_sqrt (lastActiveTheta_lt_exp u).le
  have hE : Real.sqrt (Real.exp (2*u)) = Real.exp u := by
    rw [show 2*u = u+u by ring, Real.exp_add, ← pow_two, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos u)]
  rw [hE] at hK
  simpa [K, Nat.add_comm] using hsum.trans (mul_le_mul_of_nonneg_left hK (by norm_num : (0:ℝ) ≤ 2))

private theorem abs_tailMomentWeight_le_factored {s m : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    {x u : ℝ} (hx : 0 ≤ x) (hxu : x ≤ u) :
    |tailMomentWeight (s-1) x| ≤ ((m:ℝ)+u)*(1+u)^m / (s.factorial:ℝ) := by
  have hs' : s-1+1 = s := by omega
  have hfac : s.factorial = s*(s-1).factorial := by
    calc
      _ = (s-1+1).factorial := congrArg Nat.factorial hs'.symm
      _ = _ := by rw [Nat.factorial_succ, hs']
  have he : tailMomentWeight (s-1) x = x^(s-1)*((s:ℝ)-x)/(s.factorial:ℝ) := by
    unfold tailMomentWeight
    rw [hs', show x^s = x^(s-1)*x by rw [← pow_succ, hs']]
    rw [hfac, Nat.cast_mul]
    have hsn : (s:ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
    have hn : ((s-1).factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    field_simp
  have hu := hx.trans hxu
  have hp : x^(s-1) ≤ (1+u)^m :=
    (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have ha : |(s:ℝ)-x| ≤ (m:ℝ)+u := by
    apply (abs_le.2 ⟨?_,?_⟩) <;> have h : (s:ℝ) ≤ m := by exact_mod_cast hsm
    · linarith
    · linarith
  rw [he, abs_div, abs_mul, abs_of_nonneg (pow_nonneg hx _),
    abs_of_nonneg (show (0:ℝ) ≤ s.factorial by positivity)]
  exact div_le_div_of_nonneg_right
    (by simpa only [mul_comm] using mul_le_mul hp ha (abs_nonneg _) (by positivity))
    (Nat.cast_nonneg _)

/-- On the whole positive half-line a normalized moment contributes at most
the common polynomial envelope times the sum of active theta weights. -/
theorem abs_shiftedMoment_le_polynomial_envelope {s m : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    {u : ℝ} (hu : 0 ≤ u) :
    |shiftedMoment (s-1) u| ≤
      (2*Real.exp u)*(((m:ℝ)+u)*(1+u)^m/(s.factorial:ℝ)) := by
  let C := ((m:ℝ)+u)*(1+u)^m/(s.factorial:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  rw [shiftedMoment_eq_sum_active]
  calc
    _ ≤ ∑ n ∈ activeThetaIndices u,
        |tailMomentWeight (s-1) (u-thetaKnot n)/Real.sqrt (n:ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ activeThetaIndices u, (1/Real.sqrt (n:ℝ))*C := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn₀, hn₁⟩ := mem_activeThetaIndices.1 hn
      have ha : 0 ≤ thetaKnot n := by
        unfold thetaKnot
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn₀)) (by norm_num)
      rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), one_div, mul_comm, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right
        (abs_tailMomentWeight_le_factored hs hsm (by linarith) (by linarith)) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (activeTheta_invSqrt_sum_le u) hC

theorem abs_shiftedMoment_linearCombination_le_envelope {p L m : ℕ} (hL : 1 ≤ L)
    (hLm : L+p ≤ m+1) (c : Fin p → ℝ) {F u : ℝ} (hu : 0 ≤ u)
    (hF : ∀ j, |c j / ((L+j.val).factorial:ℝ)| ≤ F) :
    |∑ j : Fin p, c j*shiftedMoment (L+j.val-1) u| ≤
      (2*Real.exp u)*(p:ℝ)*F*((m:ℝ)+u)*(1+u)^m := by
  have hterm (j : Fin p) :
      |c j*shiftedMoment (L+j.val-1) u| ≤
        (2*Real.exp u)*F*((m:ℝ)+u)*(1+u)^m := by
    have hj := j.isLt
    rw [abs_mul]
    refine (mul_le_mul_of_nonneg_left
      (abs_shiftedMoment_le_polynomial_envelope (s := L+j.val) (m := m)
        (by omega) (by omega) hu) (abs_nonneg _)).trans ?_
    have h := hF j
    rw [abs_div, abs_of_nonneg (show (0:ℝ) ≤ (L+j.val).factorial by positivity)] at h
    calc
      _ = (2*Real.exp u)*(|c j|/((L+j.val).factorial:ℝ))*((m:ℝ)+u)*(1+u)^m := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ j : Fin p, |c j*shiftedMoment (L+j.val-1) u| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin p, (2*Real.exp u)*F*((m:ℝ)+u)*(1+u)^m :=
      Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

#print axioms abs_shiftedMoment_linearCombination_le_envelope

end Nuttall
