import Nuttall.PhiComplexJets

namespace Nuttall

open scoped BigOperators

private theorem exp_neg_base_le : Real.exp (-(26:ℝ)/25) ≤ (9:ℝ)/25 := by
  have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 26/25 by norm_num) 6
  have hl : (25:ℝ)/9 ≤ Real.exp (26/25) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  rw [neg_div, Real.exp_neg]
  have hi := inv_anti₀ (by norm_num : (0:ℝ) < 25/9) hl
  norm_num at hi ⊢
  exact hi

private theorem gaussian_base_bound (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    Real.exp (-((n:ℝ)^2 * Real.pi * Real.exp (4*c))/3) ≤ (9/25:ℝ)^(n^2) := by
  have hπ : (78:ℝ)/25 ≤ Real.pi := Real.pi_gt_d6.le.trans' (by norm_num)
  have he : (1:ℝ) ≤ Real.exp (4*c) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hprod : (78:ℝ)/25 ≤ Real.pi * Real.exp (4*c) :=
    hπ.trans (le_mul_of_one_le_right Real.pi_pos.le he)
  have h := mul_le_mul_of_nonneg_left hprod (sq_nonneg (n:ℝ))
  calc
    _ ≤ Real.exp ((↑(n^2):ℝ) * (-(26:ℝ)/25)) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith only [h]
    _ = Real.exp (-(26:ℝ)/25)^(n^2) := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_base_le _

/-- A single geometric bound covers every omitted derivative tail on the
whole center range used by the compact certificates. -/
theorem phiJet_geometric_tail (j N : ℕ) (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) (hc₂ : c ≤ 2) :
    ‖∑' k, auxiliaryWeightedSummand (phiJetPolynomial j) (k+N) c‖ ≤
      ((j.factorial:ℝ) * 8^j) * (20000 * (9/25:ℝ)^(N^2) / (1-9/25)) := by
  let q : ℝ := 9/25
  let A : ℝ := (j.factorial:ℝ) * 8^j * 20000
  have hterm (k : ℕ) :
      ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+N) c‖ ≤ A * q^(N^2+k) := by
    have hpow : N^2+k ≤ (k+N)^2 := by
      have hlin : k ≤ k*N := by simpa using Nat.mul_le_mul_left k hN
      nlinarith only [hlin, Nat.zero_le (k*k), Nat.zero_le (N*k)]
    have hq : q^((k+N)^2) ≤ q^(N^2+k) :=
      pow_le_pow_of_le_one (by norm_num [q]) (by norm_num [q]) hpow
    have hG := (gaussian_base_bound (k+N) hc).trans hq
    calc
      _ ≤ (j.factorial:ℝ) *
          (20000 * Real.exp (-(((k+N:ℕ):ℝ)^2 * Real.pi * Real.exp (4*c))/3)) /
          (1/8:ℝ)^j := phiJetSummand_norm_le (k+N) j hc₂
      _ ≤ (j.factorial:ℝ) * (20000 * q^(N^2+k)) / (1/8:ℝ)^j := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG (by norm_num)) (by positivity))
          (by positivity)
      _ = _ := by
        rw [div_eq_mul_inv, ← inv_pow]
        norm_num [A]
        ring
  have hq : ‖q‖ < 1 := by norm_num [q, Real.norm_eq_abs]
  have hg := summable_geometric_of_norm_lt_one hq
  have hM : Summable fun k : ℕ => A * q^(N^2+k) := by
    convert hg.mul_left (A*q^(N^2)) using 1
    funext k
    rw [pow_add]
    ring
  have hS : Summable (fun k : ℕ =>
      ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+N) c‖) :=
    hM.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc
    _ ≤ ∑' k : ℕ, ‖auxiliaryWeightedSummand (phiJetPolynomial j) (k+N) c‖ :=
      norm_tsum_le_tsum_norm hS
    _ ≤ ∑' k : ℕ, A * q^(N^2+k) := hS.tsum_le_tsum hterm hM
    _ = _ := by
      simp only [pow_add, ← mul_assoc, tsum_mul_left]
      rw [tsum_geometric_of_norm_lt_one hq]
      dsimp [q, A]
      ring

set_option exponentiation.threshold 1000 in
/-- The finite truncation at the preprint's 24 positive indices has the
claimed error for each derivative, uniformly on [0,2]. -/
theorem phiJet_from_twenty_five_norm_le (j : ℕ) {c : ℝ} (hc : 0 ≤ c) (hc₂ : c ≤ 2) :
    ‖∑' k, auxiliaryWeightedSummand (phiJetPolynomial j) (k+25) c‖ ≤
      ((j.factorial:ℝ) * 8^j) * (1/2:ℝ)^900 := by
  refine (phiJet_geometric_tail j 25 (by decide) hc hc₂).trans ?_
  exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)

/-- A Cauchy bound for the full real kernel, at every order used for the
integrated Taylor panels and the matrix entries. -/
theorem iteratedDeriv_phi_compact_norm_le (j : ℕ) {c : ℝ} (hc : 0 ≤ c) (hc₂ : c ≤ 2) :
    ‖iteratedDeriv j W5.Phi c‖ ≤ ((j.factorial:ℝ) * 8^j) * 10^6 := by
  rw [iteratedDeriv_phi_eq_tsum,
    ← (auxiliaryWeightedSummand_summable (phiJetPolynomial j) c).sum_add_tsum_nat_add 1]
  have hn : auxiliaryWeightedSummand (phiJetPolynomial j) 0 c = 0 := by
    simp [auxiliaryWeightedSummand, auxiliarySummand]
  rw [Finset.sum_range_one, hn, zero_add]
  refine (phiJet_geometric_tail j 1 (by decide) hc hc₂).trans ?_
  exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)

#print axioms phiJet_from_twenty_five_norm_le
#print axioms iteratedDeriv_phi_compact_norm_le

end Nuttall
