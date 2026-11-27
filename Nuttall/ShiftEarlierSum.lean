import Nuttall.ShiftEarlierTerms
import Nuttall.ShiftCriticalSplit
import Nuttall.ShiftWeightSum

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

theorem lastActiveTheta_lt_exp (u : ℝ) :
    (lastActiveTheta u : ℝ) < Real.exp (2*u) := by
  apply Nat.lt_ceil.1
  have h : 0 < ⌈Real.exp (2*u)⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast Real.exp_pos (2*u))
  unfold lastActiveTheta
  omega

theorem thetaKnot_two_pos : 0 < thetaKnot 2 := by
  unfold thetaKnot
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem thetaKnot_two_div_le {u B : ℝ} (hu : 0 < u) (huB : u ≤ B)
    {n : ℕ} (hn : 2 ≤ n) :
    thetaKnot 2 / B ≤ thetaKnot n / u := by
  have hlog : Real.log 2 ≤ Real.log (n:ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  calc
    _ ≤ thetaKnot 2 / u := div_le_div_of_nonneg_left thetaKnot_two_pos.le hu huB
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hu.le
      unfold thetaKnot
      exact div_le_div_of_nonneg_right hlog (by norm_num)

/-- Explicit uniform majorant for the earlier positive shifts in the critical block. -/
noncomputable def shiftEarlierError (M k : ℕ) (B : ℝ) : ℝ :=
  4*(2*Real.sqrt (2*B)*Real.exp B/((thetaKnot 2/B)^2*Real.sqrt M)) +
    2*Real.exp B*((k:ℝ)*Real.exp (-(thetaKnot 2/B)*Real.sqrt M/16))

private theorem sum_earlier_inv_sqrt_le {K : ℕ} {B : ℝ} (hK : (K:ℝ) ≤ Real.exp (2*B)) :
    (∑ n ∈ Finset.Ico 2 K, 1/Real.sqrt (n:ℝ)) ≤ 2*Real.exp B := by
  calc
    _ ≤ ∑ m ∈ Finset.range K, 1/Real.sqrt ((m:ℝ)+1) := by
      apply Finset.sum_le_sum_of_injOn (fun n : ℕ => n-1)
      · intro x hx y hy he
        change x-1 = y-1 at he
        have := (Finset.mem_Ico.mp hx).1
        have := (Finset.mem_Ico.mp hy).1
        omega
      · intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        exact Finset.mem_range.mpr (by have := (Finset.mem_Ico.mp hn).2; omega)
      · intro n hn
        have h : ((n-1:ℕ):ℝ)+1 = n := by
          rw [Nat.cast_sub (show 1 ≤ n by have := (Finset.mem_Ico.mp hn).1; omega),
            Nat.cast_one, sub_add_cancel]
        exact le_of_eq (by rw [h])
      · intro m _ _
        positivity
    _ ≤ 2*Real.sqrt K := sum_inv_sqrt_succ_le _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.sqrt_le_iff).2 ⟨Real.exp_nonneg _, ?_⟩
      rwa [← Real.exp_nat_mul, show (↑(2:ℕ):ℝ)*B = 2*B by norm_num]

theorem norm_earlier_shift_sum_le {M k : ℕ} (hM : 0 < M) (hk : 2*(k-1) ≤ M)
    {u B : ℝ} (hu : 0 < u) (huB : u ≤ B) :
    (∑ n ∈ Finset.Ico 2 (lastActiveTheta u),
      (Real.sqrt (n:ℝ))⁻¹ * ‖shiftCore M k (thetaKnot n/u)‖) ≤ shiftEarlierError M k B := by
  let K := lastActiveTheta u
  let D := thetaKnot 2/B
  let C := 2*Real.sqrt (2*B)*Real.exp B/(D^2*Real.sqrt M)
  let P := (k:ℝ)*Real.exp (-D*Real.sqrt M/16)
  have hB := hu.trans_le huB
  have hD : 0 < D := div_pos thetaKnot_two_pos hB
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hK : (K:ℝ) ≤ Real.exp (2*u) := (lastActiveTheta_lt_exp u).le
  have hb (n : ℕ) (hn : n ∈ Finset.Ico 2 K) :
      (Real.sqrt (n:ℝ))⁻¹ * ‖shiftCore M k (thetaKnot n/u)‖ ≤
        C*(1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) + P*(1/Real.sqrt (n:ℝ)) := by
    obtain ⟨hn₂, hnK⟩ := Finset.mem_Ico.mp hn
    let d := thetaKnot n/u
    have hd : D ≤ d := thetaKnot_two_div_le hu huB hn₂
    have hd₁ : d < 1 := (activeTheta_shiftFraction hu (by
      rw [activeThetaIndices_eq_Icc]
      exact Finset.mem_Icc.mpr ⟨by omega, hnK.le⟩)).2
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hgap' : (0:ℝ) < (K:ℝ)-n := sub_pos.2 (by exact_mod_cast hnK)
    have hgap := shiftKnot_gap_lower hu huB (show 0 < n by omega) hnK.le hK
    have hv : Real.sqrt ((K:ℝ)-n)/(Real.sqrt (2*B)*Real.exp B) ≤ Real.sqrt (1-d) := by
      have hh := Real.sqrt_le_sqrt hgap
      rw [Real.sqrt_div hgap'.le, Real.sqrt_mul (by positivity),
        show Real.exp (2*B) = (Real.exp B)^2 by rw [← Real.exp_nat_mul]; norm_num,
        Real.sqrt_sq (Real.exp_nonneg _)] at hh
      exact hh
    let q := Real.sqrt (2*B)*Real.exp B
    have hq : 0 < q := by dsimp [q]; positivity
    have hv' : Real.sqrt ((K:ℝ)-n) ≤ Real.sqrt (1-d)*q := (div_le_iff₀ hq).1 hv
    have hds := pow_le_pow_left₀ hD.le hd 2
    have hden : D^2*Real.sqrt M*Real.sqrt ((K:ℝ)-n) ≤
        d^2*Real.sqrt (1-d)*Real.sqrt M*q := by
      calc
        _ ≤ (d^2*Real.sqrt M)*(Real.sqrt (1-d)*q) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_right hds (Real.sqrt_nonneg _)) hv'
            (Real.sqrt_nonneg _) (by positivity)
        _ = _ := by ring
    have hdp : 0 < d := hD.trans_le hd
    have hdm : 0 < 1-d := sub_pos.2 hd₁
    have hcentral : 2/(d^2*Real.sqrt (1-d)*Real.sqrt M) ≤ C/Real.sqrt ((K:ℝ)-n) := by
      rw [show C = 2*q/(D^2*Real.sqrt M) by dsimp [C, q]; ring]
      rw [div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      linarith only [hden]
    have hout : (k:ℝ)*Real.exp (-d*Real.sqrt M/16) ≤ P := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.2
      nlinarith only [mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg (M:ℝ))]
    have hnrm := (norm_shiftCore_le_earlierTerms hM (hD.trans_le hd) hd₁ hk).trans
      (add_le_add hcentral hout)
    apply (mul_le_mul_of_nonneg_left hnrm (by positivity)).trans_eq
    rw [Real.sqrt_mul hn'.le]
    ring
  have hweights : (∑ n ∈ Finset.Ico 2 K, 1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) ≤ 4 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)).trans
      (sum_cross_inv_sqrt_le_four K)
    intro n hn
    obtain ⟨hn₂, hnK⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, hnK⟩
  have hcount := sum_earlier_inv_sqrt_le (hK.trans (Real.exp_le_exp.2 (by linarith : 2*u ≤ 2*B)))
  change (∑ n ∈ Finset.Ico 2 K, _) ≤ _
  calc
    _ ≤ (∑ n ∈ Finset.Ico 2 K, (C*(1/Real.sqrt ((n:ℝ)*((K:ℝ)-n))) + P*(1/Real.sqrt (n:ℝ)))) :=
      Finset.sum_le_sum hb
    _ ≤ C*4+P*(2*Real.exp B) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hweights hC) (mul_le_mul_of_nonneg_left hcount hP)
    _ = _ := by change C*4+P*(2*Real.exp B) = 4*C+2*Real.exp B*P; ring

/-- A finite bound on the norm distance, with no lower bound on the order
other than the dimension and the validity of the core estimate. -/
theorem norm_summedCorrectedShiftCore_sub_le_explicit {M k : ℕ}
    (hM : 0 < M) (hk : 2*(k-1) ≤ M) {r u B : ℝ} (hr : 0 < r)
    (hrM : r ≤ (M:ℝ)+1) (hu : 0 < u) (huB : u ≤ B) :
    let E := B*(1/r+Real.sqrt (Real.pi/r))
    ‖summedCorrectedShiftCore M k u-shiftSignMatrix k‖ ≤
      E+(1+E)*(1/Real.sqrt 2+shiftEarlierError M k B) := by
  have h := norm_summedCorrectedShiftCore_sub_le_split hk hr hrM hu huB
  have hB := hu.le.trans huB
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (norm_earlier_shift_sum_le hM hk hu huB))
      (by positivity)))

#print axioms norm_earlier_shift_sum_le
#print axioms norm_summedCorrectedShiftCore_sub_le_explicit

end Nuttall
