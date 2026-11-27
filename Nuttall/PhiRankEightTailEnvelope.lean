import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Nuttall

/-- The tail interval of the compact replay lies in the region X ≥ 16. -/
theorem sixteen_le_theta_tail_coordinate {t : ℝ} (ht : 1/2 ≤ t) :
    16 ≤ Real.pi * Real.exp (4*t) := by
  have he : (27:ℝ)/10 ≤ Real.exp 1 :=
    (by norm_num : (27:ℝ)/10 ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 27/10) he 2
  rw [← Real.exp_nat_mul] at hsq
  norm_num at hsq
  have htime : Real.exp 2 ≤ Real.exp (4*t) := Real.exp_le_exp.mpr (by linarith only [ht])
  calc
    _ ≤ 3*(729/100:ℝ) := by norm_num
    _ ≤ Real.pi*Real.exp 2 := mul_le_mul Real.pi_gt_three.le hsq (by norm_num) Real.pi_pos.le
    _ ≤ _ := mul_le_mul_of_nonneg_left htime Real.pi_pos.le

private theorem pow_exp_decay_from {X B d : ℝ} (m : ℕ) (hB : 0 < B)
    (hX : B ≤ X) (hd : (m:ℝ)/B ≤ d) :
    (X/B)^m * Real.exp (-d*X) ≤ Real.exp (-d*B) := by
  have hz : X/B ≤ Real.exp ((X-B)/B) := by
    have he := Real.add_one_le_exp ((X-B)/B)
    have heq : (X-B)/B+1 = X/B := by
      field_simp [hB.ne']
      ring
    rwa [heq] at he
  have hp := pow_le_pow_left₀ (div_nonneg (hB.le.trans hX) hB.le) hz m
  rw [← Real.exp_nat_mul] at hp
  calc
    _ ≤ Real.exp ((m:ℝ)*((X-B)/B)) * Real.exp (-d*X) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp ((m:ℝ)*((X-B)/B) + -d*X) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hX)
      linarith only [h, show (m:ℝ)*((X-B)/B) = (m:ℝ)/B*(X-B) by ring]

/-- A scalar majorant for the contribution of square index (k+2)² to the
perturbation of the normalized rank-eight tail matrix. -/
noncomputable def phiRankEightTailEnvelope (X : ℝ) (k : ℕ) : ℝ :=
  (1792*2^46) * (((k:ℝ)+2)/2)^32 *
    ((X/16)^8 * Real.exp (-((k:ℝ)^2+4*(k:ℝ)+3)*X))

private def rankEightDecayExponent (k : ℕ) : ℕ := 16*(k^2+4*k+3)

private noncomputable def rankEightDecayMajorant (k : ℕ) : ℝ :=
  (1792*2^46) * (((k:ℝ)+2)/2)^32 * (3/8:ℝ)^(rankEightDecayExponent k)

private theorem rankEightEnvelope_le_majorant {X : ℝ} (hX : 16 ≤ X) (k : ℕ) :
    phiRankEightTailEnvelope X k ≤ rankEightDecayMajorant k := by
  have he : Real.exp (-1) ≤ (3:ℝ)/8 := by
    rw [Real.exp_neg]
    exact inv_le_iff_one_le_mul₀ (Real.exp_pos _)
      |>.2 (by linarith only [Real.exp_one_gt_d9])
  have hm := pow_exp_decay_from (X := X) (B := 16) (d := (k:ℝ)^2+4*(k:ℝ)+3) 8
    (by norm_num) hX (by
      norm_num
      nlinarith only [sq_nonneg (k:ℝ), Nat.cast_nonneg (α := ℝ) k])
  have he' : Real.exp (-((k:ℝ)^2+4*(k:ℝ)+3)*16) ≤
      (3/8:ℝ)^(rankEightDecayExponent k) := by
    rw [show -((k:ℝ)^2+4*(k:ℝ)+3)*16 = (rankEightDecayExponent k:ℝ)*(-1) by
      unfold rankEightDecayExponent
      push_cast
      ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le he _
  exact mul_le_mul_of_nonneg_left (hm.trans he') (by positivity)

private theorem rankEightMajorant_step (k : ℕ) :
    rankEightDecayMajorant (k+1) ≤ rankEightDecayMajorant k/2 := by
  have hpow : (((k+1:ℕ):ℝ)+2)/2 ≤ (((k:ℝ)+2)/2) * (3/2) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (((k+1:ℕ):ℝ)+2)/2) hpow 32
  have he : rankEightDecayExponent (k+1) = rankEightDecayExponent k + 16*(2*k+5) := by
    unfold rankEightDecayExponent
    ring
  have hdecay : (3/8:ℝ)^(16*(2*k+5)) ≤ (3/8:ℝ)^80 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold rankEightDecayMajorant
  rw [he, pow_add]
  calc
    _ ≤ (1792*2^46) * ((((k:ℝ)+2)/2)*(3/2))^32 *
        ((3/8:ℝ)^(rankEightDecayExponent k)*(3/8:ℝ)^80) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (mul_le_mul_of_nonneg_left hdecay (by positivity)) (by positivity) (by positivity)
    _ = rankEightDecayMajorant k * ((3/2:ℝ)^32*(3/8:ℝ)^80) := by
      unfold rankEightDecayMajorant
      rw [mul_pow]
      ring
    _ ≤ _ := by
      unfold rankEightDecayMajorant
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        (mul_le_mul_of_nonneg_left (by norm_num : (3/2:ℝ)^32*(3/8:ℝ)^80 ≤ 1/2)
          (by positivity : 0 ≤ (1792*2^46)*(((k:ℝ)+2)/2)^32*(3/8:ℝ)^(rankEightDecayExponent k)))

theorem phiRankEightTailEnvelope_summable_le {X : ℝ} (hX : 16 ≤ X) :
    Summable (phiRankEightTailEnvelope X) ∧
      ∑' k, phiRankEightTailEnvelope X k < 1/1000 := by
  have hgeom (k : ℕ) : rankEightDecayMajorant k ≤ rankEightDecayMajorant 0 * (1/2:ℝ)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        _ ≤ rankEightDecayMajorant k/2 := rankEightMajorant_step k
        _ ≤ _ := by
          rw [pow_succ]
          exact (div_le_div_of_nonneg_right ih (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
  have hbase : ‖(1/2:ℝ)‖ < 1 := by norm_num [Real.norm_eq_abs]
  have hsum := (summable_geometric_of_norm_lt_one hbase).mul_left (rankEightDecayMajorant 0)
  have hcompare (k : ℕ) := (rankEightEnvelope_le_majorant hX k).trans (hgeom k)
  have hs := hsum.of_nonneg_of_le
    (fun k => show 0 ≤ phiRankEightTailEnvelope X k by unfold phiRankEightTailEnvelope; positivity)
    hcompare
  refine ⟨hs, (hs.tsum_le_tsum hcompare hsum).trans_lt ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hbase]
  norm_num [rankEightDecayMajorant, rankEightDecayExponent]

#print axioms phiRankEightTailEnvelope_summable_le
#print axioms sixteen_le_theta_tail_coordinate

end Nuttall
