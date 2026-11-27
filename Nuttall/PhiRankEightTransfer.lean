import Nuttall.PhiCompactTransfer
import Nuttall.PhiRankEightPolynomial
import Nuttall.PhiRankEightNormalizedSign
import Nuttall.PhiRankEightTermScaling
import W5.DeterminantCongruence

namespace Nuttall

open Polynomial
open scoped BigOperators

private noncomputable def phiRankEightScale (t : ℝ) : ℝ :=
  Real.exp t * phiThetaCoordinate t * Real.exp (-phiThetaCoordinate t)

private theorem phiRankEightScale_pos (t : ℝ) : 0 < phiRankEightScale t := by
  unfold phiRankEightScale phiThetaCoordinate
  positivity

private theorem auxiliaryWeightedSummand_rankEight (P : ℝ[X]) (n : ℕ) (t : ℝ) :
    auxiliaryWeightedSummand P n t =
      phiRankEightScale t *
        ((n:ℝ)^2 * P.eval ((n:ℝ)^2 * phiThetaCoordinate t) *
          Real.exp (-((n:ℝ)^2-1)*phiThetaCoordinate t)) := by
  unfold auxiliaryWeightedSummand auxiliarySummand auxiliaryCoordinate
    phiRankEightScale phiThetaCoordinate
  rw [show (5:ℝ)*t = t+4*t by ring, Real.exp_add]
  rw [show -(n:ℝ)^2 * Real.pi * Real.exp (4*t) =
    -(Real.pi * Real.exp (4*t)) + (-((n:ℝ)^2-1)*(Real.pi*Real.exp (4*t))) by ring]
  rw [Real.exp_add]
  ring_nf

private theorem phiRankEightCompactTerm_eq_sums {p : ℕ} (hp : p ≤ 8) (t : ℝ)
    (i j : Fin p) (n : ℕ) :
    phiRankEightScale t * phiCompactTerm (phiThetaCoordinate t) i.val j.val n =
      ∑ a : Fin p, ∑ b : Fin p,
        phiRankEightRows p (phiThetaCoordinate t) i a *
        phiRankEightRows p (phiThetaCoordinate t) j b *
        auxiliaryWeightedSummand (phiJetPolynomial (a.val+b.val)) n t := by
  let X := phiThetaCoordinate t
  let q : ℝ := (n:ℝ)^2
  have hp' : Finset.range p ⊆ Finset.range 8 := Finset.range_mono hp
  have hi : i.val < 8 := i.isLt.trans_le hp
  have hj : j.val < 8 := j.isLt.trans_le hp
  change phiRankEightScale t * phiCompactTerm X i.val j.val n = _
  rw [phiCompactTerm, phiRankEightPolynomial_eq_rows X q _ _ hi hj]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [phiRankEightRows, Matrix.of_apply]
  let f (a b : ℕ) := phiRankEightRow X i.val a * phiRankEightRow X j.val b *
    auxiliaryWeightedSummand (phiJetPolynomial (a+b)) n t
  have hr : (∑ a : Fin p, ∑ b : Fin p, f a.val b.val) =
      ∑ a ∈ Finset.range p, ∑ b ∈ Finset.range p, f a b := by
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => ∑ b : Fin p, f a b.val)]
    exact Finset.sum_congr rfl (fun a _ => Fin.sum_univ_eq_sum_range (f a) p)
  change _ = (∑ a : Fin p, ∑ b : Fin p, f a.val b.val)
  rw [hr]
  rw [← Finset.sum_subset hp' (fun a _ ha => by
    have hia : i.val < a := lt_of_lt_of_le i.isLt (Nat.le_of_not_gt (fun h => ha (Finset.mem_range.mpr h)))
    simp [phiRankEightRow_zero hi hia])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_subset hp' (fun b _ hb => by
    have hjb : j.val < b := lt_of_lt_of_le j.isLt (Nat.le_of_not_gt (fun h => hb (Finset.mem_range.mpr h)))
    simp [phiRankEightRow_zero hj hjb])]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [f, auxiliaryWeightedSummand_rankEight, X, q]
  ring

set_option maxHeartbeats 2000000 in
private theorem phiRankEightCompactMatrix_eq_congruence {p : ℕ} (hp : p ≤ 8) (t : ℝ) :
    phiRankEightScale t • phiCompactMatrix p (phiThetaCoordinate t) =
      phiRankEightRows p (phiThetaCoordinate t) *
        Matrix.of (fun (i j : Fin p) => iteratedDeriv (i.val+j.val) W5.Phi t) *
        (phiRankEightRows p (phiThetaCoordinate t)).transpose := by
  ext i j
  simp only [phiCompactMatrix, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← tsum_mul_left]
  simp_rw [phiRankEightCompactTerm_eq_sums hp t i j]
  rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ =>
    (auxiliaryWeightedSummand_summable (phiJetPolynomial (a.val+b.val)) t).mul_left _))]
  have hinner (a : Fin p) :
      (∑' n, ∑ b : Fin p, phiRankEightRows p (phiThetaCoordinate t) i a *
        phiRankEightRows p (phiThetaCoordinate t) j b *
        auxiliaryWeightedSummand (phiJetPolynomial (a.val+b.val)) n t) =
      ∑ b : Fin p, phiRankEightRows p (phiThetaCoordinate t) i a *
        phiRankEightRows p (phiThetaCoordinate t) j b *
        iteratedDeriv (a.val+b.val) W5.Phi t := by
    rw [Summable.tsum_finsetSum (fun (b : Fin p) _ =>
      (auxiliaryWeightedSummand_summable (phiJetPolynomial (a.val+b.val)) t).mul_left _)]
    simp only [tsum_mul_left, ← iteratedDeriv_phi_eq_tsum]
  simp_rw [hinner]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private noncomputable def rankEightBasisDiagonal (p : ℕ) (X : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.diagonal fun i => phiRankEightBasisScale X i.val

private noncomputable def rankEightTailSum (p : ℕ) (X : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  phiRankEightTerm p X 1 + ∑' k : ℕ, phiRankEightTerm p X (((k:ℝ)+2)^2)

private theorem rankEightTailSum_eq_scaled {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    (t : ℝ) (hX : 16 ≤ phiThetaCoordinate t) :
    rankEightTailSum p (phiThetaCoordinate t) =
      rankEightBasisDiagonal p (phiThetaCoordinate t) * phiCompactMatrix p (phiThetaCoordinate t) *
        rankEightBasisDiagonal p (phiThetaCoordinate t) := by
  let X := phiThetaCoordinate t
  have hX₀ : 0 < X := by dsimp [X]; linarith only [hX]
  have hT := (phiRankEightTailMatrix_summable_norm_lt hp₀ hp hX).1
  ext i j
  let c := phiRankEightBasisScale X i.val * phiRankEightBasisScale X j.val
  have h (n : ℕ) :
      phiRankEightTerm p X ((n:ℝ)^2) i j = c * phiCompactTerm X i.val j.val n := by
    simpa only [c, phiCompactTerm, mul_assoc] using
      phiRankEightTerm_eq_scaled_compact p hX₀ ((n:ℝ)^2) i j
  have hz : phiCompactTerm X i.val j.val 0 = 0 := by simp [phiCompactTerm, phiCompactPolynomial]
  have hh : Summable (fun n => phiRankEightScale t * phiCompactTerm X i.val j.val n) := by
    simp_rw [X, phiRankEightCompactTerm_eq_sums hp t i j]
    exact summable_sum (fun a _ => summable_sum (fun b _ =>
      (auxiliaryWeightedSummand_summable (phiJetPolynomial (a.val+b.val)) t).mul_left _))
  have hc : Summable (phiCompactTerm X i.val j.val) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ (phiRankEightScale_pos t).ne', one_mul] using
      hh.mul_left (phiRankEightScale t)⁻¹
  simp only [rankEightTailSum, rankEightBasisDiagonal, phiCompactMatrix, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  have hs : HasSum (fun k : ℕ => phiRankEightTerm p X (((k:ℝ)+2)^2) i j)
      ((∑' k : ℕ, phiRankEightTerm p X (((k:ℝ)+2)^2)) i j) :=
    hT.hasSum.map (Matrix.entryAddMonoidHom ℝ i j) (continuous_id.matrix_elem i j)
  rw [← hs.tsum_eq]
  change phiRankEightTerm p X 1 i j + (∑' k : ℕ, phiRankEightTerm p X (((k:ℝ)+2)^2) i j) =
    phiRankEightBasisScale X i.val * (∑' n, phiCompactTerm X i.val j.val n) * phiRankEightBasisScale X j.val
  have htail (k : ℕ) : phiRankEightTerm p X (((k:ℝ)+2)^2) i j =
      c * phiCompactTerm X i.val j.val (k+2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h (k+2)
  have h1 : phiRankEightTerm p X 1 i j = c * phiCompactTerm X i.val j.val 1 := by
    simpa only [Nat.cast_one, one_pow] using h 1
  simp_rw [htail]
  rw [h1, tsum_mul_left, ← hc.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hz]
  dsimp [c]
  ring

private theorem rankEightSign_det (p : ℕ) : (phiRankEightSign p).det = kernelMinorSign p := by
  simp only [phiRankEightSign, Matrix.det_diagonal, kernelMinorSign, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]

/-- For X ≥ 16 the original theta kernel has strictly signed Wronskians
through order eight. -/
theorem phiRankEightFarWronskian_pos {p : ℕ} (hp : p ≤ 8) (t : ℝ)
    (hX : 16 ≤ phiThetaCoordinate t) :
    0 < kernelMinorSign p * wronskian W5.Phi p t := by
  by_cases hp₀ : 0 < p
  · let X := phiThetaCoordinate t
    let D := rankEightBasisDiagonal p X
    let U := D * phiRankEightRows p X
    let H : Matrix (Fin p) (Fin p) ℝ :=
      Matrix.of fun i j => iteratedDeriv (i.val+j.val) W5.Phi t
    have hD : 0 < D.det := by
      simp only [D, rankEightBasisDiagonal, Matrix.det_diagonal]
      exact Finset.prod_pos fun i _ => phiRankEightBasisScale_pos (by linarith only [hX]) _
    have hU : 0 < U.det := by
      rw [show U = D * phiRankEightRows p X from rfl, Matrix.det_mul]
      exact mul_pos hD (phiRankEightRows_det_pos hp X)
    have hDt : D.transpose = D := Matrix.transpose_diagonal _
    have he : phiRankEightScale t • rankEightTailSum p X = U * H * U.transpose := by
      calc
        _ = D * (phiRankEightScale t • phiCompactMatrix p X) * D := by
          change phiRankEightScale t • rankEightTailSum p (phiThetaCoordinate t) = _
          rw [rankEightTailSum_eq_scaled hp₀ hp t hX]
          simp only [Matrix.mul_smul, Matrix.smul_mul, D]
        _ = _ := by
          change D * (phiRankEightScale t • phiCompactMatrix p (phiThetaCoordinate t)) * D = _
          rw [phiRankEightCompactMatrix_eq_congruence hp t]
          simp only [U, H, X, Matrix.transpose_mul, hDt, mul_assoc]
    have hdet := congrArg Matrix.det he
    rw [Matrix.det_smul, Fintype.card_fin, W5.det_of_congruence] at hdet
    have hsign := phiRankEightNormalized_det_pos hp₀ hp hX
    change 0 < (rankEightTailSum p X * phiRankEightSign p).det at hsign
    rw [Matrix.det_mul, rankEightSign_det] at hsign
    have hpositive := mul_pos (pow_pos (phiRankEightScale_pos t) p) hsign
    rw [← mul_assoc, hdet, mul_assoc] at hpositive
    simpa only [H, wronskian, mul_comm] using
      (mul_pos_iff_of_pos_left (sq_pos_of_pos hU)).mp hpositive
  · have he : p = 0 := by omega
    subst p
    simp [kernelMinorSign, wronskian]

#print axioms phiRankEightFarWronskian_pos

end Nuttall
