import Nuttall.PhiCompactNormalization
import Nuttall.ReverseSignRegularity

namespace Nuttall

open Polynomial
open scoped BigOperators

/-- The parameter used for the compact and tail calculations of Φ. -/
noncomputable def phiThetaCoordinate (t : ℝ) : ℝ := Real.pi * Real.exp (4*t)

private noncomputable def phiCompactScale (t : ℝ) : ℝ :=
  Real.exp t * phiThetaCoordinate t * Real.exp (-phiThetaCoordinate t)

private theorem phiCompactScale_pos (t : ℝ) : 0 < phiCompactScale t := by
  unfold phiCompactScale phiThetaCoordinate
  positivity

private theorem auxiliaryWeightedSummand_compact (P : ℝ[X]) (n : ℕ) (t : ℝ) :
    auxiliaryWeightedSummand P n t =
      phiCompactScale t *
        ((n:ℝ)^2 * P.eval ((n:ℝ)^2 * phiThetaCoordinate t) *
          Real.exp (-((n:ℝ)^2-1)*phiThetaCoordinate t)) := by
  unfold auxiliaryWeightedSummand auxiliarySummand auxiliaryCoordinate
    phiCompactScale phiThetaCoordinate
  rw [show (5:ℝ)*t = t+4*t by ring, Real.exp_add]
  rw [show -(n:ℝ)^2 * Real.pi * Real.exp (4*t) =
    -(Real.pi * Real.exp (4*t)) + (-((n:ℝ)^2-1)*(Real.pi*Real.exp (4*t))) by ring]
  rw [Real.exp_add]
  ring_nf

noncomputable def phiCompactMatrix (p : ℕ) (X : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of (fun i j => ∑' n, phiCompactTerm X i.val j.val n)

private theorem phiCompactTerm_eq_sums {p : ℕ} (hp : p ≤ 4) (t : ℝ)
    (i j : Fin p) (n : ℕ) :
    phiCompactScale t * phiCompactTerm (phiThetaCoordinate t) i.val j.val n =
      ∑ a : Fin p, ∑ b : Fin p,
        phiCompactRows p (phiThetaCoordinate t) i a *
        phiCompactRows p (phiThetaCoordinate t) j b *
        auxiliaryWeightedSummand (phiJetPolynomial (a.val+b.val)) n t := by
  let X := phiThetaCoordinate t
  let q : ℝ := (n:ℝ)^2
  have hp' : Finset.range p ⊆ Finset.range 4 := Finset.range_mono hp
  have hi : i.val < 4 := i.isLt.trans_le hp
  have hj : j.val < 4 := j.isLt.trans_le hp
  change phiCompactScale t * phiCompactTerm X i.val j.val n = _
  rw [phiCompactTerm, phiCompactPolynomial_eq_rows X q _ _ hi hj]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [phiCompactRows, Matrix.of_apply, Fin.sum_univ_eq_sum_range]
  rw [← Finset.sum_subset hp' (fun a _ ha => by
    have hia : i.val < a := lt_of_lt_of_le i.isLt (Nat.le_of_not_gt (fun h => ha (Finset.mem_range.mpr h)))
    simp [phiCompactRow_zero hi hia])]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_subset hp' (fun b _ hb => by
    have hjb : j.val < b := lt_of_lt_of_le j.isLt (Nat.le_of_not_gt (fun h => hb (Finset.mem_range.mpr h)))
    simp [phiCompactRow_zero hj hjb])]
  apply Finset.sum_congr rfl
  intro b hb
  rw [auxiliaryWeightedSummand_compact]
  change _ = _
  ring

private theorem phiCompactTerm_summable_mul {p : ℕ} (hp : p ≤ 4) (t : ℝ)
    (i j : Fin p) : Summable (fun n => phiCompactScale t * phiCompactTerm (phiThetaCoordinate t)
      i.val j.val n) := by
  simp_rw [phiCompactTerm_eq_sums hp t i j]
  exact summable_sum (fun a _ => summable_sum (fun b _ =>
    (auxiliaryWeightedSummand_summable (phiJetPolynomial (a.val+b.val)) t).mul_left _))

theorem phiCompactTerm_summable (t : ℝ) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    Summable (phiCompactTerm (phiThetaCoordinate t) i j) := by
  have h := (phiCompactTerm_summable_mul (p := 4) le_rfl t ⟨i,hi⟩ ⟨j,hj⟩).mul_left
    (phiCompactScale t)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ (phiCompactScale_pos t).ne', one_mul] using h

private theorem phiCompactMatrix_eq_congruence {p : ℕ} (hp : p ≤ 4) (t : ℝ) :
    phiCompactScale t • phiCompactMatrix p (phiThetaCoordinate t) =
      phiCompactRows p (phiThetaCoordinate t) *
        Matrix.of (fun (i j : Fin p) => iteratedDeriv (i.val+j.val) W5.Phi t) *
        (phiCompactRows p (phiThetaCoordinate t)).transpose := by
  ext i j
  simp only [phiCompactMatrix, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← tsum_mul_left]
  simp_rw [phiCompactTerm_eq_sums hp t i j]
  rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ =>
    (auxiliaryWeightedSummand_summable (phiJetPolynomial (a.val+b.val)) t).mul_left _))]
  simp_rw [Summable.tsum_finsetSum (fun b _ =>
    (auxiliaryWeightedSummand_summable (phiJetPolynomial (_ + b.val)) t).mul_left _)]
  simp only [tsum_mul_left, ← iteratedDeriv_phi_eq_tsum, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The normalized matrix and the original Wronskian have the same strict signed sign. -/
theorem phiCompactMatrix_signed_det_pos_iff {p : ℕ} (hp : p ≤ 4) (t : ℝ) :
    0 < kernelMinorSign p * (phiCompactMatrix p (phiThetaCoordinate t)).det ↔
      0 < kernelMinorSign p * wronskian W5.Phi p t := by
  have h := congrArg Matrix.det (phiCompactMatrix_eq_congruence hp t)
  simp only [Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose, Fintype.card_fin,
    wronskian] at h ⊢
  let c := phiCompactScale t ^ p
  let d := (phiCompactRows p (phiThetaCoordinate t)).det
  have hc : 0 < c := pow_pos (phiCompactScale_pos t) p
  have hd : 0 < d^2 := sq_pos_of_pos (phiCompactRows_det_pos hp _)
  change c * (phiCompactMatrix p (phiThetaCoordinate t)).det =
    d * (wronskian W5.Phi p t) * d at h
  have he : c * (kernelMinorSign p * (phiCompactMatrix p (phiThetaCoordinate t)).det) =
      d^2 * (kernelMinorSign p * wronskian W5.Phi p t) := by
    calc
      _ = kernelMinorSign p * (c * (phiCompactMatrix p (phiThetaCoordinate t)).det) := by ring
      _ = _ := by rw [h]; ring
  change 0 < kernelMinorSign p * (phiCompactMatrix p (phiThetaCoordinate t)).det ↔
    0 < kernelMinorSign p * wronskian W5.Phi p t
  rw [← mul_pos_iff_of_pos_left hc, he, mul_pos_iff_of_pos_left hd]

#print axioms phiCompactTerm_summable
#print axioms phiCompactMatrix_signed_det_pos_iff

end Nuttall
