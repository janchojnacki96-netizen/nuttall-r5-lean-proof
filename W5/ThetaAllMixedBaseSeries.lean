import W5.ThetaAllMixedJetInterchange
import W5.ThetaAllMixedJetCoefficientBridge

namespace W5
open MeasureTheory Filter
open scoped Topology

noncomputable def thetaBaseMixedTerm
    (i j : ℕ) (x u v : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^2 * thetaAllMixedJetTerm x u v n 0 i j

noncomputable def thetaBaseMixedMajorant
    (i j : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ((n:ℝ)^2+1) * thetaAllMixedJetIndexFactor i j x n

theorem thetaBaseMixedMajorant_summable
    (i j : ℕ) (x : ℝ) : Summable (thetaBaseMixedMajorant i j x) := by
  have h := (thetaHigherJetIndexFactor_extra_square_summable (i+j) x).mul_left
    (((j:ℝ)+1)^i)
  convert h using 1
  funext n
  unfold thetaBaseMixedMajorant thetaAllMixedJetIndexFactor
  ring

theorem thetaBaseMixedTerm_norm_le
    (i j : ℕ) (x u v : ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    ‖thetaBaseMixedTerm i j x u v n‖ ≤ thetaBaseMixedMajorant i j x n := by
  have h := thetaAllMixedJetTerm_norm_le_separable i j x u v n 0 hx hx1 hu hv le_rfl
  have ht : thetaHigherJetTailFactor (i+j) 0 = 1 := by
    simp [thetaHigherJetTailFactor]
  rw [ht, mul_one] at h
  have hI : 0 ≤ thetaAllMixedJetIndexFactor i j x n := by
    unfold thetaAllMixedJetIndexFactor thetaHigherJetIndexFactor
    positivity
  unfold thetaBaseMixedTerm thetaBaseMixedMajorant
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n:ℝ))]
  calc
    _ ≤ (n:ℝ)^2 * thetaAllMixedJetIndexFactor i j x n :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hI

theorem thetaBaseMixedTerm_summable
    (i j : ℕ) (x u v : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1) (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    Summable (thetaBaseMixedTerm i j x u v) :=
  (thetaBaseMixedMajorant_summable i j x).of_norm_bounded
    (fun n => thetaBaseMixedTerm_norm_le i j x u v n hx hx1 hu hv)

theorem thetaBaseMixedTerm_hasDerivAt_left
    (i j : ℕ) (x u v : ℝ) (n : ℕ) :
    HasDerivAt (fun z => thetaBaseMixedTerm i j x z v n)
      (thetaBaseMixedTerm (i+1) j x u v n) u :=
  (thetaAllMixedJetTerm_hasDerivAt_left x v n 0 i j u).const_mul ((n:ℝ)^2)

theorem thetaBaseMixedTerm_hasDerivAt_right
    (j : ℕ) (x u v : ℝ) (n : ℕ) :
    HasDerivAt (fun z => thetaBaseMixedTerm 0 j x u z n)
      (thetaBaseMixedTerm 0 (j+1) x u v n) v := by
  by_cases hn : n = 0
  · subst n
    simp only [thetaBaseMixedTerm, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul]
    exact hasDerivAt_const v 0
  · have h := (thetaWeightedGaussianRightJet_hasDerivAt
      j x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) u v 0).const_mul
        (Real.exp (-((n:ℝ)^2-1)/x^2))
    have h' := h.const_mul ((n:ℝ)^2)
    simpa only [thetaBaseMixedTerm, thetaAllMixedJetTerm,
      thetaHigherRightJetSeriesTerm, if_neg hn] using h'

theorem thetaBaseMixedSeries_hasDerivAt_left
    (i j : ℕ) (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hv : |v| ≤ x/8) (hu : u ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt (fun z => ∑' n : ℕ, thetaBaseMixedTerm i j x z v n)
      (∑' n : ℕ, thetaBaseMixedTerm (i+1) j x u v n) u := by
  have hz : |(0:ℝ)| ≤ x/8 := by simp only [abs_zero]; positivity
  exact hasDerivAt_tsum_of_isPreconnected
    (thetaBaseMixedMajorant_summable (i+1) j x)
    (thetaGaussianSummableRightPatch_isOpen x)
    (thetaGaussianSummableRightPatch_isPreconnected x)
    (fun n z _ => thetaBaseMixedTerm_hasDerivAt_left i j x z v n)
    (fun n z hz => thetaBaseMixedTerm_norm_le (i+1) j x z v n hx hx1
      (thetaGaussianSummableRightPatch_abs_le x z hz) hv)
    (thetaGaussianSummableRightPatch_zero_mem x hx)
    (thetaBaseMixedTerm_summable i j x 0 v hx hx1 hz hv) hu

theorem thetaBaseMixedSeries_hasDerivAt_right
    (j : ℕ) (x u v : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : v ∈ thetaGaussianSummableRightPatch x) :
    HasDerivAt (fun z => ∑' n : ℕ, thetaBaseMixedTerm 0 j x u z n)
      (∑' n : ℕ, thetaBaseMixedTerm 0 (j+1) x u v n) v := by
  have hz : |(0:ℝ)| ≤ x/8 := by simp only [abs_zero]; positivity
  exact hasDerivAt_tsum_of_isPreconnected
    (thetaBaseMixedMajorant_summable 0 (j+1) x)
    (thetaGaussianSummableRightPatch_isOpen x)
    (thetaGaussianSummableRightPatch_isPreconnected x)
    (fun n z _ => thetaBaseMixedTerm_hasDerivAt_right j x u z n)
    (fun n z hz => thetaBaseMixedTerm_norm_le 0 (j+1) x u z n hx hx1 hu
      (thetaGaussianSummableRightPatch_abs_le x z hz))
    (thetaGaussianSummableRightPatch_zero_mem x hx)
    (thetaBaseMixedTerm_summable 0 j x u 0 hx hx1 hu hz) hv

end W5
