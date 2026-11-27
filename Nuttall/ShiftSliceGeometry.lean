import Nuttall.ShiftedThetaAlgebra
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace Nuttall

open MeasureTheory Set
open scoped BigOperators

/-- The normalization of an exponential Vandermonde factor absorbs
the fixed node on the positive half-line. -/
theorem abs_exp_four_sub_le {u v : ℝ} (hu : 0 ≤ u) :
    |Real.exp (4*u)-Real.exp (4*v)| ≤ Real.exp (4*u)*(1+Real.exp (4*v)) := by
  have h := Real.one_le_exp (show 0 ≤ 4*u by positivity)
  rw [sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos (Real.exp_pos _)]
  nlinarith [mul_nonneg (sub_nonneg.2 h) (Real.exp_pos (4*v)).le]

/-- Separation of two positive nodes yields a uniform lower bound for
the corresponding exponential Vandermonde factor. -/
theorem separated_exp_four_sub_lower {u v δ : ℝ} (hv : 0 ≤ v)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/4) (hsep : δ ≤ |u-v|) :
    δ*(1+Real.exp (4*v)) ≤ |Real.exp (4*u)-Real.exp (4*v)| := by
  let a := Real.exp (4*u)
  let b := Real.exp (4*v)
  let E := Real.exp (4*δ)
  have hb : 1 ≤ b := Real.one_le_exp (show 0 ≤ 4*v by positivity)
  have hE : 1+4*δ ≤ E := by dsimp [E]; linarith [Real.add_one_le_exp (4*δ)]
  have hδb := mul_le_mul_of_nonneg_left hb hδ
  change δ*(1+b) ≤ |a-b|
  rcases le_total u v with huv | hvu
  · rw [abs_of_nonpos (sub_nonpos.2 huv)] at hsep
    rw [abs_of_nonpos (sub_nonpos.2 (Real.exp_le_exp.2 (by linarith : 4*u ≤ 4*v)))]
    have hab : a*E ≤ b := by
      dsimp [a,b,E]
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have hc : 0 ≤ 1-2*δ := by linarith
    have hprod : 1 ≤ (1-2*δ)*E := by
      calc
        1 ≤ (1-2*δ)*(1+4*δ) := by nlinarith [mul_nonneg hδ (show 0 ≤ 1-4*δ by linarith)]
        _ ≤ (1-2*δ)*E := mul_le_mul_of_nonneg_left hE hc
    have ha : 0 ≤ a := (Real.exp_pos _).le
    have h₁ := mul_le_mul_of_nonneg_left hprod ha
    have h₂ := mul_le_mul_of_nonneg_left hab hc
    nlinarith only [hδb,h₁,h₂]
  · rw [abs_of_nonneg (sub_nonneg.2 hvu)] at hsep
    rw [abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (by linarith : 4*v ≤ 4*u)))]
    have hab : b*E ≤ a := by
      dsimp [a,b,E]
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h₁ := mul_le_mul_of_nonneg_left hE (show 0 ≤ b by linarith)
    nlinarith only [hδb, hab, h₁, mul_nonneg hδ (show 0 ≤ b by linarith)]

/-- The central weight is bounded below by its exponential scale at the
right endpoint of the short interval. -/
theorem central_thetaOrthantWeight_lower {X u : ℝ} (hX : 0 ≤ X) (hu : 0 ≤ u)
    (hu' : u ≤ 1/4) :
    Real.exp (-Real.exp 1*X) ≤ thetaOrthantWeight X u := by
  unfold thetaOrthantWeight
  apply Real.exp_le_exp.2
  have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (show 4*u ≤ 1 by linarith)) hX
  linarith

/-- Points of the short central interval that avoid every excluded interval. -/
def shiftSliceGoodSet (centers : Finset ℝ) (δ : ℝ) : Set ℝ :=
  Icc (1/8) (1/4) \ ⋃ c ∈ centers, Ioo (c-δ) (c+δ)

theorem measurableSet_shiftSliceGoodSet (centers : Finset ℝ) (δ : ℝ) :
    MeasurableSet (shiftSliceGoodSet centers δ) :=
  measurableSet_Icc.diff (Finset.measurableSet_biUnion centers (fun _ _ => measurableSet_Ioo))

theorem shiftSliceGoodSet_separates {centers : Finset ℝ} {u δ : ℝ}
    (hu : u ∈ shiftSliceGoodSet centers δ) {c : ℝ} (hc : c ∈ centers) : δ ≤ |u-c| := by
  by_contra! hn
  have hab := abs_lt.mp hn
  exact hu.2 (mem_iUnion.2 ⟨c, mem_iUnion.2 ⟨hc, by constructor <;> linarith⟩⟩)

/-- The excluded intervals remove at most their total length, so at least
one sixteenth remains under the budget from Section 4.1. -/
theorem shiftSliceGoodSet_volume_lower (centers : Finset ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : (centers.card:ℝ)*(2*δ) ≤ 1/16) :
    1/16 ≤ volume.real (shiftSliceGoodSet centers δ) := by
  let U (c : ℝ) := Ioo (c-δ) (c+δ)
  let bad := ⋃ c ∈ centers, U c
  have hU (c : ℝ) : volume (U c) ≠ ⊤ := by simp [U, Real.volume_Ioo]
  have hbad : volume bad ≠ ⊤ := by
    apply ne_of_lt
    exact (measure_biUnion_finset_le centers U).trans_lt (ENNReal.sum_lt_top.2 (fun c _ => (hU c).lt_top))
  have hlen : volume.real bad ≤ (centers.card:ℝ)*(2*δ) := by
    calc
      _ ≤ ∑ c ∈ centers, volume.real (U c) :=
        measureReal_biUnion_finset_le centers U
      _ = _ := by
        have he (c : ℝ) : volume.real (U c) = 2*δ := by
          dsimp [U]
          rw [Real.volume_real_Ioo_of_le (by linarith)]
          ring
        simp [he, nsmul_eq_mul]
  have hb := le_measureReal_sdiff (μ := volume) (s₁ := Icc (1/8:ℝ) (1/4))
    (s₂ := bad) hbad
  rw [Real.volume_real_Icc_of_le (by norm_num)] at hb
  change _ ≤ volume.real (Icc (1/8:ℝ) (1/4) \ bad)
  linarith

#print axioms separated_exp_four_sub_lower
#print axioms shiftSliceGoodSet_volume_lower

end Nuttall
