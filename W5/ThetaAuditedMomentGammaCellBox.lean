import W5.ThetaAuditedMomentGammaQuadraticLower

/-!
# Reusable sharp two-sided Gamma boxes on any nonnegative rational x-cell

The old and quarter-Gamma boxes have only the base factorial as
their lower endpoint. This module combines a genuine second-order
fourth-root lower bound at the LEFT x-cell endpoint with the existing
quarter-Gamma upper bound at the RIGHT endpoint.

Crucially, the passage from the left endpoint to the actual x
uses the PRE-EXISTING monotonicity theorem for Lebesgue moments,
not an unverified claim that the quadratic polynomial is monotone.
The construction works uniformly for all n>0 and all k.
-/

namespace W5

/-- Exact rational two-sided enclosure for a genuine theta Gamma
moment with index n, based on x in the full interval [a,b]. -/
def thetaNthQuadraticGammaMomentBox (a b : ℚ) (n k : ℕ) : QInterval :=
  ⟨(Nat.factorial k : ℚ) +
      (((a / (n : ℚ))^2) / 4) * (Nat.factorial (k+1) : ℚ) -
      (3 * ((a / (n : ℚ))^4) / 32) *
        (Nat.factorial (k+2) : ℚ),
   (Nat.factorial k : ℚ) +
      (((b / (n : ℚ))^2) / 4) *
        (Nat.factorial (k+1) : ℚ)⟩

/-- Uniform *real* semantic soundness of the sharp rational box.
It uses exactly the quadratic lower integral at the left endpoint,
the previously verified real monotonicity, and the quarter-Gamma
upper bound at the right endpoint. No new integral is taken here. -/
theorem thetaNthQuadraticGammaMomentBox_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ))
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (n k : ℕ) (hn : 0 < n) :
    QInterval.ContainsReal
      (thetaNthQuadraticGammaMomentBox a b n k)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hnR1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  let left : ℝ := (a:ℝ)/(n:ℝ)
  let mid : ℝ := x/(n:ℝ)
  let right : ℝ := (b:ℝ)/(n:ℝ)
  have hleft0 : 0 ≤ left := div_nonneg ha hnR.le
  have hleftMid : left ≤ mid := by
    dsimp [left, mid]
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hax (inv_nonneg.mpr hnR.le)
  have hmidRight : mid ≤ right := by
    dsimp [mid, right]
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hxb (inv_nonneg.mpr hnR.le)
  have hright1 : right ≤ 1 := by
    dsimp [right]
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hmid1 : mid ≤ 1 := hmidRight.trans hright1
  have hleft1 : left ≤ 1 := hleftMid.trans hmid1
  have hquadratic :=
    thetaAuditedOneWeightedMoment_gamma_lower_quadratic
      left hleft0 hleft1 k
  have hmonotone :=
    thetaAuditedOneWeightedMoment_mono
      left mid hleft0 hleftMid hmid1 k
  have hbelow :
      (Nat.factorial k : ℝ) +
          (left^2/4) * (Nat.factorial (k+1) : ℝ) -
          (3*left^4/32) * (Nat.factorial (k+2) : ℝ) ≤
        thetaAuditedOneWeightedMoment mid k :=
    hquadratic.trans hmonotone
  have hlo :
      ((thetaNthQuadraticGammaMomentBox a b n k).lo : ℝ) ≤
        thetaAuditedOneWeightedMoment (x/(n:ℝ)) k := by
    dsimp [left, mid] at hbelow
    simpa only [thetaNthQuadraticGammaMomentBox,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hbelow
  have hu :
      thetaAuditedOneWeightedMoment (x/(n:ℝ)) k ≤
        ((thetaNthQuadraticGammaMomentBox a b n k).hi : ℝ) :=
    (thetaNthQuarterGammaMomentBox_containsReal
      b x (ha.trans hax) hxb hb n k hn).2
  exact ⟨hlo, hu⟩

end W5
