import W5.ThetaAuditedCorrectionIntegral
import W5.ThetaSeriesPrefixTailEnclosure

/-!
# Full ORIGINAL theta-coefficient tail dominated by audited majorant

This combines the already-proved base-term bound with the new genuine
integral-correction bound. The same polynomial-Gaussian envelope applies
to ALL 25 theta coefficient entries and retains the full square-index
Gaussian factor, not merely an integrability surrogate.

The total per-term multiplier is bounded by the EXACT auditor constant
5*4096*30000000000, since 1+16926797486 < 30000000000.

The already existing geometric tail and uniform x-range theorems then
give strict 10^(-35) bounds for the true original (base-correction)
infinite tails, for both finite-prefix cutoffs N=12 and N=2.
No finite-prefix enclosure or determinant conclusion is inferred here.
-/

namespace W5

/-- Original n-th theta coefficient term (base minus integrated
correction) satisfies the exact per-index multiplier allowed by
the independent 768-bit auditor, for every entry of Fin 5 x Fin 5. -/
theorem thetaAuditedSeriesTerm_abs_le_majorant
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 2 ≤ n) :
    |thetaAuditedSeriesTerm x i j n| ≤
      ((5*4096*30000000000 : ℝ)*(1/x^2)^4) *
        thetaMajorantTerm (1/x^2) n := by
  have hb := thetaCertificateBaseTerm_abs_le_audited_majorant
    x hx hx1 i j n hn
  have hc := thetaCertificateCorrectionTerm_abs_le_audited_majorant
    x hx hx1 i j n hn
  have hnonneg :
      0 ≤ (1/x^2)^4 * thetaMajorantTerm (1/x^2) n := by
    dsimp [thetaMajorantTerm]
    positivity
  calc
    |thetaAuditedSeriesTerm x i j n| =
      |thetaCertificateBaseTerm x i j n -
        thetaCertificateCorrectionTerm x i j n| := rfl
    _ ≤ |thetaCertificateBaseTerm x i j n| +
          |thetaCertificateCorrectionTerm x i j n| := abs_sub _ _
    _ ≤ (5*4096 : ℝ)*(1/x^2)^4 *
          thetaMajorantTerm (1/x^2) n +
        (5*4096*16926797486 : ℝ)*(1/x^2)^4 *
          thetaMajorantTerm (1/x^2) n := add_le_add hb hc
    _ = (5*4096*16926797487 : ℝ) *
        ((1/x^2)^4 * thetaMajorantTerm (1/x^2) n) := by ring
    _ ≤ (5*4096*30000000000 : ℝ) *
        ((1/x^2)^4 * thetaMajorantTerm (1/x^2) n) :=
      mul_le_mul_of_nonneg_right (by norm_num) hnonneg
    _ = ((5*4096*30000000000 : ℝ)*(1/x^2)^4) *
        thetaMajorantTerm (1/x^2) n := by ring

/-- Full infinite tail of ORIGINAL theta coefficient n-series is
bounded by the already-certified Gaussian majorant tsum. No
new geometric argument or convergence theorem is duplicated. -/
theorem thetaAuditedTail_abs_le_majorant_tsum
    (N : ℕ) (hN : 2 ≤ N)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : (3:ℝ) ≤ 1/x^2) (i j : Fin 5) :
    |thetaAuditedTail N x i j| ≤
      ((5*4096*30000000000 : ℝ)*(1/x^2)^4) *
        (∑' k : ℕ, thetaMajorantTerm (1/x^2) (N+k)) := by
  let y : ℝ := 1/x^2
  let C : ℝ := (5*4096*30000000000 : ℝ)*y^4
  have hmajor : Summable (fun k : ℕ =>
      C * thetaMajorantTerm y (N+k)) :=
    (thetaMajorantTerm_tail_summable N hN y hy).mul_left C
  have hpoint : ∀ k : ℕ,
      |thetaAuditedSeriesTerm x i j (k+N)| ≤
        C*thetaMajorantTerm y (N+k) := by
    intro k
    have h := thetaAuditedSeriesTerm_abs_le_majorant
      x hx hx1 i j (k+N) (by omega)
    simpa only [C, y, Nat.add_comm] using h
  have habs : Summable (fun k : ℕ =>
      |thetaAuditedSeriesTerm x i j (k+N)|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hpoint hmajor
  have hnorm :
      |thetaAuditedTail N x i j| ≤
        ∑' k : ℕ, |thetaAuditedSeriesTerm x i j (k+N)| := by
    have h := norm_tsum_le_tsum_norm
      (by simpa only [Real.norm_eq_abs] using habs)
    simpa only [thetaAuditedTail, Real.norm_eq_abs] using h
  have hcompare := habs.tsum_le_tsum hpoint hmajor
  calc
    |thetaAuditedTail N x i j| ≤
        ∑' k : ℕ, |thetaAuditedSeriesTerm x i j (k+N)| := hnorm
    _ ≤ ∑' k : ℕ, C*thetaMajorantTerm y (N+k) := hcompare
    _ = C * (∑' k : ℕ, thetaMajorantTerm y (N+k)) := by
      rw [tsum_mul_left]
    _ = ((5*4096*30000000000 : ℝ)*(1/x^2)^4) *
          (∑' k : ℕ, thetaMajorantTerm (1/x^2) (N+k)) := rfl

/-- The genuine original theta tail after n=11 is uniformly
smaller than 10^-35 on the entire near-cell audited domain. -/
theorem thetaAuditedNearTail_abs_lt_oneE35
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (145:ℝ)/256)
    (i j : Fin 5) :
    |thetaAuditedTail 12 x i j| < 1/(10:ℝ)^35 := by
  have hx1 : x ≤ 1 := by linarith
  have hy : (3:ℝ) ≤ 1/x^2 := thetaAuditor_y_ge_three x hx hxB
  exact (thetaAuditedTail_abs_le_majorant_tsum
    12 (by norm_num) x hx hx1 hy i j).trans_lt
      (thetaAuditorNearMajorant_on_x_domain x hx hxB)

/-- The genuine original theta tail after n=1 is uniformly
smaller than 10^-35 for all 0<x<=1/8 (far-cell regime). -/
theorem thetaAuditedFarTail_abs_lt_oneE35
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1:ℝ)/8)
    (i j : Fin 5) :
    |thetaAuditedTail 2 x i j| < 1/(10:ℝ)^35 := by
  have hx1 : x ≤ 1 := by linarith
  have hy64 : (64:ℝ) ≤ 1/x^2 :=
    thetaAuditor_y_ge_sixtyfour x hx hxB
  have hy : (3:ℝ) ≤ 1/x^2 := by linarith
  exact (thetaAuditedTail_abs_le_majorant_tsum
    2 (by norm_num) x hx hx1 hy i j).trans_lt
      (thetaAuditorFarMajorant_on_x_domain x hx hxB)

end W5
