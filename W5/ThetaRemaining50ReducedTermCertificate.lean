import W5.ThetaFirstCellRemaining50Bridge

/-!
# Remaining 50 theta cells: eliminate n=0 and allow adaptive n=1

The original twelve-index prefix requires per-cell real interval
enclosures of n=0,...,11. The n=0 term is identically zero.
The existing coarse Gamma enclosure for n=1 is valid but is ALREADY
wider than the original fixed 768-bit interval in cell 2 at entry (0,0).
It therefore cannot close all 50 audited cells even with perfect
n=2,...,11 bounds.

We retain the reusable coarse-Gamma lemma, but allow a separate
TIGHT, genuinely sound n=1 enclosure when required. The outstanding
ten terms n=2,...,11 and numerical inclusion in each fixed original
audited cell matrix also remain explicit.

The exact-rational 250 remaining LDL checks, the 10^-35 tail bound,
and final 51-cell cover all come from existing compiled modules.
-/

namespace W5

/-- The exact n=0 term is zero; the n=1 term comes from an
independently certified cell interval J1 (which may use a sharper
enclosure than the existing coarse Gamma bound).
The higher indices are delegated to the original R input. -/
noncomputable def thetaRemainingCellTermBoxes
    (J1 : ThetaIntervalMatrix)
    (R : Matrix (Fin 5) (Fin 5) (ℕ → QInterval))
    (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then ⟨0, 0⟩
  else if n = 1 then J1 i j
  else R i j n

/-- A REAL analytic certificate for a separately certified n=1
interval and ten higher indices n=2,...,11 per entry and cell.
The exact n=0 proof is reused unconditionally. An explicit, sound
n=1 enclosure is necessary: the coarse Gamma enclosure alone cannot
fit the fixed original matrix on every audited cell.
Prefix-to-target rational containment is still a separate obligation. -/
def ThetaRemainingTenTermCellCertificate
    (a b : ℚ) (C : ThetaIntervalMatrix) : Prop :=
  (1 / 8 : ℚ) < b ∧
    ∃ J1 : ThetaIntervalMatrix,
    ∃ R : Matrix (Fin 5) (Fin 5) (ℕ → QInterval),
      (b : ℝ) ≤ (145 : ℝ)/256 ∧
      (∀ i j : Fin 5, i ≤ j →
        (C i j).lo ≤
          (QInterval.add
            (thetaAuditedPrefixInterval 12
              (thetaRemainingCellTermBoxes J1 R i j))
            thetaAuditedTailErrorInterval).lo ∧
        (QInterval.add
          (thetaAuditedPrefixInterval 12
            (thetaRemainingCellTermBoxes J1 R i j))
          thetaAuditedTailErrorInterval).hi ≤ (C i j).hi) ∧
      (∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          QInterval.ContainsReal (J1 i j)
            (thetaAuditedSeriesTerm x i j 1)) ∧
      ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          ∀ n : ℕ, 2 ≤ n → n < 12 →
            QInterval.ContainsReal (R i j n)
              (thetaAuditedSeriesTerm x i j n)

/-- The fixed 768-bit interval for the (0,0) entry on cell 2 is
STRICTLY narrower than the elementary coarse n=1 Gamma envelope.
This is a check over exact rationals, not a floating-point assertion.
The envelope uses b=177/512, M₀∈[1,1+b²] and x²/4∈[1/256,b²/4].
Consequently its width is (255/256)-(1-(b²/4)(1+b²)).
This finite obstruction motivates a selectable tighter n=1 box. -/
theorem thetaSecondCell_coarseGamma_n1_width_obstruction :
    (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).hi -
        (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).lo <
      (255 : ℚ) / 256 -
        (1 - (((177 : ℚ) / 512)^2 / 4) *
          (1 + ((177 : ℚ) / 512)^2)) := by
  native_decide

/-- Every certified n=1 plus ten higher-index inputs produce the
SAME verified finite-term certificate; there is no new convergence,
LDL, matrix, or tail argument. -/
theorem thetaRemainingTenTermCell_to_finite
    (a b : ℚ) (C : ThetaIntervalMatrix)
    (h : ThetaRemainingTenTermCellCertificate a b C) :
    ThetaAuditedFiniteCellCertificate a b C := by
  rcases h with ⟨hb8, J1, R, hb, hinside, hfirst, hrest⟩
  have hN : thetaAuditedCellCutoff b = 12 := by
    simp only [thetaAuditedCellCutoff, if_neg (not_le.mpr hb8)]
  have hb1 : (b : ℝ) ≤ 1 := by linarith
  refine ⟨thetaRemainingCellTermBoxes J1 R, hb, ?_, ?_⟩
  · simpa only [hN] using hinside
  · intro x hx hax hxb i j hij n hn
    have hn12 : n < 12 := by
      simpa only [hN] using (Finset.mem_range.mp hn)
    by_cases hn0 : n = 0
    · subst n
      change QInterval.ContainsReal (⟨0, 0⟩ : QInterval)
        (thetaAuditedSeriesTerm x i j 0)
      simp [thetaAuditedSeriesTerm_zero, QInterval.ContainsReal]
    · by_cases hn1 : n = 1
      · subst n
        change QInterval.ContainsReal
          (J1 i j) (thetaAuditedSeriesTerm x i j 1)
        exact hfirst x hx hax hxb i j hij
      · simpa only [thetaRemainingCellTermBoxes,
            if_neg hn0, if_neg hn1] using
          (hrest x hx hax hxb i j hij n (by omega) hn12)

/-- One list certificate for the 50 residual cells. No matrix
entries, original endpoints or pivot checks are copied. -/
def ThetaRemainingTenTermCertificateChain :
    ℚ → List ℚ → List ThetaIntervalMatrix → Prop
  | _, [], [] => True
  | a, b :: bs, C :: Cs =>
      ThetaRemainingTenTermCellCertificate a b C ∧
        ThetaRemainingTenTermCertificateChain b bs Cs
  | _, _, _ => False

theorem thetaRemainingTenTermChain_to_finite :
    ∀ (a : ℚ) (bs : List ℚ) (Cs : List ThetaIntervalMatrix),
      ThetaRemainingTenTermCertificateChain a bs Cs →
        ThetaAuditedFiniteCertificateChain a bs Cs := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      intro Cs h
      cases Cs with
      | nil => trivial
      | cons C Cs => exact False.elim h
  | cons b bs ih =>
      intro Cs h
      cases Cs with
      | nil => exact False.elim h
      | cons C Cs =>
          change ThetaRemainingTenTermCellCertificate a b C ∧
            ThetaRemainingTenTermCertificateChain b bs Cs at h
          rcases h with ⟨hfirst, hrest⟩
          change ThetaAuditedFiniteCellCertificate a b C ∧
            ThetaAuditedFiniteCertificateChain b bs Cs
          exact ⟨thetaRemainingTenTermCell_to_finite a b C hfirst,
            ih b Cs hrest⟩

/-- Global 51-cell positivity from the existing unconditional
first-cell theorem, a sharp n=1 enclosure and TEN certified
indices n=2,...,11 on each of the remaining 50 cells.
The 50-cell residual hypothesis and rational containment are OPEN. -/
theorem analyticMatrixPositive_of_remaining_50_ten_term_certificates
    (h : ThetaRemainingTenTermCertificateChain
      (1 / 8 : ℚ) (endpoints.drop 1)
      (thetaAuditUpperCellMatrices.drop 1)) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_50_finite_term_certificates
    (thetaRemainingTenTermChain_to_finite
      (1 / 8 : ℚ) (endpoints.drop 1)
      (thetaAuditUpperCellMatrices.drop 1) h)

end W5
