import W5.ThetaOneSquareCellGammaBridge
import W5.ThetaFirstCellRemaining50Bridge

/-!
# Remaining 50 theta cells: eliminate n=0 and n=1 real-term obligations

The original twelve-index prefix requires per-cell real interval
enclosures of n=0,...,11. The n=0 term is identically zero; the n=1
term has the rational, real-sound, uniformly valid Gamma/polynomial
interval constructed in ThetaOneSquareCellGammaBridge.

Use those proved facts INSTEAD OF requesting 50x15 duplicate proofs
for n=0,1. The outstanding ten terms n=2,...,11 and numerical
inclusion in each tight original audited cell matrix remain explicit.

The exact-rational 250 remaining LDL checks, the 10^-35 tail bound,
and final 51-cell cover all come from existing compiled modules.
-/

namespace W5

/-- Reuse this existing-interval-compatible first two-term prefix:
n=0 is exactly zero and n=1 has a genuine Gamma/Mathlib enclosure.
All higher terms are delegated to the remaining certified input. -/
noncomputable def thetaRemainingCellTermBoxes
    (a b : ℚ)
    (R : Matrix (Fin 5) (Fin 5) (ℕ → QInterval))
    (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then ⟨0, 0⟩
  else if n = 1 then thetaOneSquareCellTermBox a b i j
  else R i j n

/-- A REAL analytic certificate requiring only ten genuine
square-index term enclosures (n=2,...,11) per entry and cell.
The prefix-to-target rational containment is still an explicit,
independently checkable premise. -/
def ThetaRemainingTenTermCellCertificate
    (a b : ℚ) (C : ThetaIntervalMatrix) : Prop :=
  (1 / 8 : ℚ) < b ∧
    ∃ R : Matrix (Fin 5) (Fin 5) (ℕ → QInterval),
      (b : ℝ) ≤ (145 : ℝ)/256 ∧
      (∀ i j : Fin 5, i ≤ j →
        (C i j).lo ≤
          (QInterval.add
            (thetaAuditedPrefixInterval 12
              (thetaRemainingCellTermBoxes a b R i j))
            thetaAuditedTailErrorInterval).lo ∧
        (QInterval.add
          (thetaAuditedPrefixInterval 12
            (thetaRemainingCellTermBoxes a b R i j))
          thetaAuditedTailErrorInterval).hi ≤ (C i j).hi) ∧
      ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          ∀ n : ℕ, 2 ≤ n → n < 12 →
            QInterval.ContainsReal (R i j n)
              (thetaAuditedSeriesTerm x i j n)

/-- Every ten-term input produces the SAME existing verified
finite-term certificate; there is no new convergence, LDL,
matrix or tail argument. -/
theorem thetaRemainingTenTermCell_to_finite
    (a b : ℚ) (C : ThetaIntervalMatrix)
    (h : ThetaRemainingTenTermCellCertificate a b C) :
    ThetaAuditedFiniteCellCertificate a b C := by
  rcases h with ⟨hb8, R, hb, hinside, hrest⟩
  have hN : thetaAuditedCellCutoff b = 12 := by
    simp [thetaAuditedCellCutoff, not_le.mpr hb8]
  have hb1 : (b : ℝ) ≤ 1 := by linarith
  refine ⟨thetaRemainingCellTermBoxes a b R, hb, ?_, ?_⟩
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
          (thetaOneSquareCellTermBox a b i j)
          (thetaAuditedSeriesTerm x i j 1)
        exact thetaOneSquareCellTermBox_containsReal
          a b x hx hax hxb hb1 i j
      · change QInterval.ContainsReal (R i j n)
          (thetaAuditedSeriesTerm x i j n)
        exact hrest x hx hax hxb i j hij n (by omega) hn12

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
first-cell theorem and only TEN certified positive square indices
for each of the remaining 50 audited cells. The 50-cell residual
hypothesis and tight rational containment are NOT yet discharged. -/
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
