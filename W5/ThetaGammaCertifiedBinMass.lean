import W5.ThetaGammaFiniteBinMassBox
import W5.ThetaGammaBinExpNegBox

/-!
# One fully generated Γ-bin mass from rational endpoint data

The earlier generic Γ mass theorem accepted *any* real-sound
exp(-L), exp(-U) enclosures, while the separate Mathlib-backed
Taylor/rational theorem supplies exact such enclosures for every
nonnegative rational L,U≤1024/3.

Compose these existing CI-green theorems. Every integration bin now
has a concrete computable rational mass box and ONE fixed family
of exact-rational endpoint hypotheses. No rational tables, guessed
transcendental values, or per-cell proofs.
-/

namespace W5

/-- Exact rational Gamma-bin mass enclosure computed using the
verified Taylor65 exp generator at both endpoints. -/
def thetaGammaCertifiedBinMassBox (k : ℕ) (L U : ℚ) : QInterval :=
  thetaGammaBinMassBox k L U
    (thetaGammaBinExpNegBox L)
    (thetaGammaBinExpNegBox U)

/-- The single rational endpoint validity predicate, independent
of all theta x-cells and of the Gamma moment degree k. -/
def thetaGammaCertifiedBinEligible (L U : ℚ) : Prop :=
  0 ≤ L ∧ L ≤ U ∧ U ≤ (1024:ℚ)/3 ∧
    0 < (thetaBulkExpTaylorBox (QInterval.point (L/1024))).lo ∧
    0 < (thetaBulkExpTaylorBox (QInterval.point (U/1024))).lo

/-- One theorem establishes the exact genuine Γ integral
inclusion for ALL admissible rational endpoints and ALL k.
The proof contains no new transcendental estimates: only
existing real-interval soundness and already-checked Taylor65. -/
theorem thetaGammaCertifiedBinMassBox_containsReal
    (k : ℕ) (L U : ℚ)
    (h : thetaGammaCertifiedBinEligible L U) :
    QInterval.ContainsReal
      (thetaGammaCertifiedBinMassBox k L U)
      (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^k) := by
  rcases h with ⟨hL, hLU, hU, hLP, hUP⟩
  have hL3 : L ≤ (1024:ℚ)/3 := hLU.trans hU
  have hU0 : (0:ℚ) ≤ U := hL.trans hLU
  exact thetaGammaBinMassBox_containsReal k L U
    (thetaGammaBinExpNegBox L)
    (thetaGammaBinExpNegBox U)
    (thetaGammaBinExpNegBox_containsReal L hL hL3 hLP)
    (thetaGammaBinExpNegBox_containsReal U hU0 hU hUP)

/-- Exact decidability of the purely rational endpoint requirements. -/
instance thetaGammaCertifiedBinEligible_decidable (L U : ℚ) :
    Decidable (thetaGammaCertifiedBinEligible L U) := by
  unfold thetaGammaCertifiedBinEligible
  infer_instance

/-- The final eligibility check is a finite rational Boolean.
Proving a list of bins eligible needs ONLY one native_decide pass
over this fixed predicate, never one theorem per bin. -/
def thetaGammaCertifiedBinEligibleCheck (L U : ℚ) : Bool :=
  decide (thetaGammaCertifiedBinEligible L U)

theorem thetaGammaCertifiedBinMassBox_containsReal_of_check
    (k : ℕ) (L U : ℚ)
    (h : thetaGammaCertifiedBinEligibleCheck L U = true) :
    QInterval.ContainsReal
      (thetaGammaCertifiedBinMassBox k L U)
      (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^k) := by
  apply thetaGammaCertifiedBinMassBox_containsReal
  exact of_decide_eq_true h

end W5
