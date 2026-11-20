import W5.ThetaAllFiveActualLeadingMinorSigns
import W5.FiniteCore

/-!
# Reduce the original theta sign target to 51 exact rational interval cells

The previously kernel-verified `W5.cover_51` proves that 51 adjacent
rational intervals cover x∈[0,145/256]. The interval-based sign theorem
requires, at each x, some 5×5 rational interval matrix enclosing the
25 ORIGINAL thetaCoefficient entries and passing the finite LDL test.

Here we prove a constructive logical reduction: it suffices to supply
ONE constant rational interval matrix for each of the 51 cells,
with (i) a real entry enclosure valid uniformly over that cell and
(ii) the exact rational five-pivot check. The existing chain coverage
then supplies the correct matrix for every x in the required range.

This closes the finite-COVERAGE part, not the transcendental
entry-bound or rational-check computation. No assumptions are hidden.
-/

namespace W5

/-- A *single* exact 5×5 rational interval matrix certifying the actual
25 real theta coefficients UNIFORMLY on a rational x-cell [a,b].
The five rational LDL checks are independent of x once B is fixed. -/
def ThetaRealCellCertificate (a b : ℚ) : Prop :=
  ∃ B : Matrix (Fin 5) (Fin 5) QInterval,
    intervalLDL5Alternating B ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5,
          QInterval.ContainsReal (B i j) (thetaCoefficient x i j)

/-- Provide a real-cell certificate for every adjacent interval
in an arbitrary rational endpoint chain, including the 51-cell chain. -/
def ThetaRealCellCertificateChain (a : ℚ) : List ℚ → Prop
  | [] => True
  | b :: bs =>
      ThetaRealCellCertificate a b ∧
        ThetaRealCellCertificateChain b bs

/-- Extract a genuine real-theta interval certificate at any point
of a certified rational endpoint chain. This proves the soundness
of the interval partition selection, without numeric approximations. -/
theorem theta_real_interval_certificate_of_chain (bs : List ℚ) :
    ∀ (a : ℚ) (x : ℝ),
      ThetaRealCellCertificateChain a bs →
      Chain a bs x →
      ∃ B : Matrix (Fin 5) (Fin 5) QInterval,
        (∀ i j : Fin 5,
          QInterval.ContainsReal (B i j) (thetaCoefficient x i j)) ∧
        intervalLDL5Alternating B := by
  induction bs with
  | nil =>
      intro a x _ hmem
      exact False.elim hmem
  | cons b bs ih =>
      intro a x hcert hmem
      change ThetaRealCellCertificate a b ∧
        ThetaRealCellCertificateChain b bs at hcert
      rcases hcert with ⟨hfirst, hrest⟩
      change (((a : ℝ) ≤ x) ∧ x ≤ (b : ℝ)) ∨
        Chain b bs x at hmem
      rcases hmem with hab | hmore
      · rcases hfirst with ⟨B, hchecks, hentry⟩
        refine ⟨B, ?_, hchecks⟩
        intro i j
        exact hentry x hab.1 hab.2 i j
      · exact ih b x hrest hmore

/-- Only the 51 concrete cells remain to be certified:
their validity yields all five signs of the ACTUAL theta matrix
uniformly on the original Nuttall parameter range.

Note that `ThetaRealCellCertificateChain 0 endpoints` remains
a nontrivial explicit hypothesis, not a computed Lean proof. -/
theorem analyticMatrixPositive_of_51_real_cell_certificates
    (hcells : ThetaRealCellCertificateChain 0 endpoints) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_real_interval_family
  intro x hx hbound
  have hchain : Chain 0 endpoints x :=
    cover_51 x hx.le hbound
  exact theta_real_interval_certificate_of_chain endpoints
    0 x hcells hchain

end W5
