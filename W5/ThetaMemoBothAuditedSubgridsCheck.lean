import W5.ThetaMemoN1N2SelectedCellMatrix
import W5.ThetaAuditedSubcellRefinementReuse
import W5.ThetaThirdCellRemaining48Reduction

/-!
# One executable 48-cell audited-subgrid checker

For each original audited x-cell, choose ANY finite rational subgrid.
The source matrix at each subcell uses the already verified shared
n=1 and n=2 Gamma moments and the unchanged true theta series.

All finite checks are EXACT rational Booleans: admissible x-ranges,
original Gaussian and Gamma hypotheses, and 15 interval inclusions
into the original 768-bit target. The already proved 255 LDL signs
are reused wholesale and are NEVER recomputed for every subcell.

Only three reusable proofs: soundness for an arbitrary subgrid;
the general 48-cell induction; and the final implication to the
original analytic matrix-positivity target. No finite Boolean
outcome is postulated true. This does NOT prove W5.MainClaim.
-/

namespace W5

/-- The exact seven independent requirements for one source subcell;
the matrix inclusion check below is a separate eighth requirement. -/
def thetaMemoBothSubcellEligibility
    (steps : ℕ) (us : List ℚ) (a b : ℚ) : Bool :=
  decide ((0 : ℚ) < a ∧ a ≤ b ∧ b ≤ (145 : ℚ) / 256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b)

/-- One comparison against an EXISTING audited target, not a
fresh 5-pivot LDL evaluation for the generated source. -/
def thetaMemoBothSubcellAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  thetaMemoBothSubcellEligibility steps us a b &&
  thetaUpperMatrixRefinesCheck target
    (thetaMemoN1N2SelectedCellMatrix steps us K a b)

/-- For a subgrid [a,b1,...,bk], verify every generated source
is genuinely real-sound and contained in one fixed target matrix. -/
def thetaMemoBothSubgridAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      thetaMemoBothSubcellAuditCheck steps us K target a b &&
      thetaMemoBothSubgridAuditCheck steps us K target b bs

/-- One induction promotes ALL successful finite subcell checks
to REAL theta enclosures in the SAME original audited matrix.
This reuses the existing real-sound Gamma generator and the
previously checked rational inclusion-transitivity lemma. -/
theorem thetaMemoBothSubgridAuditCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (bs : List ℚ) :
    ∀ a : ℚ,
      thetaMemoBothSubgridAuditCheck
        steps us K target a bs = true →
      ThetaCellMatricesEnclose a bs
        (List.replicate bs.length target) := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a h
      have hp :
          thetaMemoBothSubcellAuditCheck
            steps us K target a b = true ∧
          thetaMemoBothSubgridAuditCheck
            steps us K target b bs = true := by
        simpa only [thetaMemoBothSubgridAuditCheck,
          Bool.and_eq_true] using h
      have hh :
          thetaMemoBothSubcellEligibility steps us a b = true ∧
          thetaUpperMatrixRefinesCheck target
            (thetaMemoN1N2SelectedCellMatrix
              steps us K a b) = true := by
        simpa only [thetaMemoBothSubcellAuditCheck,
          Bool.and_eq_true] using hp.1
      have he :
          (0 : ℚ) < a ∧ a ≤ b ∧ b ≤ (145 : ℚ) / 256 ∧
            ThetaBulkGaussianEligibility a b ∧
            thetaGammaAutoMomentCheck steps a us = true ∧
            thetaGammaAutoMomentCheck steps b us = true ∧
            ThetaBulkSelectedGammaEligibility
              steps us ({2} : Finset ℕ) a b :=
        of_decide_eq_true hh.1
      rcases he with ⟨ha, _, hb, hExp, hA, hB, hSel⟩
      change
        (∀ x : ℝ, 0 < x →
          (a : ℝ) ≤ x → x ≤ (b : ℝ) →
            ∀ i j : Fin 5, i ≤ j →
              QInterval.ContainsReal (target i j)
                (thetaCoefficient x i j)) ∧
        ThetaCellMatricesEnclose b bs
          (List.replicate bs.length target)
      refine ⟨?_, ih b hp.2⟩
      intro x hx hax hxb i j hij
      have hbR : (b : ℝ) ≤ (145 : ℝ)/256 := by
        have hc : (b : ℝ) ≤ (((145 : ℚ)/256):ℝ) := by
          exact_mod_cast hb
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
      have hSource := thetaMemoN1N2SelectedCellMatrix_containsReal
        steps us K a b x ha hx hax hxb hbR hExp hA hB hSel i j
      exact thetaUpperMatrixRefines_containsReal
        target (thetaMemoN1N2SelectedCellMatrix steps us K a b)
        (thetaUpperMatrixRefinesCheck_sound _ _ hh.2)
        (thetaCoefficient x i j) i j hij hSource

/-- A single Boolean traverses ALL original coarse cells. The
selected grid for each coarse cell must end at the original b.
Every subcell uses the exact shared Gamma evaluator; every
inclusion is tested against the EXISTING 768-bit audit target. -/
def thetaMemoBothAuditedSubgridsCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ) :
    ℚ → List ℚ → List ThetaIntervalMatrix →
      List (List ℚ) → Bool
  | _, [], [], [] => true
  | a, b :: bs, target :: targets, grid :: grids =>
      decide (lastFrom a grid = b ∧ grid ≠ []) &&
      thetaMemoBothSubgridAuditCheck
        steps us K target a grid &&
      thetaMemoBothAuditedSubgridsCheck
        steps us K b bs targets grids
  | _, _, _, _ => false

/-- Inductive soundness for all 48 source subgrids and all 48
fixed audited target matrices, without rechecking ANY old LDL. -/
theorem thetaMemoBothAuditedSubgridsCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (bs : List ℚ) :
    ∀ (a : ℚ) (targets : List ThetaIntervalMatrix)
      (grids : List (List ℚ)),
      thetaMemoBothAuditedSubgridsCheck
        steps us K a bs targets grids = true →
      ThetaCellMatricesEnclose a bs targets := by
  induction bs with
  | nil =>
      intro a targets grids h
      cases targets with
      | nil =>
          cases grids with
          | nil => trivial
          | cons grid grids =>
              simp [thetaMemoBothAuditedSubgridsCheck] at h
      | cons target targets =>
          simp [thetaMemoBothAuditedSubgridsCheck] at h
  | cons b bs ih =>
      intro a targets grids h
      cases targets with
      | nil =>
          simp [thetaMemoBothAuditedSubgridsCheck] at h
      | cons target targets =>
          cases grids with
          | nil =>
              simp [thetaMemoBothAuditedSubgridsCheck] at h
          | cons grid grids =>
              have hparts :
                  ((lastFrom a grid = b ∧ grid ≠ []) ∧
                    thetaMemoBothSubgridAuditCheck
                      steps us K target a grid = true) ∧
                  thetaMemoBothAuditedSubgridsCheck
                    steps us K b bs targets grids = true := by
                simpa only [thetaMemoBothAuditedSubgridsCheck,
                  Bool.and_eq_true, decide_eq_true_eq] using h
              rcases hparts with ⟨⟨⟨hlast, hne⟩, hcell⟩, hrest⟩
              have hsub : ThetaCellMatricesEnclose a grid
                  (List.replicate grid.length target) :=
                thetaMemoBothSubgridAuditCheck_sound
                  steps us K target grid a hcell
              change
                (∀ x : ℝ, 0 < x →
                  (a : ℝ) ≤ x → x ≤ (b : ℝ) →
                    ∀ i j : Fin 5, i ≤ j →
                      QInterval.ContainsReal (target i j)
                        (thetaCoefficient x i j)) ∧
                ThetaCellMatricesEnclose b bs targets
              refine ⟨?_, ih b targets grids hrest⟩
              intro x hx hax hxb i j hij
              have hchain : Chain a grid x := by
                apply chain_cover grid a x hax
                · rw [hlast]
                  exact hxb
                · exact hne
              exact thetaRepeatedTarget_contains_of_chain
                grid target a x hx hsub hchain i j hij

/-- One finite all-subgrid Boolean is enough for the original
theta sign pattern through order r=5. The first three cells are
already established independently in Lean, and the other 48
reuse their audited 5-pivot signs. W5.MainClaim remains OPEN
because the analytic-to-Wronskian jet bridge is separate. -/
theorem analyticMatrixPositive_of_memo_both_audited48_subgrids
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ))
    (hcheck : thetaMemoBothAuditedSubgridsCheck
      steps us K (821/2048 : ℚ)
      (endpoints.drop 3) (thetaAuditUpperCellMatrices.drop 3)
      grids = true) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_audited_enclosures
    (thetaMemoBothAuditedSubgridsCheck_sound
      steps us K (endpoints.drop 3)
      (821/2048 : ℚ)
      (thetaAuditUpperCellMatrices.drop 3) grids hcheck)

end W5
