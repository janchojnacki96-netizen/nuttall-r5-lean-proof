import W5.ThetaAuditedMatrixRefinementReuse

/-!
# Subdivide analytic cells without recomputing any audited LDL pivot

The original 51-cell 768-bit audit has *already* checked all 255
alternating LDL signs. A coarse analytic enclosure on [a,b] can be too
wide to fit the audited box even though much smaller genuine analytic
enclosures on a subdivision would each fit.

This module proves the exact general reduction: split EACH of the 51
cells into any finite rational subgrid; establish sound real theta
enclosures on the subcells and 15-entry rational inclusion in the ONE
original audited matrix for the containing coarse cell. Reuse its five
already verified pivots; do NOT rerun LDL for each subcell.

All subgrid coverage, source soundness, and rational inclusions remain
explicit hypotheses. No numerical claim is invented and W5.MainClaim
is not deduced here.
-/

namespace W5

/-- The same interval matrix encloses theta on a whole finite
subdivision when it encloses theta on each subcell. This consumes
only the previously proved chain coverage predicate. -/
theorem thetaRepeatedTarget_contains_of_chain
    (bs : List ℚ) (target : ThetaIntervalMatrix) :
    ∀ (a : ℚ) (x : ℝ), 0 < x →
      ThetaCellMatricesEnclose a bs
        (List.replicate bs.length target) →
      Chain a bs x →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j) (thetaCoefficient x i j) := by
  induction bs with
  | nil =>
      intro a x hx hs hchain i j hij
      change False at hchain
      exact False.elim hchain
  | cons b bs ih =>
      intro a x hx hs hchain i j hij
      have hpair :
          (∀ y : ℝ, 0 < y →
            (a : ℝ) ≤ y → y ≤ (b : ℝ) →
              ∀ k l : Fin 5, k ≤ l →
                QInterval.ContainsReal
                  (target k l) (thetaCoefficient y k l)) ∧
          ThetaCellMatricesEnclose b bs
            (List.replicate bs.length target) := by
        change
          (∀ y : ℝ, 0 < y →
            (a : ℝ) ≤ y → y ≤ (b : ℝ) →
              ∀ k l : Fin 5, k ≤ l →
                QInterval.ContainsReal
                  (target k l) (thetaCoefficient y k l)) ∧
          ThetaCellMatricesEnclose b bs
            (List.replicate bs.length target) at hs
        exact hs
      change (((a : ℝ) ≤ x) ∧ x ≤ (b : ℝ)) ∨
        Chain b bs x at hchain
      rcases hchain with hfirst | hrest
      · exact hpair.1 x hx hfirst.1 hfirst.2 i j hij
      · exact ih b x hx hpair.2 hrest i j hij

/-- A single coarse audited matrix suffices on the whole original
[a,b] cell when exact-rational subinterval source matrices fit into
it and the subintervals reach b from a.

No extra LDL sign test is performed: the identical target matrix is
reused for every subcell through the existing general refinement proof. -/
theorem thetaAuditedTarget_contains_of_subgrid
    (a b : ℚ) (target : ThetaIntervalMatrix)
    (grid : List ℚ) (sources : List ThetaIntervalMatrix)
    (hlast : lastFrom a grid = b)
    (hne : grid ≠ [])
    (hsource : ThetaCellMatricesEnclose a grid sources)
    (hfit : thetaUpperMatrixRefinementsCheck
      (List.replicate grid.length target) sources = true) :
    ∀ x : ℝ, 0 < x →
      (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j)
          (thetaCoefficient x i j) := by
  have htarget : ThetaCellMatricesEnclose a grid
      (List.replicate grid.length target) :=
    thetaCellMatricesEnclose_of_refinements a grid
      (List.replicate grid.length target) sources hsource hfit
  intro x hx hax hxb i j hij
  have hchain : Chain a grid x := by
    apply chain_cover grid a x hax
    · rw [hlast]
      exact hxb
    · exact hne
  exact thetaRepeatedTarget_contains_of_chain grid target
    a x hx htarget hchain i j hij

/-- One data structure for all 51 original audit cells with
independent subdivisions and independent source matrices per cell.
In each coarse cell the last subgrid endpoint must be that cell's
original right endpoint, and the grid may not be empty. -/
def ThetaAuditedSubgridEncloses :
    ℚ → List ℚ → List ThetaIntervalMatrix →
      List (List ℚ) → List (List ThetaIntervalMatrix) → Prop
  | _, [], [], [], [] => True
  | a, b :: bs, target :: targets, grid :: grids, source :: sources =>
      lastFrom a grid = b ∧
      grid ≠ [] ∧
      ThetaCellMatricesEnclose a grid source ∧
      thetaUpperMatrixRefinementsCheck
        (List.replicate grid.length target) source = true ∧
      ThetaAuditedSubgridEncloses b bs targets grids sources
  | _, _, _, _, _ => False

/-- One induction handles any number of subcells within each
original cell, with no new matrix elimination and no 51 case proofs. -/
theorem thetaAuditedSubgridEncloses_sound (bs : List ℚ) :
    ∀ (a : ℚ) (targets : List ThetaIntervalMatrix)
      (grids : List (List ℚ))
      (sources : List (List ThetaIntervalMatrix)),
      ThetaAuditedSubgridEncloses a bs targets grids sources →
      ThetaCellMatricesEnclose a bs targets := by
  induction bs with
  | nil =>
      intro a targets grids sources h
      cases targets with
      | nil =>
          cases grids with
          | nil =>
              cases sources with
              | nil => trivial
              | cons S Ss =>
                  simp [ThetaAuditedSubgridEncloses] at h
          | cons grid grids =>
              simp [ThetaAuditedSubgridEncloses] at h
      | cons target targets =>
          simp [ThetaAuditedSubgridEncloses] at h
  | cons b bs ih =>
      intro a targets grids sources h
      cases targets with
      | nil =>
          simp [ThetaAuditedSubgridEncloses] at h
      | cons target targets =>
          cases grids with
          | nil =>
              simp [ThetaAuditedSubgridEncloses] at h
          | cons grid grids =>
              cases sources with
              | nil =>
                  simp [ThetaAuditedSubgridEncloses] at h
              | cons source sources =>
                  have hparts :
                      lastFrom a grid = b ∧
                      grid ≠ [] ∧
                      ThetaCellMatricesEnclose a grid source ∧
                      thetaUpperMatrixRefinementsCheck
                        (List.replicate grid.length target) source = true ∧
                      ThetaAuditedSubgridEncloses
                        b bs targets grids sources := by
                    change
                      lastFrom a grid = b ∧
                      grid ≠ [] ∧
                      ThetaCellMatricesEnclose a grid source ∧
                      thetaUpperMatrixRefinementsCheck
                        (List.replicate grid.length target) source = true ∧
                      ThetaAuditedSubgridEncloses
                        b bs targets grids sources at h
                    exact h
                  rcases hparts with
                    ⟨hlast, hne, hsource, hfit, htail⟩
                  change
                    (∀ x : ℝ, 0 < x →
                      (a : ℝ) ≤ x → x ≤ (b : ℝ) →
                        ∀ i j : Fin 5, i ≤ j →
                          QInterval.ContainsReal (target i j)
                            (thetaCoefficient x i j)) ∧
                    ThetaCellMatricesEnclose b bs targets
                  exact ⟨thetaAuditedTarget_contains_of_subgrid
                    a b target grid source hlast hne hsource hfit,
                    ih b targets grids sources htail⟩

/-- The ENTIRE imported 51-cell/255-pivot audit can be reused
unchanged after arbitrarily fine analytic subcell refinements.
The substantial source interval and inclusion obligations are explicit
and are NOT yet discharged by this theorem. -/
theorem analyticMatrixPositive_of_audited_subgrid_refinements
    (grids : List (List ℚ))
    (sources : List (List ThetaIntervalMatrix))
    (hsub : ThetaAuditedSubgridEncloses
      0 endpoints thetaAuditUpperCellMatrices grids sources) :
    analyticMatrixPositive := by
  exact analyticMatrixPositive_of_audited_768bit_enclosures
    (thetaAuditedSubgridEncloses_sound endpoints
      0 thetaAuditUpperCellMatrices grids sources hsub)

end W5
