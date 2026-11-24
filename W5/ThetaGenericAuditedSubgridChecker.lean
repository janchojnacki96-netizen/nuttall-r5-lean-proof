import W5.ThetaEarlyRoundedBothCellMatrix
import W5.ThetaMemoBothAuditedSubgridsCheck

/-!
# Generic real-sound audit transfer for arbitrarily refined x-subgrids

Reuse the proved 255 original theta LDL signs without recomputing
Schur pivots. A numerical method provides only a Boolean check for
one target audited matrix on one small rational x-cell, together
with a theorem that check=true genuinely encloses thetaCoefficient.

One generic induction transports ANY such sound checker through an
arbitrary rational subgrid, then through all 48 remaining audited
original cells. No separate formalization per cell, choice of
Gamma precision, or numerical approximation scheme is necessary.

The concrete instance uses the CI-checked early-rounded n=1/n=2
Gamma coefficient matrix. This module does NOT assert the final
48-cell Boolean true and does NOT prove W5.MainClaim.
-/

namespace W5

/-- Traverse any finite rational subgrid with a reusable Boolean
enclosure test against ONE fixed audited target matrix. -/
def thetaGenericSubgridAuditCheck
    (check : ThetaIntervalMatrix → ℚ → ℚ → Bool)
    (target : ThetaIntervalMatrix) : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      check target a b &&
      thetaGenericSubgridAuditCheck check target b bs

/-- A sound single-subcell Boolean yields an analytic enclosure
throughout every subcell in any rational endpoint chain. -/
theorem thetaGenericSubgridAuditCheck_sound
    (check : ThetaIntervalMatrix → ℚ → ℚ → Bool)
    (hcheck : ∀ (target : ThetaIntervalMatrix) (a b : ℚ),
      check target a b = true →
      ∀ (x : ℝ), 0 < x →
        (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          QInterval.ContainsReal (target i j)
            (thetaCoefficient x i j))
    (target : ThetaIntervalMatrix) (bs : List ℚ) :
    ∀ a : ℚ,
      thetaGenericSubgridAuditCheck check target a bs = true →
      ThetaCellMatricesEnclose a bs
        (List.replicate bs.length target) := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a h
      have hs :
          check target a b = true ∧
          thetaGenericSubgridAuditCheck check target b bs = true := by
        simpa only [thetaGenericSubgridAuditCheck,
          Bool.and_eq_true] using h
      change
        (∀ x : ℝ, 0 < x →
          (a : ℝ) ≤ x → x ≤ (b : ℝ) →
          ∀ i j : Fin 5, i ≤ j →
            QInterval.ContainsReal (target i j)
              (thetaCoefficient x i j)) ∧
        ThetaCellMatricesEnclose b bs
          (List.replicate bs.length target)
      exact ⟨hcheck target a b hs.1, ih b hs.2⟩

/-- One Boolean covering ANY finite collection of audited x-cells.
Each original cell [a,b] can have a distinct and arbitrarily fine
subgrid; all subgrids are checked to end exactly at b. -/
def thetaGenericAuditedSubgridsCheck
    (check : ThetaIntervalMatrix → ℚ → ℚ → Bool) :
    ℚ → List ℚ → List ThetaIntervalMatrix →
      List (List ℚ) → Bool
  | _, [], [], [] => true
  | a, b :: bs, target :: targets, grid :: grids =>
      decide (lastFrom a grid = b ∧ grid ≠ []) &&
      thetaGenericSubgridAuditCheck check target a grid &&
      thetaGenericAuditedSubgridsCheck check b bs targets grids
  | _, _, _, _ => false

/-- The ONE 48-cell transfer theorem for ANY sound numerical
method. All rational coverage, real theta enclosures, and exact
audited-matrix inclusions are justified by the Boolean and its
single-subcell soundness proof, not by an assumed sign. -/
theorem thetaGenericAuditedSubgridsCheck_sound
    (check : ThetaIntervalMatrix → ℚ → ℚ → Bool)
    (hcheck : ∀ (target : ThetaIntervalMatrix) (a b : ℚ),
      check target a b = true →
      ∀ (x : ℝ), 0 < x →
        (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          QInterval.ContainsReal (target i j)
            (thetaCoefficient x i j))
    (bs : List ℚ) :
    ∀ (a : ℚ) (targets : List ThetaIntervalMatrix)
      (grids : List (List ℚ)),
      thetaGenericAuditedSubgridsCheck
        check a bs targets grids = true →
      ThetaCellMatricesEnclose a bs targets := by
  induction bs with
  | nil =>
      intro a targets grids h
      cases targets with
      | nil =>
          cases grids with
          | nil => trivial
          | cons grid grids =>
              simp [thetaGenericAuditedSubgridsCheck] at h
      | cons target targets =>
          simp [thetaGenericAuditedSubgridsCheck] at h
  | cons b bs ih =>
      intro a targets grids h
      cases targets with
      | nil =>
          simp [thetaGenericAuditedSubgridsCheck] at h
      | cons target targets =>
          cases grids with
          | nil =>
              simp [thetaGenericAuditedSubgridsCheck] at h
          | cons grid grids =>
              have hparts :
                  ((lastFrom a grid = b ∧ grid ≠ []) ∧
                    thetaGenericSubgridAuditCheck
                      check target a grid = true) ∧
                  thetaGenericAuditedSubgridsCheck
                    check b bs targets grids = true := by
                simpa only [thetaGenericAuditedSubgridsCheck,
                  Bool.and_eq_true, decide_eq_true_eq] using h
              rcases hparts with ⟨⟨⟨hlast, hne⟩, hcell⟩, hrest⟩
              have hsub : ThetaCellMatricesEnclose a grid
                  (List.replicate grid.length target) :=
                thetaGenericSubgridAuditCheck_sound
                  check hcheck target grid a hcell
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

/-- Use already checked REAL semantics of the early-rounded
original n=1/n=2 theta source with the generic 48-cell checker. -/
def thetaEarlyRoundedAudited48Check
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ)) : Bool :=
  thetaGenericAuditedSubgridsCheck
    (thetaEarlyRoundedBothCellAuditCheck steps us K)
    (821/2048 : ℚ) (endpoints.drop 3)
    (thetaAuditUpperCellMatrices.drop 3) grids

/-- One successful finite exact-rational Boolean supplies all
48 remaining REAL original theta enclosures and hence the
original signed analytic 5x5-matrix positivity target. The
numerical Boolean is a real outstanding obligation. -/
theorem analyticMatrixPositive_of_early_rounded_48_subgrids
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ))
    (h : thetaEarlyRoundedAudited48Check steps us K grids = true) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_audited_enclosures
  exact thetaGenericAuditedSubgridsCheck_sound
    (thetaEarlyRoundedBothCellAuditCheck steps us K)
    (fun target a b => thetaEarlyRoundedBothCellAuditCheck_sound
      steps us K target a b)
    (endpoints.drop 3)
    (821/2048 : ℚ) (thetaAuditUpperCellMatrices.drop 3)
    grids h

/-- A reproducible initial two-half subdivision per original
cell, usable for a finite diagnostic. Finer or adaptive lists
may be supplied instead without changing any proof. -/
def thetaBisectAuditedGrids : ℚ → List ℚ → List (List ℚ)
  | _, [] => []
  | a, b :: bs =>
      [(a+b)/2, b] :: thetaBisectAuditedGrids b bs

end W5
