import W5.ThetaAudited51CellCertificateBridge

/-!
# Reuse ALL 255 already verified 768-bit LDL pivots by interval refinement

The original audit imported 51 matrices whose five LDL pivot signs were
already formally checked, but the transcendental theta enclosures are
still open. A separate certified analytic generator provides correct
rational intervals which may differ from the audit's own data.

There is NO reason to recompute five expensive LDL pivots per generated
matrix. One exact-rational inclusion check of the 15 upper-triangle
entries suffices to transfer the analytic enclosure to the ALREADY
audited matrix. This module proves that soundness once, for any list of
cells and any choice of source generator.

All inclusions are explicit executable rational inequalities.
Neither the 51-cell inclusion Boolean nor W5.MainClaim is asserted true.
-/

namespace W5

/-- Only the 15 independent upper-triangle source intervals need
to fit INSIDE the corresponding original audited target intervals. -/
def ThetaUpperMatrixRefines
    (target source : ThetaIntervalMatrix) : Prop :=
  ∀ i j : Fin 5, i ≤ j →
    (target i j).lo ≤ (source i j).lo ∧
    (source i j).hi ≤ (target i j).hi

/-- Exactly 15 rational comparisons; finite quantification is
decidable without any analytic or numerical oracle. -/
instance thetaUpperMatrixRefines_decidable
    (target source : ThetaIntervalMatrix) :
    Decidable (ThetaUpperMatrixRefines target source) := by
  unfold ThetaUpperMatrixRefines
  infer_instance

def thetaUpperMatrixRefinesCheck
    (target source : ThetaIntervalMatrix) : Bool :=
  decide (ThetaUpperMatrixRefines target source)

theorem thetaUpperMatrixRefinesCheck_sound
    (target source : ThetaIntervalMatrix)
    (h : thetaUpperMatrixRefinesCheck target source = true) :
    ThetaUpperMatrixRefines target source := by
  exact of_decide_eq_true h

/-- Rational interval containment is transitive when interpreted
on the genuine REAL theta coefficient. The source may have
negative endpoints; no sign or width hypothesis is needed. -/
theorem thetaUpperMatrixRefines_containsReal
    (target source : ThetaIntervalMatrix)
    (hfit : ThetaUpperMatrixRefines target source)
    (x : ℝ) (i j : Fin 5) (hij : i ≤ j)
    (hs : QInterval.ContainsReal (source i j) x) :
    QInterval.ContainsReal (target i j) x := by
  obtain ⟨hlo, hhi⟩ := hfit i j hij
  have hloR : ((target i j).lo : ℝ) ≤
      ((source i j).lo : ℝ) := by exact_mod_cast hlo
  have hhiR : ((source i j).hi : ℝ) ≤
      ((target i j).hi : ℝ) := by exact_mod_cast hhi
  exact ⟨hloR.trans hs.1, hs.2.trans hhiR⟩

/-- Reject length mismatches, then check every target/source
matrix pair using just 15 rational comparisons per cell. -/
def thetaUpperMatrixRefinementsCheck :
    List ThetaIntervalMatrix → List ThetaIntervalMatrix → Bool
  | [], [] => true
  | target :: targets, source :: sources =>
      thetaUpperMatrixRefinesCheck target source &&
        thetaUpperMatrixRefinementsCheck targets sources
  | _, _ => false

/-- A completely generic analytic transfer: if a constructed
matrix family really encloses thetaCoefficient, and all generated
intervals fit inside the desired audited intervals, then the
audited family itself genuinely encloses thetaCoefficient.

This induction handles all 51 cells at once, without any fresh
LDL, integral, derivative, or interval polynomial proof. -/
theorem thetaCellMatricesEnclose_of_refinements
    (a : ℚ) (bs : List ℚ)
    (targets sources : List ThetaIntervalMatrix)
    (hsource : ThetaCellMatricesEnclose a bs sources)
    (hfit : thetaUpperMatrixRefinementsCheck targets sources = true) :
    ThetaCellMatricesEnclose a bs targets := by
  induction bs generalizing a targets sources with
  | nil =>
      cases sources with
      | nil =>
          cases targets with
          | nil => trivial
          | cons T Ts =>
              simp [thetaUpperMatrixRefinementsCheck] at hfit
      | cons C Cs =>
          simp [ThetaCellMatricesEnclose] at hsource
  | cons b bs ih =>
      cases sources with
      | nil =>
          simp [ThetaCellMatricesEnclose] at hsource
      | cons C Cs =>
          cases targets with
          | nil =>
              simp [thetaUpperMatrixRefinementsCheck] at hfit
          | cons T Ts =>
              have hs :
                  (∀ x : ℝ, 0 < x →
                    (a : ℝ) ≤ x → x ≤ (b : ℝ) →
                      ∀ i j : Fin 5, i ≤ j →
                        QInterval.ContainsReal (C i j)
                          (thetaCoefficient x i j)) ∧
                  ThetaCellMatricesEnclose b bs Cs := by
                simpa only [ThetaCellMatricesEnclose] using hsource
              have hf :
                  thetaUpperMatrixRefinesCheck T C = true ∧
                  thetaUpperMatrixRefinementsCheck Ts Cs = true := by
                simpa only [thetaUpperMatrixRefinementsCheck,
                  Bool.and_eq_true] using hfit
              change
                (∀ x : ℝ, 0 < x →
                  (a : ℝ) ≤ x → x ≤ (b : ℝ) →
                    ∀ i j : Fin 5, i ≤ j →
                      QInterval.ContainsReal (T i j)
                        (thetaCoefficient x i j)) ∧
                ThetaCellMatricesEnclose b bs Ts
              refine ⟨?_, ih b Ts Cs hs.2 hf.2⟩
              intro x hx hax hxb i j hij
              exact thetaUpperMatrixRefines_containsReal T C
                (thetaUpperMatrixRefinesCheck_sound T C hf.1)
                (thetaCoefficient x i j) i j hij
                (hs.1 x hx hax hxb i j hij)

/-- THE important numerical shortcut. The imported 255 checked
rational LDL pivot signs are reused wholesale. A new generator
only needs:
  (1) genuine real theta enclosures on the prescribed cells;
  (2) exact rational containment in the 51 audited 768-bit boxes.

No other new finite pivot theorem is necessary. This still proves
only analyticMatrixPositive, not W5.MainClaim. -/
theorem analyticMatrixPositive_of_audited_refinement
    (sources : List ThetaIntervalMatrix)
    (hsource : ThetaCellMatricesEnclose 0 endpoints sources)
    (hfit : thetaUpperMatrixRefinementsCheck
      thetaAuditUpperCellMatrices sources = true) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_audited_768bit_enclosures
  exact thetaCellMatricesEnclose_of_refinements
    0 endpoints thetaAuditUpperCellMatrices sources
    hsource hfit

end W5
