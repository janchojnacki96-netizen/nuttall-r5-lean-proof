import W5.Theta51CellRealCertificateReduction
import W5.ThetaCoefficientSymmetry

/-!
# Certify only the 15 independent entries of the actual theta matrix

The original `thetaCoefficient` is ALREADY proved symmetric
(`thetaCoefficient_symmetric`), including its full theta integral.
Thus a symmetric rational interval matrix needs enclosures for
only 15 of the 25 entries of the 5×5 matrix.

This is useful when importing the exact integer interval certificate:
the existing C++ and Python computations store only one triangle.
The actual five-pivot checker is unchanged; all arithmetic and
determinant proofs are reused, including Mathlib's Schur formula.

Here we prove that any uniformly valid upper-triangle enclosure on
each of the existing 51 rational x-cells is sufficient for
`analyticMatrixPositive`. The concrete upper-triangle numerical
enclosures still have to be verified; no theta bounds are invented.
-/

namespace W5

/-- Fill the lower triangle by reflection. No property of C
(in particular no symmetry) is assumed. -/
def thetaSymmetricIntervals
    (C : Matrix (Fin 5) (Fin 5) QInterval) :
    Matrix (Fin 5) (Fin 5) QInterval :=
  Matrix.of (fun i j => if i ≤ j then C i j else C j i)

/-- The symmetric completion agrees with C above the diagonal. -/
theorem thetaSymmetricIntervals_upper
    (C : Matrix (Fin 5) (Fin 5) QInterval)
    (i j : Fin 5) (hij : i ≤ j) :
    thetaSymmetricIntervals C i j = C i j := by
  simp [thetaSymmetricIntervals, hij]

/-- Symmetric completion, by construction, for ANY input intervals. -/
theorem thetaSymmetricIntervals_symmetric
    (C : Matrix (Fin 5) (Fin 5) QInterval)
    (i j : Fin 5) :
    thetaSymmetricIntervals C i j =
      thetaSymmetricIntervals C j i := by
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have heq : i = j := le_antisymm hij hji
      subst j
      rfl
    · simp [thetaSymmetricIntervals, hij, hji]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simp [thetaSymmetricIntervals, hij, hji]

/-- 15 upper-triangle bounds on the genuine theta series provide
ALL 25 bounds on the completed symmetric rational interval matrix. -/
theorem thetaSymmetricIntervals_contains_theta
    (C : Matrix (Fin 5) (Fin 5) QInterval)
    (x : ℝ)
    (hupper : ∀ i j : Fin 5, i ≤ j →
      QInterval.ContainsReal (C i j) (thetaCoefficient x i j))
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaSymmetricIntervals C i j)
      (thetaCoefficient x i j) := by
  by_cases hij : i ≤ j
  · rw [thetaSymmetricIntervals_upper C i j hij]
    exact hupper i j hij
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    rw [thetaSymmetricIntervals_symmetric C i j]
    rw [thetaSymmetricIntervals_upper C j i hji]
    rw [thetaCoefficient_symmetric x i j]
    exact hupper j i hji

/-- One compact certified x-cell: only its 15 upper-triangle
entries need to be enclosed, but all five LDL tests are performed
on the same symmetric 5×5 interval matrix. -/
def ThetaUpperRealCellCertificate (a b : ℚ) : Prop :=
  ∃ C : Matrix (Fin 5) (Fin 5) QInterval,
    intervalLDL5Alternating (thetaSymmetricIntervals C) ∧
      ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          QInterval.ContainsReal (C i j) (thetaCoefficient x i j)

/-- The compact 15-entry cell implies the full 25-entry certificate
required by the established verified interval LDL proof. -/
theorem thetaRealCellCertificate_of_upper
    (a b : ℚ)
    (h : ThetaUpperRealCellCertificate a b) :
    ThetaRealCellCertificate a b := by
  rcases h with ⟨C, hchecks, hupper⟩
  refine ⟨thetaSymmetricIntervals C, hchecks, ?_⟩
  intro x hx ha hb i j
  exact thetaSymmetricIntervals_contains_theta C x
    (fun k l hkl => hupper x hx ha hb k l hkl) i j

/-- The exact endpoint chain from `FiniteCore`, with one
15-entry certificate per interval. -/
def ThetaUpperRealCellCertificateChain (a : ℚ) : List ℚ → Prop
  | [] => True
  | b :: bs =>
      ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs

/-- Reuse the previous 51-cell theorem without redoing coverage,
rational interval arithmetic, pivot signs or determinant algebra. -/
theorem thetaRealCellCertificateChain_of_upper (bs : List ℚ) :
    ∀ a : ℚ,
      ThetaUpperRealCellCertificateChain a bs →
        ThetaRealCellCertificateChain a bs := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a h
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs at h
      rcases h with ⟨hfirst, hrest⟩
      change ThetaRealCellCertificate a b ∧
        ThetaRealCellCertificateChain b bs
      exact ⟨thetaRealCellCertificate_of_upper a b hfirst,
        ih b hrest⟩

/-- The full ORIGINAL theta leading-minor signs for r=1,...,5
are now reduced to exactly 51 batches of 15 genuine analytic
entry enclosures and 51 verified rational five-pivot tests. -/
theorem analyticMatrixPositive_of_51_upper_cell_certificates
    (hcells : ThetaUpperRealCellCertificateChain 0 endpoints) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_51_real_cell_certificates
    (thetaRealCellCertificateChain_of_upper endpoints 0 hcells)

end W5
