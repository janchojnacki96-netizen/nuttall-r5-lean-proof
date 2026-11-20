import W5.ThetaAllBaseCoefficientsSummability

/-!
# Generic splitting of ALL 25 original theta coefficient series

PR #82 proved the elementary Gaussian base series summable for every
i,j : Fin 5. Therefore the *only* remaining summability hypothesis
needed to split any original coefficient into two infinite sums is
summability of the genuine integral correction for that entry.

Using Mathlib's proven HasSum.sub and a single Matrix.ext, we
replace 25 independent coefficient splitting proofs by ONE exact
generic matrix statement. No Fubini or termwise differentiation
is invoked here. The remaining integral-correction summability
hypothesis is explicitly visible, never asserted as a fact.

The numerical theta matrix is not identified with normalizedKernel,
nor are determinant signs claimed.
-/

namespace W5

/-- Once the correction series for a single (i,j) entry is
summable, the ORIGINAL theta coefficient can be rigorously
split into two independently convergent sums. The base
summability requires no extra hypothesis beyond 0<x. -/
theorem thetaCoefficient_all_eq_base_sub_correction
    (x : ℝ) (hx : 0 < x) (i j : Fin 5)
    (hc : Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x i j n)) :
    thetaCoefficient x i j =
      (∑' n : ℕ, thetaCertificateBaseTerm x i j n) -
      (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n) := by
  have hb := thetaCertificateBaseTerm_all_summable x hx i j
  calc
    thetaCoefficient x i j =
        ∑' n : ℕ,
          (thetaCertificateBaseTerm x i j n -
            thetaCertificateCorrectionTerm x i j n) :=
      thetaCoefficient_eq_tsum_base_sub_correction x i j
    _ = (∑' n : ℕ, thetaCertificateBaseTerm x i j n) -
        (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n) :=
      (hb.hasSum.sub hc.hasSum).tsum_eq

/-- The full 5x5 numerical certificate matrix decomposition
is ONE consequence of the 25 correction-summability facts.
No additional hypotheses about any of the elementary Gaussian
base series are needed because PR #82 proves them uniformly
for all 25 entries. -/
theorem thetaMatrixFive_eq_base_sub_correction
    (x : ℝ) (hx : 0 < x)
    (hc : ∀ (i j : Fin 5),
      Summable (fun n : ℕ =>
        thetaCertificateCorrectionTerm x i j n)) :
    Matrix.of (fun i j : Fin 5 => thetaCoefficient x i j) =
      Matrix.of (fun i j : Fin 5 =>
        (∑' n : ℕ, thetaCertificateBaseTerm x i j n) -
        (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n)) := by
  ext i j
  exact thetaCoefficient_all_eq_base_sub_correction x hx i j (hc i j)

end W5
