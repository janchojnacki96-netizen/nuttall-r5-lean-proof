import W5.ThetaLeadingTwoActualJetMatrixBridge
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Reusing Mathlib's ALL-ORDERS multidimensional smooth-series theorem

The target Nuttall W5 matrix uses the ordinary mixed derivatives
of the transformed theta series to TOTAL order 8. Currently the
project derives these derivatives via several successive 1D lemmas.

Mathlib's `iteratedFDeriv_tsum_apply` handles *all* Fréchet
derivatives of the sum, in both parameters simultaneously,
once one proves ContDiff and a summable bound on the norm of
each iterated Fréchet derivative.

We specialize that library theorem to E = (Fin 2 → ℝ),
the two Taylor parameters (u,v), and derivative orders k ≤ 8.

IMPORTANT: Mathlib's theorem requires UNIFORM GLOBAL bounds in
the parameter space, while our existing Gaussian bounds hold
only in |u|,|v| ≤ x/8. For actual theta applications we will
need a smooth cutoff preserving the function in a neighborhood
of the Taylor origin, or a suitable local version of Mathlib's
smooth-series argument. These hypotheses are NOT asserted or
proved for the original theta series here.

This adapter is an honest conditional mathlib theorem; it gives
a reusable precise set of obligations rather than 15 independently
admitted derivative/sum interchanges.
-/

namespace W5

/-- Exactly the original integrated theta summand, now viewed as a
function on the TWO-variable Euclidean parameter space. -/
noncomputable def thetaIntegratedSeriesTermTwoVariable
    (x : ℝ) (n : ℕ) (z : Fin 2 → ℝ) : ℝ :=
  thetaGaussianIntegratedSeriesTerm x (z 0) n (z 1)

/-- The elementary gaussian model is genuinely smooth
simultaneously in BOTH Taylor coordinates. -/
theorem thetaGaussianModel_twoVariable_contDiff
    (d q : ℝ) :
    ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaGaussianModel d q (z 0) (z 1)) := by
  unfold thetaGaussianModel
  fun_prop

/-- Mathlib gives the full derivative of a SUM as the sum of
full derivatives, at EVERY order up to 8, from one uniform
summable envelope of the Fréchet derivatives. This covers
mixed derivatives after contraction to coordinate directions.

No assumption is hidden: `hsmooth`, `hsummable` and `hbound`
must all be established for a suitable cutoff of the actual
theta terms before using this theorem to prove Nuttall. -/
theorem thetaTwoVariable_iteratedFDeriv_tsum_eight
    (f : ℕ → (Fin 2 → ℝ) → ℝ)
    (majorant : ℕ → ℕ → ℝ)
    (hsmooth : ∀ n : ℕ, ContDiff ℝ (8 : ℕ∞) (f n))
    (hsummable :
      ∀ k : ℕ, (k : ℕ∞) ≤ (8 : ℕ∞) → Summable (majorant k))
    (hbound :
      ∀ (k n : ℕ) (z : Fin 2 → ℝ),
        (k : ℕ∞) ≤ (8 : ℕ∞) →
        ‖iteratedFDeriv ℝ k (f n) z‖ ≤ majorant k n)
    (k : ℕ) (hk : k ≤ 8) (z : Fin 2 → ℝ) :
    iteratedFDeriv ℝ k
        (fun y : Fin 2 → ℝ => ∑' n : ℕ, f n y) z =
      ∑' n : ℕ, iteratedFDeriv ℝ k (f n) z := by
  have hkn : (k : ℕ∞) ≤ (8 : ℕ∞) := by
    exact_mod_cast hk
  exact iteratedFDeriv_tsum_apply hsmooth hsummable hbound hkn z

/-- The SAME bounds also give C^8 regularity of the
infinite TWO-variable theta-like series. Unlike separate
one-dimensional derivatives, this supports mixed derivative
identities once their coordinate contractions are justified. -/
theorem thetaTwoVariable_tsum_contDiff_eight
    (f : ℕ → (Fin 2 → ℝ) → ℝ)
    (majorant : ℕ → ℕ → ℝ)
    (hsmooth : ∀ n : ℕ, ContDiff ℝ (8 : ℕ∞) (f n))
    (hsummable :
      ∀ k : ℕ, (k : ℕ∞) ≤ (8 : ℕ∞) → Summable (majorant k))
    (hbound :
      ∀ (k n : ℕ) (z : Fin 2 → ℝ),
        (k : ℕ∞) ≤ (8 : ℕ∞) →
        ‖iteratedFDeriv ℝ k (f n) z‖ ≤ majorant k n) :
    ContDiff ℝ (8 : ℕ∞)
      (fun y : Fin 2 → ℝ => ∑' n : ℕ, f n y) := by
  exact contDiff_tsum hsmooth hsummable
    (fun k n z hk => hbound k n z hk)

/-- Definitional two-variable equivalence at the origin:
no differentiation or analytic assumption is involved. -/
theorem thetaTwoVariable_series_at_origin (x : ℝ) :
    (∑' n : ℕ,
      thetaIntegratedSeriesTermTwoVariable x n (fun _ => 0)) =
    ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0 := by
  rfl

end W5
