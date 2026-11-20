import W5.ThetaMathlibLocalTwoVariableDerivative

/-!
# Concrete summable envelopes for actual theta jets in two parameters

Mathlib's LOCAL two-parameter FDeriv-of-tsum theorem (PR #78)
requires an indexwise summable majorant uniform on its local
parameter domain. Previously, the sharp Gaussian/exponential
majorants were proved for theta jets in scalar u and v variables.

Here we transport the already verified estimates to the genuine
two-variable parameter space Fin 2 → ℝ, *without introducing
any unknown constants or bounding assumptions*.

We prove:
* a single explicitly summable index majorant for every right
  derivative order k;
* a uniform bound for the true Lebesgue integral of each
  weighted kth right Gaussian jet;
* the same bound for every kth left jet by exact Gaussian symmetry;
* summability of the original integrated theta series throughout
  the local closed parameter box, not just at its origin;
* a single summable uniform bound on the *sum of norms* of both
  first-coordinate jet integrals.

It remains to prove that the actual two-dimensional FDeriv
of each integrated term is given by these component jets,
and to upgrade this first-order estimate to mixed FDerivs
through total order eight.
-/

namespace W5
open MeasureTheory

/-- A single n-dependent majorant for the actual integrated
kth Gaussian right jet, independent of both Taylor parameters
on the local x/8 rectangle. -/
noncomputable def thetaTwoVariableIntegratedJetMajorant
    (k : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  thetaHigherJetIndexFactor k x n *
    (∫ w : ℝ, thetaHigherJetTailFactor k w
      ∂(volume.restrict (Set.Ioi (0:ℝ))))

/-- This true n-majorant is summable for every fixed jet order.
The proof imports the existing polynomial-Gaussian decay estimate. -/
theorem thetaTwoVariableIntegratedJetMajorant_summable
    (k : ℕ) (x : ℝ) :
    Summable (thetaTwoVariableIntegratedJetMajorant k x) := by
  change Summable (fun n : ℕ =>
    thetaHigherJetIndexFactor k x n *
      (∫ w : ℝ, thetaHigherJetTailFactor k w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))))
  exact (thetaHigherJetIndexFactor_summable k x).mul_right _

/-- The actual full weighted kth right jet integral is bounded
for EVERY two-variable parameter z in the same x/8 box. -/
theorem thetaTwoVariable_right_jet_integral_norm_le
    (k : ℕ) (x : ℝ) (z : Fin 2 → ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hz0 : |z 0| ≤ x/8) (hz1 : |z 1| ≤ x/8) :
    ‖∫ w : ℝ,
      thetaHigherRightJetSeriesTerm k x (z 0) (z 1) n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
      thetaTwoVariableIntegratedJetMajorant k x n := by
  exact thetaHigherRightJetSeriesTerm_integral_norm_le
    k x (z 0) (z 1) n hx hx1 hz0 hz1

/-- By exact Gaussian symmetry, the same uniform bound holds
for the true kth LEFT jet integral (no new majorant needed). -/
theorem thetaTwoVariable_left_jet_integral_norm_le
    (k : ℕ) (x : ℝ) (z : Fin 2 → ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hz0 : |z 0| ≤ x/8) (hz1 : |z 1| ≤ x/8) :
    ‖∫ w : ℝ,
      thetaHigherLeftJetSeriesTerm k x (z 0) (z 1) n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
      thetaTwoVariableIntegratedJetMajorant k x n := by
  change
    ‖∫ w : ℝ,
      thetaHigherRightJetSeriesTerm k x (z 1) (z 0) n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
      thetaTwoVariableIntegratedJetMajorant k x n
  exact thetaTwoVariable_right_jet_integral_norm_le
    k x (fun i : Fin 2 => if i = 0 then z 1 else z 0) n
    hx hx1 (by simpa) (by simpa)

/-- Unlike a conditional summability statement, this bounds
the ACTUAL original integrated theta summand in both variables,
using the previously proved zeroth-jet integral equality. -/
theorem thetaTwoVariable_actual_term_norm_le
    (x : ℝ) (z : Fin 2 → ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hz0 : |z 0| ≤ x/8) (hz1 : |z 1| ≤ x/8) :
    ‖thetaIntegratedSeriesTermTwoVariable x n z‖ ≤
      thetaTwoVariableIntegratedJetMajorant 0 x n := by
  change ‖thetaGaussianIntegratedSeriesTerm x (z 0) n (z 1)‖ ≤ _
  rw [thetaGaussianIntegratedSeriesTerm_eq_jet_zero_integral
    x (z 0) (z 1) n]
  exact thetaTwoVariable_right_jet_integral_norm_le
    0 x z n hx hx1 hz0 hz1

/-- The actual transformed integrated theta series is absolutely
summable at ALL points of the local two-variable rectangle. -/
theorem thetaTwoVariable_actual_series_summable_on_box
    (x : ℝ) (z : Fin 2 → ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hz0 : |z 0| ≤ x/8) (hz1 : |z 1| ≤ x/8) :
    Summable (fun n : ℕ =>
      thetaIntegratedSeriesTermTwoVariable x n z) := by
  exact (thetaTwoVariableIntegratedJetMajorant_summable 0 x).of_norm_bounded
    (fun n => thetaTwoVariable_actual_term_norm_le
      x z n hx hx1 hz0 hz1)

/-- Both first-coordinate Gaussian jet integral norms are
uniformly controlled by the SAME summable sequence. This is
the precise input needed when constructing and bounding
the Fréchet derivative as the two coordinate components. -/
theorem thetaTwoVariable_both_first_jet_integral_norms_le
    (x : ℝ) (z : Fin 2 → ℝ) (n : ℕ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hz0 : |z 0| ≤ x/8) (hz1 : |z 1| ≤ x/8) :
    ‖∫ w : ℝ,
      thetaHigherLeftJetSeriesTerm 1 x (z 0) (z 1) n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ +
    ‖∫ w : ℝ,
      thetaHigherRightJetSeriesTerm 1 x (z 0) (z 1) n w
        ∂(volume.restrict (Set.Ioi (0:ℝ)))‖ ≤
    2 * thetaTwoVariableIntegratedJetMajorant 1 x n := by
  have hleft := thetaTwoVariable_left_jet_integral_norm_le
    1 x z n hx hx1 hz0 hz1
  have hright := thetaTwoVariable_right_jet_integral_norm_le
    1 x z n hx hx1 hz0 hz1
  linarith

/-- Even the JOINT first-coordinate majorant remains summable. -/
theorem thetaTwoVariable_both_first_jet_majorant_summable
    (x : ℝ) :
    Summable (fun n : ℕ =>
      2 * thetaTwoVariableIntegratedJetMajorant 1 x n) :=
  (thetaTwoVariableIntegratedJetMajorant_summable 1 x).mul_left 2

end W5
