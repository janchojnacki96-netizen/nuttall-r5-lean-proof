import W5.ThetaAllMixedWeightedJetRecurrence
import W5.ThetaMixedJetSeparableEnvelope

/-!
One separable envelope for all mixed weighted derivatives. Keeping a
fixed right-order cap k avoids a different envelope for j-1 in the
neighbor recurrence. Each left derivative costs one polynomial power
and a factor k+1, retaining the already proved Gaussian decay.
-/

namespace W5
open MeasureTheory

noncomputable def thetaAllMixedJetIndexFactor
    (i k : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  ((k:ℝ)+1)^i * thetaHigherJetIndexFactor (i+k) x n

theorem thetaAllMixedJetIndexFactor_summable
    (i k : ℕ) (x : ℝ) :
    Summable (thetaAllMixedJetIndexFactor i k x) :=
  (thetaHigherJetIndexFactor_summable (i+k) x).mul_left _

theorem thetaHigherJetIndexFactor_mono_order
    (j k : ℕ) (x : ℝ) (n : ℕ) (hx : 0 < x) (hjk : j ≤ k) :
    thetaHigherJetIndexFactor j x n ≤ thetaHigherJetIndexFactor k x n := by
  have hC : 1 ≤ 1/x+2 := by
    have h : 0 ≤ 1/x := by positivity
    linarith
  have hp : (1:ℝ) ≤ (n:ℝ)^2+1 := by nlinarith [sq_nonneg (n:ℝ)]
  have h1 := pow_le_pow_right₀ hC hjk
  have h2 := pow_le_pow_right₀ hp (show j+1 ≤ k+1 by omega)
  unfold thetaHigherJetIndexFactor
  gcongr

theorem thetaHigherJetTailFactor_mono_order
    (j k : ℕ) (w : ℝ) (hw : 0 ≤ w) (hjk : j ≤ k) :
    thetaHigherJetTailFactor j w ≤ thetaHigherJetTailFactor k w := by
  have h : 1 ≤ w+1 := by linarith
  have hpow := pow_le_pow_right₀ h hjk
  unfold thetaHigherJetTailFactor
  gcongr

theorem thetaAllMixedJetTerm_zero_index
    (x u v w : ℝ) (i j : ℕ) :
    thetaAllMixedJetTerm x u v 0 w i j = 0 := by
  induction i generalizing j with
  | zero => simp [thetaAllMixedJetTerm, thetaHigherRightJetSeriesTerm]
  | succ i ih => simp only [thetaAllMixedJetTerm, ih, mul_zero, add_zero]

theorem thetaAllMixedJetTerm_norm_le_cap
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) (hw : 0 ≤ w) :
    ∀ (i j : ℕ), j ≤ k →
    ‖thetaAllMixedJetTerm x u v n w i j‖ ≤
      thetaAllMixedJetIndexFactor i k x n *
        thetaHigherJetTailFactor (i+k) w := by
  let C : ℝ := 1/x+2
  let P : ℝ := (n:ℝ)^2+1
  let T : ℝ := w+1
  have hC : 1 ≤ C := by
    have h : 0 ≤ 1/x := by positivity
    dsimp [C]
    linarith
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  intro i
  induction i with
  | zero =>
      intro j hj
      have hb := thetaHigherRightJetSeriesTerm_norm_le j x u v n w hx hx1 hu hv hw
      have hI := thetaHigherJetIndexFactor_mono_order j k x n hx hj
      have hW := thetaHigherJetTailFactor_mono_order j k w hw hj
      have hIn : 0 ≤ thetaHigherJetIndexFactor k x n := by
        unfold thetaHigherJetIndexFactor
        positivity
      have hWn : 0 ≤ thetaHigherJetTailFactor j w := by
        unfold thetaHigherJetTailFactor
        positivity
      simpa only [thetaAllMixedJetTerm, thetaAllMixedJetIndexFactor,
        pow_zero, one_mul, Nat.zero_add] using
        hb.trans (mul_le_mul hI hW hWn hIn)
  | succ i ih =>
      intro j hj
      have hB : 0 ≤ thetaAllMixedJetIndexFactor i k x n *
          thetaHigherJetTailFactor (i+k) w := by
        unfold thetaAllMixedJetIndexFactor thetaHigherJetIndexFactor thetaHigherJetTailFactor
        positivity
      have hnext : 0 ≤ thetaAllMixedJetIndexFactor (i+1) k x n *
          thetaHigherJetTailFactor (i+1+k) w := by
        unfold thetaAllMixedJetIndexFactor thetaHigherJetIndexFactor thetaHigherJetTailFactor
        positivity
      by_cases hn : n = 0
      · rw [hn, thetaAllMixedJetTerm_zero_index, norm_zero]
        simpa only [hn] using hnext
      let B := thetaAllMixedJetIndexFactor i k x n *
          thetaHigherJetTailFactor (i+k) w
      have hBn : 0 ≤ B := hB
      have hprev : |thetaAllMixedJetTerm x u v n w i (j-1)| ≤ B := by
        simpa only [Real.norm_eq_abs, B] using ih (j-1) (by omega)
      have hnow : |thetaAllMixedJetTerm x u v n w i j| ≤ B := by
        simpa only [Real.norm_eq_abs, B] using ih j hj
      have hcoef := thetaAllMixedJetTerm_coefficients_bound x v n w hx hx1 hv hw hn
      have hq : |(n:ℝ)^2+w*x^2| ≤ P*T := hcoef.1
      have hm : |thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) v w| ≤ C*(P*T) := hcoef.2
      have hjR : (j:ℝ) ≤ (k:ℝ) := by exact_mod_cast hj
      have hfirst : (j:ℝ)*|(n:ℝ)^2+w*x^2| *
          |thetaAllMixedJetTerm x u v n w i (j-1)| ≤ (k:ℝ)*(P*T)*B := by
        have h0 : (j:ℝ)*|(n:ℝ)^2+w*x^2| ≤ (k:ℝ)*(P*T) :=
          mul_le_mul hjR hq (abs_nonneg _) (Nat.cast_nonneg k)
        exact mul_le_mul h0 hprev (abs_nonneg _) (by positivity)
      have hsecond : |thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) v w| *
          |thetaAllMixedJetTerm x u v n w i j| ≤ C*(P*T)*B :=
        mul_le_mul hm hnow (abs_nonneg _) (by positivity)
      have hshift : ((k:ℝ)+1)*C*(P*T)*B =
          thetaAllMixedJetIndexFactor (i+1) k x n *
            thetaHigherJetTailFactor (i+1+k) w := by
        dsimp [B, C, P, T, thetaAllMixedJetIndexFactor,
          thetaHigherJetIndexFactor, thetaHigherJetTailFactor]
        rw [show i+1+k = (i+k)+1 by omega]
        simp only [pow_succ]
        ring
      change ‖(j:ℝ) * (-((n:ℝ)^2+w*x^2)) *
          thetaAllMixedJetTerm x u v n w i (j-1) +
        thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) v w *
          thetaAllMixedJetTerm x u v n w i j‖ ≤ _
      calc
        _ ≤ ‖(j:ℝ) * (-((n:ℝ)^2+w*x^2)) *
            thetaAllMixedJetTerm x u v n w i (j-1)‖ +
          ‖thetaWeightedGaussianRightMultiplier x ((n:ℝ)^2)
            (((n:ℝ)^2-1)/x) v w *
            thetaAllMixedJetTerm x u v n w i j‖ := norm_add_le _ _
        _ ≤ (k:ℝ)*(P*T)*B + C*(P*T)*B := by
          simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (Nat.cast_nonneg j)]
          exact add_le_add hfirst hsecond
        _ ≤ ((k:ℝ)+1)*C*(P*T)*B := by
          have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg k
          have hkc : (k:ℝ) ≤ (k:ℝ)*C := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hC hk
          have hh := mul_le_mul_of_nonneg_right (add_le_add_right hkc C)
            (mul_nonneg (mul_nonneg hP hT) hBn)
          calc
            _ = ((k:ℝ)+C)*((P*T)*B) := by ring
            _ ≤ ((k:ℝ)*C+C)*((P*T)*B) := hh
            _ = _ := by ring
        _ = _ := hshift

theorem thetaAllMixedJetTerm_norm_le_separable
    (i j : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) (hw : 0 ≤ w) :
    ‖thetaAllMixedJetTerm x u v n w i j‖ ≤
      thetaAllMixedJetIndexFactor i j x n * thetaHigherJetTailFactor (i+j) w :=
  thetaAllMixedJetTerm_norm_le_cap j x u v n w hx hx1 hu hv hw i j le_rfl

end W5
