import W5.ThetaGammaExactExpTail
import W5.ThetaAuditedMomentGammaBox

/-!
# Sharp original-theta weighted Gamma tail via EXACT incomplete moments

The previous Markov tail estimate loses substantial precision by
bounding every Gamma moment over the entire half-line.

Instead, use the already proven fourth-root tangent inequality
(1+w*x^2)^(1/4) <= 1+w*x^2/4 and the newly proven exact
incomplete Gamma formulas at H.

This theorem is a REAL inequality for the ACTUAL original theta
moment tail, for arbitrary k>=0, H>=0 and 0<=x<=1, not a
numerical guess. A rational interval for exp(-H) can be attached
without changing any analytic reasoning.
-/

namespace W5
open MeasureTheory

/-- ONE sharp real upper estimate for all original weighted theta
Gamma tails. The RHS is exp(-H) times an explicit polynomial in H,
not a factorial bound divided by H^m. -/
theorem thetaGammaWeightedTail_le_exact_exponential
    (k : ℕ) (x H : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hH : 0 ≤ H) :
    (∫ w in Set.Ici H,
      (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k
      ∂volume) ≤
      Real.exp (-H) *
        (thetaGammaBinPolyR k H +
          (x^2/4) * thetaGammaBinPolyR (k+1) H) := by
  let F : ℝ → ℝ := fun w =>
    (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k
  let G : ℝ → ℝ := fun w =>
    Real.exp (-w)*w^k +
      (x^2/4) * (Real.exp (-w)*w^(k+1))
  have hsubset : Set.Ici H ⊆ Set.Ici (0:ℝ) := by
    intro w hw
    exact hH.trans hw
  have hF0 : IntegrableOn F (Set.Ici (0:ℝ)) volume :=
    thetaAuditedOneWeightedMoment_integrable_nonneg x hx hx1 k
  have hF : IntegrableOn F (Set.Ici H) volume :=
    hF0.mono_set hsubset
  have hGamma0 : IntegrableOn
      (fun w : ℝ => w^k * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable k)
  have hGamma1 : IntegrableOn
      (fun w : ℝ => w^(k+1) * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+1))
  have h0 : IntegrableOn
      (fun w : ℝ => Real.exp (-w)*w^k)
      (Set.Ici H) volume := by
    have heq :
        (fun w : ℝ => Real.exp (-w)*w^k) =
          (fun w : ℝ => w^k*Real.exp (-w)) := by
      funext w
      ring
    rw [heq]
    exact hGamma0.mono_set hsubset
  have h1 : IntegrableOn
      (fun w : ℝ => Real.exp (-w)*w^(k+1))
      (Set.Ici H) volume := by
    have heq :
        (fun w : ℝ => Real.exp (-w)*w^(k+1)) =
          (fun w : ℝ => w^(k+1)*Real.exp (-w)) := by
      funext w
      ring
    rw [heq]
    exact hGamma1.mono_set hsubset
  have hG : IntegrableOn G (Set.Ici H) volume :=
    h0.add (h1.const_mul (x^2/4))
  have hpoint : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici H)), F w ≤ G w := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hw0 : 0 ≤ w := hH.trans hw
    have hroot := thetaFourthRoot_one_add_le_linear
      (w*x^2) (mul_nonneg hw0 (sq_nonneg x))
    have hweight : 0 ≤ Real.exp (-w)*w^k :=
      mul_nonneg (Real.exp_nonneg _) (pow_nonneg hw0 k)
    change (Real.exp (-w)*(1+w*x^2)^((1:ℝ)/4))*w^k ≤
      Real.exp (-w)*w^k +
        (x^2/4)*(Real.exp (-w)*w^(k+1))
    calc
      (Real.exp (-w)*(1+w*x^2)^((1:ℝ)/4))*w^k =
        (Real.exp (-w)*w^k)*(1+w*x^2)^((1:ℝ)/4) := by ring
      _ ≤ (Real.exp (-w)*w^k)*(1+w*x^2/4) :=
        mul_le_mul_of_nonneg_left hroot hweight
      _ = Real.exp (-w)*w^k +
          (x^2/4)*(Real.exp (-w)*w^(k+1)) := by
        rw [pow_succ]
        ring
  have hmon : (∫ w in Set.Ici H, F w ∂volume) ≤
      (∫ w in Set.Ici H, G w ∂volume) :=
    integral_mono_ae hF hG hpoint
  have hGEval :
      (∫ w in Set.Ici H, G w ∂volume) =
        Real.exp (-H)*thetaGammaBinPolyR k H +
          (x^2/4)*(Real.exp (-H)*thetaGammaBinPolyR (k+1) H) := by
    dsimp [G]
    rw [integral_add h0 (h1.const_mul (x^2/4)),
      integral_const_mul,
      thetaGammaExpMoment_tail_exact k H hH,
      thetaGammaExpMoment_tail_exact (k+1) H hH]
  calc
    (∫ w in Set.Ici H,
      (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k
        ∂volume) ≤
      (∫ w in Set.Ici H, G w ∂volume) := hmon
    _ = Real.exp (-H)*thetaGammaBinPolyR k H +
        (x^2/4)*(Real.exp (-H)*thetaGammaBinPolyR (k+1) H) :=
      hGEval
    _ = Real.exp (-H) *
      (thetaGammaBinPolyR k H +
        (x^2/4)*thetaGammaBinPolyR (k+1) H) := by ring

end W5
