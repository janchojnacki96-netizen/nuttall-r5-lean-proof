import W5.ThetaGammaUniformMarkovTail
import W5.ThetaAuditedMomentGammaCubicUpper

/-!
# ONE genuine infinite tail bound for all original theta weighted Gamma moments

The preceding universal Markov inequality is pointwise. Here we
integrate it rigorously on [H,∞) using ALREADY EXISTING Mathlib:
  * integrability of the original weighted theta Γ integrand;
  * two exact exponential Γ moment identities = factorial;
  * integral_mono_ae on the restricted half-line;
  * setIntegral_mono_set for the nonnegative comparison function.

The resulting bound is exact:
  tail_k(x,H) ≤ ((k+m)! + x²/4 · (k+m+1)!)/H^m
for every 0≤x≤1, H>0 and k,m natural. It is UNIFORM over the
entire theta x-range (x/n≤1) and every w-bin partition.

No new gamma function, infinite-series summation, or 48 cases.
-/

namespace W5
open MeasureTheory

/-- The true original theta weighted Gamma INTEGRAL from H to ∞
is dominated by an exact factorial-ratio Markov expression.
All integrability conditions are proved, not assumed. -/
theorem thetaGammaUniformTail_integral_markov
    (x H : ℝ) (k m : ℕ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hH : 0 < H) :
    (∫ w in Set.Ici H,
      (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k
      ∂volume) ≤
    ((Nat.factorial (k+m) : ℝ) +
      (x^2/4) * (Nat.factorial (k+m+1) : ℝ)) / H^m := by
  let F : ℝ → ℝ := fun w =>
    (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k
  let S : ℝ → ℝ := fun w =>
    w^(k+m) * Real.exp (-w) +
      (x^2/4) * (w^(k+m+1) * Real.exp (-w))
  let G : ℝ → ℝ := fun w => S w * (H^m)⁻¹
  have hsubset : Set.Ici H ⊆ Set.Ici (0:ℝ) := by
    intro w hw
    exact hH.le.trans hw
  have hF0 : IntegrableOn F (Set.Ici (0:ℝ)) volume :=
    thetaAuditedOneWeightedMoment_integrable_nonneg x hx hx1 k
  have hF : IntegrableOn F (Set.Ici H) volume :=
    hF0.mono_set hsubset
  have hΓ0 : IntegrableOn
      (fun w : ℝ => w^(k+m) * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+m))
  have hΓ1 : IntegrableOn
      (fun w : ℝ => w^(k+m+1) * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+m+1))
  have hS : IntegrableOn S (Set.Ici (0:ℝ)) volume :=
    hΓ0.add (hΓ1.const_mul (x^2/4))
  have hG0 : IntegrableOn G (Set.Ici (0:ℝ)) volume :=
    hS.mul_const ((H^m)⁻¹)
  have hG : IntegrableOn G (Set.Ici H) volume :=
    hG0.mono_set hsubset
  have hpoint : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici H)), F w ≤ G w := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hmk := thetaGammaTailMarkov_pointwise
      (x^2) H w k m (sq_nonneg x) hH hw
    have hrearrange : (1+x^2*w)^((1:ℝ)/4) =
        (1+w*x^2)^((1:ℝ)/4) := by
      congr 1
      ring
    rw [hrearrange] at hmk
    calc
      F w = (Real.exp (-w) * w^k) *
          (1+w*x^2)^((1:ℝ)/4) := by
            dsimp [F]
            ring
      _ ≤ (Real.exp (-w) * w^(k+m) *
          (1+x^2*w/4)) / H^m := hmk
      _ = G w := by
            dsimp [G, S]
            rw [pow_succ]
            ring
  have hFirst : (∫ w in Set.Ici H, F w ∂volume) ≤
      (∫ w in Set.Ici H, G w ∂volume) :=
    integral_mono_ae hF hG hpoint
  have hGnonneg : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici (0:ℝ))), 0 ≤ G w := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hw0 : 0 ≤ w := hw
    have h0 : 0 ≤ w^(k+m) * Real.exp (-w) :=
      mul_nonneg (pow_nonneg hw0 _) (Real.exp_nonneg _)
    have h1 : 0 ≤ w^(k+m+1) * Real.exp (-w) :=
      mul_nonneg (pow_nonneg hw0 _) (Real.exp_nonneg _)
    have hcoeff : 0 ≤ x^2/4 := by positivity
    have hinv : 0 ≤ (H^m)⁻¹ :=
      inv_nonneg.mpr (pow_nonneg hH.le m)
    change 0 ≤ (w^(k+m) * Real.exp (-w) +
      (x^2/4) * (w^(k+m+1) * Real.exp (-w))) * (H^m)⁻¹
    exact mul_nonneg (add_nonneg h0 (mul_nonneg hcoeff h1)) hinv
  have hSet : (∫ w in Set.Ici H, G w ∂volume) ≤
      (∫ w in Set.Ici (0:ℝ), G w ∂volume) :=
    setIntegral_mono_set hG0 hGnonneg hsubset.eventuallySubset
  have hΓ0eval :
      (∫ w in Set.Ici (0:ℝ),
        w^(k+m) * Real.exp (-w) ∂volume) =
          (Nat.factorial (k+m) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+m)
  have hΓ1eval :
      (∫ w in Set.Ici (0:ℝ),
        w^(k+m+1) * Real.exp (-w) ∂volume) =
          (Nat.factorial (k+m+1) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+m+1)
  have hGIntegral :
      (∫ w in Set.Ici (0:ℝ), G w ∂volume) =
        ((Nat.factorial (k+m) : ℝ) +
           (x^2/4) * (Nat.factorial (k+m+1) : ℝ)) / H^m := by
    calc
      (∫ w in Set.Ici (0:ℝ), G w ∂volume) =
          (∫ w in Set.Ici (0:ℝ), S w ∂volume) * (H^m)⁻¹ := by
            dsimp [G]
            rw [integral_mul_const]
      _ = ((∫ w in Set.Ici (0:ℝ),
            w^(k+m) * Real.exp (-w) ∂volume) +
            (x^2/4) * (∫ w in Set.Ici (0:ℝ),
              w^(k+m+1) * Real.exp (-w) ∂volume)) * (H^m)⁻¹ := by
            dsimp [S]
            rw [integral_add hΓ0 (hΓ1.const_mul (x^2/4)),
              integral_const_mul]
      _ = ((Nat.factorial (k+m) : ℝ) +
          (x^2/4) * (Nat.factorial (k+m+1) : ℝ)) / H^m := by
            rw [hΓ0eval, hΓ1eval]
            ring
  calc
    (∫ w in Set.Ici H,
      (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k ∂volume) =
        (∫ w in Set.Ici H, F w ∂volume) := rfl
    _ ≤ (∫ w in Set.Ici H, G w ∂volume) := hFirst
    _ ≤ (∫ w in Set.Ici (0:ℝ), G w ∂volume) := hSet
    _ = _ := hGIntegral

end W5
