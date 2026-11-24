import W5.ThetaAuditedMomentGammaQuadraticLower

/-!
# A reusable cubic Gamma moment upper bound for all theta entries

The second-cell n=1 audit uses nine real weighted Gamma moments.
The previous tangent-line upper bound discards the negative quadratic
term of the fourth-root expansion and is too wide for many entries.

This module proves a GLOBAL cubic upper bound for (1+t)^(1/4),
t>=0, using only the identity r^4=1+t and positive polynomials.
Integrating its four elementary terms reuses the SAME exact Gamma
factorials and integrability lemmas already present in this project.
The theorem holds for arbitrary natural moment index k.
-/

namespace W5
open MeasureTheory

/-- Global third-degree upper Taylor bound for the real fourth root,
valid for all t>=0 (not just a small numerical interval). -/
theorem thetaFourthRoot_one_add_cubic_upper
    (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^((1:ℝ)/4) ≤
      1 + t/4 - 3*t^2/32 + 7*t^3/128 := by
  let r : ℝ := (1+t)^((1:ℝ)/4)
  have hbase : 0 ≤ 1+t := by linarith
  have hr4 : r^4 = 1+t := by
    dsimp [r]
    calc
      ((1+t)^((1:ℝ)/4))^4 =
          ((1+t)^((1:ℝ)/4))^(4:ℝ) := by
            exact (Real.rpow_natCast ((1+t)^((1:ℝ)/4)) 4).symm
      _ = (1+t)^(((1:ℝ)/4)*(4:ℝ)) :=
        (Real.rpow_mul hbase ((1:ℝ)/4) (4:ℝ)).symm
      _ = 1+t := by norm_num
  have hr1 : 1 ≤ r := by
    dsimp [r]
    simpa only [Real.one_rpow] using
      (Real.rpow_le_rpow (show (0:ℝ) ≤ 1 by norm_num)
        (show (1:ℝ) ≤ 1+t by linarith)
        (show (0:ℝ) ≤ 1/4 by norm_num))
  have hr0 : 0 ≤ r := by linarith
  have hm : 0 ≤ r-1 := sub_nonneg.mpr hr1
  have hpositive :
      0 ≤ ((r-1)^4 *
        (7*r^8 + 28*r^7 + 70*r^6 + 140*r^5 +
          212*r^4 + 260*r^3 + 258*r^2 + 180*r + 77))/128 := by
    positivity
  have ht4 : t = r^4 - 1 := by linarith [hr4]
  change r ≤ 1 + t/4 - 3*t^2/32 + 7*t^3/128
  calc
    r ≤ r +
        ((r-1)^4 *
          (7*r^8 + 28*r^7 + 70*r^6 + 140*r^5 +
            212*r^4 + 260*r^3 + 258*r^2 + 180*r + 77))/128 := by
      linarith
    _ = 1 + t/4 - 3*t^2/32 + 7*t^3/128 := by
      rw [ht4]
      ring

/-- One universal analytic UPPER moment estimate, for every k:
the exact third-order fourth-root polynomial integrates into
four existing Mathlib factorial Gamma moments. -/
theorem thetaAuditedOneWeightedMoment_gamma_upper_cubic
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    thetaAuditedOneWeightedMoment x k ≤
      (Nat.factorial k : ℝ) +
        (x^2/4) * (Nat.factorial (k+1) : ℝ) -
        (3*x^4/32) * (Nat.factorial (k+2) : ℝ) +
        (7*x^6/128) * (Nat.factorial (k+3) : ℝ) := by
  have hf : IntegrableOn
      (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k)
      (Set.Ici (0:ℝ)) volume :=
    thetaAuditedOneWeightedMoment_integrable_nonneg x hx hx1 k
  have hΓ0 : IntegrableOn
      (fun w : ℝ => w^k * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable k)
  have hΓ1 : IntegrableOn
      (fun w : ℝ => w^(k+1) * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+1))
  have hΓ2 : IntegrableOn
      (fun w : ℝ => w^(k+2) * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+2))
  have hΓ3 : IntegrableOn
      (fun w : ℝ => w^(k+3) * Real.exp (-w))
      (Set.Ici (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+3))
  have hG : IntegrableOn
      (fun w : ℝ =>
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) +
          (7*x^6/128) * (w^(k+3) * Real.exp (-w)))
      (Set.Ici (0:ℝ)) volume :=
    ((hΓ0.add (hΓ1.const_mul (x^2/4))).sub
      (hΓ2.const_mul (3*x^4/32))).add
      (hΓ3.const_mul (7*x^6/128))
  have hΓ0eval :
      (∫ w in Set.Ici (0:ℝ),
        w^k * Real.exp (-w) ∂volume) =
        (Nat.factorial k : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment k
  have hΓ1eval :
      (∫ w in Set.Ici (0:ℝ),
        w^(k+1) * Real.exp (-w) ∂volume) =
        (Nat.factorial (k+1) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+1)
  have hΓ2eval :
      (∫ w in Set.Ici (0:ℝ),
        w^(k+2) * Real.exp (-w) ∂volume) =
        (Nat.factorial (k+2) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+2)
  have hΓ3eval :
      (∫ w in Set.Ici (0:ℝ),
        w^(k+3) * Real.exp (-w) ∂volume) =
        (Nat.factorial (k+3) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+3)
  have hpoint : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici (0:ℝ))),
        (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k ≤
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) +
          (7*x^6/128) * (w^(k+3) * Real.exp (-w)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hw0 : 0 ≤ w := hw
    have hroot :
        (1+w*x^2)^((1:ℝ)/4) ≤
          1 + (w*x^2)/4 - 3*(w*x^2)^2/32 +
            7*(w*x^2)^3/128 :=
      thetaFourthRoot_one_add_cubic_upper (w*x^2)
        (mul_nonneg hw0 (sq_nonneg x))
    calc
      (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k ≤
          (Real.exp (-w) *
            (1+(w*x^2)/4-3*(w*x^2)^2/32+7*(w*x^2)^3/128)) *
              w^k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot (Real.exp_nonneg _))
          (pow_nonneg hw0 k)
      _ = (w^k * Real.exp (-w) +
            (x^2/4) * (w^(k+1) * Real.exp (-w))) -
            (3*x^4/32) * (w^(k+2) * Real.exp (-w)) +
            (7*x^6/128) * (w^(k+3) * Real.exp (-w)) := by
          simp only [pow_add, pow_one, pow_two, pow_three]
          ring
  have hInt :
      (∫ w in Set.Ici (0:ℝ),
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) +
          (7*x^6/128) * (w^(k+3) * Real.exp (-w)) ∂volume) =
      (∫ w in Set.Ici (0:ℝ),
        w^k * Real.exp (-w) ∂volume) +
        (x^2/4) * (∫ w in Set.Ici (0:ℝ),
          w^(k+1) * Real.exp (-w) ∂volume) -
        (3*x^4/32) * (∫ w in Set.Ici (0:ℝ),
          w^(k+2) * Real.exp (-w) ∂volume) +
        (7*x^6/128) * (∫ w in Set.Ici (0:ℝ),
          w^(k+3) * Real.exp (-w) ∂volume) := by
    calc
      _ =
        (∫ w in Set.Ici (0:ℝ),
          (w^k * Real.exp (-w) +
            (x^2/4) * (w^(k+1) * Real.exp (-w))) -
            (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ∂volume) +
        (∫ w in Set.Ici (0:ℝ),
          (7*x^6/128) * (w^(k+3) * Real.exp (-w)) ∂volume) := by
            simpa only [Pi.add_apply, Pi.sub_apply] using
              (integral_add
                ((hΓ0.add (hΓ1.const_mul (x^2/4))).sub
                  (hΓ2.const_mul (3*x^4/32)))
                (hΓ3.const_mul (7*x^6/128)))
      _ = _ := by
        have hSub :
            (∫ w in Set.Ici (0:ℝ),
              (w^k * Real.exp (-w) +
                (x^2/4) * (w^(k+1) * Real.exp (-w))) -
                (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ∂volume) =
              (∫ w in Set.Ici (0:ℝ),
                w^k * Real.exp (-w) +
                  (x^2/4) * (w^(k+1) * Real.exp (-w)) ∂volume) -
              (∫ w in Set.Ici (0:ℝ),
                (3*x^4/32) * (w^(k+2) * Real.exp (-w)) ∂volume) := by
          simpa only [Pi.add_apply, Pi.sub_apply] using
            (integral_sub (hΓ0.add (hΓ1.const_mul (x^2/4)))
              (hΓ2.const_mul (3*x^4/32)))
        have hAdd :
            (∫ w in Set.Ici (0:ℝ),
              w^k * Real.exp (-w) +
                (x^2/4) * (w^(k+1) * Real.exp (-w)) ∂volume) =
              (∫ w in Set.Ici (0:ℝ),
                w^k * Real.exp (-w) ∂volume) +
              (∫ w in Set.Ici (0:ℝ),
                (x^2/4) * (w^(k+1) * Real.exp (-w)) ∂volume) := by
          simpa only [Pi.add_apply] using
            (integral_add hΓ0 (hΓ1.const_mul (x^2/4)))
        rw [hSub, hAdd, integral_const_mul, integral_const_mul,
          integral_const_mul]
  calc
    thetaAuditedOneWeightedMoment x k =
      (∫ w in Set.Ici (0:ℝ),
        (Real.exp (-w) * (1+w*x^2)^((1:ℝ)/4)) * w^k ∂volume) := rfl
    _ ≤ (∫ w in Set.Ici (0:ℝ),
        (w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w))) -
          (3*x^4/32) * (w^(k+2) * Real.exp (-w)) +
          (7*x^6/128) * (w^(k+3) * Real.exp (-w)) ∂volume) :=
      integral_mono_ae hf hG hpoint
    _ = _ := by
      rw [hInt, hΓ0eval, hΓ1eval, hΓ2eval, hΓ3eval]

end W5
