import W5.ThetaAuditedMomentMonotonicity

/-!
# Independent exact Gamma box for ALL original first-cell theta moments

For the first audited cell 0 ≤ x ≤ 1/8 we can eliminate even the
numerical endpoint-moment assumptions from the previously proved
nine-moment real-interval bridge.

The elementary true-integrand inequality
  1 ≤ (1+w*x²)^(1/4) ≤ 1+w*x²    (w≥0, x≥0)
and the existing exact Mathlib Gamma moments imply
  k! ≤ M_k(x) ≤ k! + x²*(k+1)! ≤ k! + (k+1)!/64.

All bounds below are verified in Lean and contain NO 768-bit
exp/Taylor/sqrt oracle; their rational endpoints are explicit.
The remaining first-cell obligations are the nine REAL original
polynomial-coefficient interval enclosures and rational matrix
pivot checks, not moment quadrature.
-/

namespace W5
open MeasureTheory

/-- The lower Gamma bound follows from the previously formalized
monotonicity and exact zero-point identity, for every k. -/
theorem thetaAuditedOneWeightedMoment_gamma_lower
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (Nat.factorial k : ℝ) ≤ thetaAuditedOneWeightedMoment x k := by
  simpa only [thetaAuditedOneWeightedMoment_zero] using
    (thetaAuditedOneWeightedMoment_mono
      0 x (le_refl 0) hx hx1 k)

/-- Exact tangent bound for the genuine real fourth-root.
The fourth power is reduced using Mathlib's `Real.rpow_mul`,
and the final inequality follows from the nonnegative factorization
(r−1)²(r²+2r+3) = r⁴−4r+3. -/
theorem thetaFourthRoot_one_add_le_linear (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^((1:ℝ)/4) ≤ 1+t/4 := by
  let r : ℝ := (1+t)^((1:ℝ)/4)
  have hbase : 0 ≤ 1+t := by linarith
  have hr4 : r^4 = 1+t := by
    dsimp [r]
    calc
      ((1+t)^((1:ℝ)/4))^4 =
          (1+t)^(((1:ℝ)/4)*(4:ℝ)) := by
        rw [Real.rpow_mul hbase, Real.rpow_natCast]
      _ = 1+t := by norm_num
  have hrnonneg : 0 ≤ r := Real.rpow_nonneg hbase _
  have hfactor : 0 ≤ (r-1)^2 * (r^2+2*r+3) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

/-- A sharper upper Gamma bound using the tangent line to the
fourth-root function. The same previously formalized Lebesgue
integration, factorial moments and Mathlib integral monotonicity
proof are reused with x²/4 instead of x². -/
theorem thetaAuditedOneWeightedMoment_gamma_upper_quarter
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    thetaAuditedOneWeightedMoment x k ≤
      (Nat.factorial k : ℝ) +
        (x^2/4) * (Nat.factorial (k+1) : ℝ) := by
  have hf : IntegrableOn
      (fun w : ℝ =>
        (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k)
      (Set.Ici (0 : ℝ)) volume :=
    thetaAuditedOneWeightedMoment_integrable_nonneg x hx hx1 k
  have hΓ0 : IntegrableOn
      (fun w : ℝ => w^k * Real.exp (-w))
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable k)
  have hΓ1 : IntegrableOn
      (fun w : ℝ => w^(k+1) * Real.exp (-w))
      (Set.Ici (0 : ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2
      (thetaAuditedCorrectionGammaMoment_integrable (k+1))
  have hG : IntegrableOn
      (fun w : ℝ =>
        w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w)))
      (Set.Ici (0 : ℝ)) volume :=
    hΓ0.add (hΓ1.const_mul (x^2/4))
  have hΓ0eval :
      (∫ w in Set.Ici (0 : ℝ),
        w^k * Real.exp (-w) ∂volume) =
        (Nat.factorial k : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment k
  have hΓ1eval :
      (∫ w in Set.Ici (0 : ℝ),
        w^(k+1) * Real.exp (-w) ∂volume) =
        (Nat.factorial (k+1) : ℝ) := by
    rw [integral_Ici_eq_integral_Ioi]
    exact thetaAuditedCorrectionGammaMoment (k+1)
  have hpoint : ∀ᵐ w : ℝ
      ∂(volume.restrict (Set.Ici (0 : ℝ))),
      (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k ≤
        w^k * Real.exp (-w) +
          (x^2/4) * (w^(k+1) * Real.exp (-w)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
    have hw0 : 0 ≤ w := hw
    have hbase : 1 ≤ 1+w*x^2 := by
      nlinarith [mul_nonneg hw0 (sq_nonneg x)]
    have hroot :
        (1+w*x^2)^((1 : ℝ)/4) ≤ 1+w*x^2/4 :=
      thetaFourthRoot_one_add_le_linear (w*x^2)
        (mul_nonneg hw0 (sq_nonneg x))
    calc
      (Real.exp (-w) * (1+w*x^2)^((1 : ℝ)/4)) * w^k ≤
          (Real.exp (-w) * (1+w*x^2/4)) * w^k :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot (Real.exp_nonneg _))
          (pow_nonneg hw0 k)
      _ = w^k * Real.exp (-w) +
            (x^2/4) * (w^(k+1) * Real.exp (-w)) := by ring
  calc
    thetaAuditedOneWeightedMoment x k ≤
        ∫ w in Set.Ici (0 : ℝ),
          (w^k * Real.exp (-w) +
            (x^2/4) * (w^(k+1) * Real.exp (-w))) ∂volume := by
          unfold thetaAuditedOneWeightedMoment
          exact integral_mono_ae hf hG hpoint
    _ = (∫ w in Set.Ici (0 : ℝ),
          w^k * Real.exp (-w) ∂volume) +
        x^2 * (∫ w in Set.Ici (0 : ℝ),
          w^(k+1) * Real.exp (-w) ∂volume) := by
          rw [integral_add hΓ0 (hΓ1.const_mul (x^2/4))]
          rw [integral_const_mul]
    _ = (Nat.factorial k : ℝ) +
          (x^2/4) * (Nat.factorial (k+1) : ℝ) := by
          rw [hΓ0eval, hΓ1eval]

/-- Backward-compatible coarse Gamma bound, now deduced from the
stronger fourth-root tangent bound rather than reintegrating. -/
theorem thetaAuditedOneWeightedMoment_gamma_upper
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    thetaAuditedOneWeightedMoment x k ≤
      (Nat.factorial k : ℝ) +
        x^2 * (Nat.factorial (k+1) : ℝ) := by
  calc
    thetaAuditedOneWeightedMoment x k ≤
        (Nat.factorial k : ℝ) +
          (x^2/4) * (Nat.factorial (k+1) : ℝ) :=
      thetaAuditedOneWeightedMoment_gamma_upper_quarter x hx hx1 k
    _ ≤ (Nat.factorial k : ℝ) +
          x^2 * (Nat.factorial (k+1) : ℝ) := by
      have hsq : x^2/4 ≤ x^2 := by nlinarith [sq_nonneg x]
      have hmul :=
        mul_le_mul_of_nonneg_right hsq
          (show (0:ℝ) ≤ (Nat.factorial (k+1) : ℝ) by positivity)
      exact add_le_add_right hmul _

/-- A computable, purely rational enclosure. No floating-point
roundoff, quadrature or 768-bit interval transport. -/
def thetaAuditedFirstCellGammaMomentInterval (k : ℕ) : QInterval :=
  ⟨(Nat.factorial k : ℚ),
    (Nat.factorial k : ℚ) +
      (Nat.factorial (k+1) : ℚ)/64⟩

/-- For EVERY x in the whole FIRST audited interval, all original
nine weighted moments are enclosed in the explicit Gamma box.
In fact this holds for every k, without a cutoff assumption. -/
theorem thetaAuditedFirstCellGammaMomentInterval_containsReal
    (x : ℝ) (hx : 0 ≤ x)
    (hxB : x ≤ (1 : ℝ)/8) (k : ℕ) :
    QInterval.ContainsReal
      (thetaAuditedFirstCellGammaMomentInterval k)
      (thetaAuditedOneWeightedMoment x k) := by
  have hx1 : x ≤ 1 := by linarith
  have hsq : x^2 ≤ (1 : ℝ)/64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxB)
      (add_nonneg hx (by norm_num : (0 : ℝ) ≤ 1/8))]
  have hlo := thetaAuditedOneWeightedMoment_gamma_lower x hx hx1 k
  have hu := thetaAuditedOneWeightedMoment_gamma_upper x hx hx1 k
  have hupper :
      thetaAuditedOneWeightedMoment x k ≤
        (Nat.factorial k : ℝ) +
          (Nat.factorial (k+1) : ℝ)/64 := by
    calc
      _ ≤ (Nat.factorial k : ℝ) +
          x^2 * (Nat.factorial (k+1) : ℝ) := hu
      _ ≤ (Nat.factorial k : ℝ) +
          (1/64 : ℝ) * (Nat.factorial (k+1) : ℝ) := by
            have hfac : (0 : ℝ) ≤ (Nat.factorial (k+1) : ℝ) := by
              positivity
            exact add_le_add_right
              (mul_le_mul_of_nonneg_right hsq hfac)
              (Nat.factorial k : ℝ)
      _ = (Nat.factorial k : ℝ) +
          (Nat.factorial (k+1) : ℝ)/64 := by ring
  simpa only [QInterval.ContainsReal,
    thetaAuditedFirstCellGammaMomentInterval,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] using (show
      (Nat.factorial k : ℝ) ≤ thetaAuditedOneWeightedMoment x k ∧
      thetaAuditedOneWeightedMoment x k ≤
        (Nat.factorial k : ℝ) +
          (Nat.factorial (k+1) : ℝ)/64 from ⟨hlo, hupper⟩)

/-- This discharges ALL nine moment hypotheses in the existing
REAL first-cell interval soundness theorem automatically.
Only polynomial coefficients, the x²/4 interval, and exact
rational result inclusion remain explicit. -/
theorem thetaCoefficient_first_cell_containsReal_of_gamma_box
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5)
    (D X : QInterval) (C : ℕ → QInterval)
    (Target : QInterval)
    (hdiag : QInterval.ContainsReal D
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0))
    (hscale : QInterval.ContainsReal X (x^2/4))
    (hcoeff : ∀ k ∈ Finset.range 9,
      QInterval.ContainsReal (C k)
        ((thetaCorrectionWPolynomial x 1 0 i j).coeff k))
    (hlo : Target.lo ≤
      (QInterval.add
        (thetaAuditedOneTermMomentInterval
          D X C thetaAuditedFirstCellGammaMomentInterval 9)
        thetaAuditedTailErrorInterval).lo)
    (hhi : (QInterval.add
        (thetaAuditedOneTermMomentInterval
          D X C thetaAuditedFirstCellGammaMomentInterval 9)
        thetaAuditedTailErrorInterval).hi ≤ Target.hi) :
    QInterval.ContainsReal Target (thetaCoefficient x i j) := by
  exact thetaCoefficient_first_cell_containsReal_of_nine_moment_intervals
    x hx hxB i j D X C thetaAuditedFirstCellGammaMomentInterval
    Target hdiag hscale hcoeff
    (fun k _ =>
      thetaAuditedFirstCellGammaMomentInterval_containsReal
        x hx.le hxB k)
    hlo hhi

end W5
