import W5.ThetaMixedJetNeighborMajorant

/-!
# One separable summable/integrable envelope for every mixed theta jet

The previous exact mixed derivative identity has a bound involving
the adjacent right jets and the polynomial factor p+w, p=n².
Since 0 ≤ p,w, we have p+w ≤ (p+1)(w+1). This file converts that
bound into one honest product A_k(n) B_k(w), whose n factor is
summable and whose w factor is Lebesgue integrable.

The estimates hold uniformly on |u|,|v| ≤ x/8 for 0<x≤1 and
every fixed right order k. These are the required domination
ingredients for later mixed derivative/interchange theorems.
-/

namespace W5
open MeasureTheory

/-- Summable n-factor for a mixed (one-left, k-right) jet:
one extra polynomial power compared with ordinary right jets. -/
noncomputable def thetaMixedJetIndexFactor
    (k : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  (k:ℝ) * (((n:ℝ)^2+1) * thetaHigherJetIndexFactor (k-1) x n) +
    (1/x+2) * (((n:ℝ)^2+1) * thetaHigherJetIndexFactor k x n)

/-- The w-factor after separating p+w, with exponential decay. -/
noncomputable def thetaMixedJetTailFactor (k : ℕ) (w : ℝ) : ℝ :=
  (w+1) *
    (thetaHigherJetTailFactor (k-1) w + thetaHigherJetTailFactor k w)

/-- Multiplying the n-factor of a genuine right jet by p+1
still leaves a summable Gaussian sequence. -/
theorem thetaHigherJetIndexFactor_extra_square_summable
    (j : ℕ) (x : ℝ) :
    Summable (fun n : ℕ =>
      (((n:ℝ)^2+1) * thetaHigherJetIndexFactor j x n)) := by
  have h := (thetaHigherJet_shifted_index_summable (j+2)).mul_left
    ((1/x+2)^j * Real.exp (3/4))
  convert h using 1
  funext n
  dsimp [thetaHigherJetIndexFactor]
  rw [show j+2 = (j+1)+1 by omega, pow_succ]
  ring

/-- The mixed n-index envelope is summable for every k and x,
without an additional analyticity or interchange assumption. -/
theorem thetaMixedJetIndexFactor_summable (k : ℕ) (x : ℝ) :
    Summable (thetaMixedJetIndexFactor k x) := by
  have hprev :=
    (thetaHigherJetIndexFactor_extra_square_summable (k-1) x).mul_left (k:ℝ)
  have hnow :=
    (thetaHigherJetIndexFactor_extra_square_summable k x).mul_left (1/x+2)
  change Summable (fun n : ℕ =>
    (k:ℝ) * (((n:ℝ)^2+1) * thetaHigherJetIndexFactor (k-1) x n) +
    (1/x+2) * (((n:ℝ)^2+1) * thetaHigherJetIndexFactor k x n))
  exact hprev.add hnow

/-- Multiplying the w-factor by w+1 shifts the jet order by one. -/
theorem thetaHigherJetTailFactor_shift
    (j : ℕ) (w : ℝ) :
    (w+1) * thetaHigherJetTailFactor j w =
      thetaHigherJetTailFactor (j+1) w := by
  dsimp [thetaHigherJetTailFactor]
  rw [pow_succ]
  ring

/-- The mixed w-tail envelope is integrable on the positive half-line
at every fixed derivative order. -/
theorem thetaMixedJetTailFactor_integrableOn (k : ℕ) :
    IntegrableOn (thetaMixedJetTailFactor k)
      (Set.Ioi (0:ℝ)) volume := by
  let μ := volume.restrict (Set.Ioi (0:ℝ))
  have hprev : Integrable
      (fun w : ℝ => (w+1)*thetaHigherJetTailFactor (k-1) w) μ := by
    have heq :
        (fun w : ℝ => (w+1)*thetaHigherJetTailFactor (k-1) w) =
        thetaHigherJetTailFactor ((k-1)+1) := by
      funext w
      exact thetaHigherJetTailFactor_shift (k-1) w
    rw [heq]
    exact thetaHigherJet_full_w_factor_integrableOn ((k-1)+1)
  have hnow : Integrable
      (fun w : ℝ => (w+1)*thetaHigherJetTailFactor k w) μ := by
    have heq :
        (fun w : ℝ => (w+1)*thetaHigherJetTailFactor k w) =
        thetaHigherJetTailFactor (k+1) := by
      funext w
      exact thetaHigherJetTailFactor_shift k w
    rw [heq]
    exact thetaHigherJet_full_w_factor_integrableOn (k+1)
  change Integrable (thetaMixedJetTailFactor k) μ
  have h := hprev.add hnow
  convert h using 1
  funext w
  dsimp [thetaMixedJetTailFactor]
  ring

/-- Actual mixed theta Gaussian jet, majorized by ONE separable
summable/integrable product. The estimate is uniform on the full
small closed two-parameter box, including index n=0. -/
theorem thetaMixedOneRightJetSeriesTerm_norm_le_separable
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ)
    (hx : 0 < x) (hx1 : x ≤ 1)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) (hw : 0 ≤ w) :
    ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
      thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w := by
  let p : ℝ := (n:ℝ)^2
  let C : ℝ := 1/x+2
  let Iprev : ℝ := thetaHigherJetIndexFactor (k-1) x n
  let Inow : ℝ := thetaHigherJetIndexFactor k x n
  let Tprev : ℝ := thetaHigherJetTailFactor (k-1) w
  let Tnow : ℝ := thetaHigherJetTailFactor k w
  let A : ℝ := (k:ℝ) * (p+1) * Iprev
  let B : ℝ := C * (p+1) * Inow
  let D : ℝ := (w+1) * Tprev
  let E : ℝ := (w+1) * Tnow
  have hp : 0 ≤ p := sq_nonneg _
  have hc : 0 ≤ C := by dsimp [C]; positivity
  have hw1 : 0 ≤ w+1 := by linarith
  have hi0 : 0 ≤ Iprev := by dsimp [Iprev, thetaHigherJetIndexFactor]; positivity
  have hi1 : 0 ≤ Inow := by dsimp [Inow, thetaHigherJetIndexFactor]; positivity
  have ht0 : 0 ≤ Tprev := by dsimp [Tprev, thetaHigherJetTailFactor]; positivity
  have ht1 : 0 ≤ Tnow := by dsimp [Tnow, thetaHigherJetTailFactor]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hsep : p+w ≤ (p+1)*(w+1) := by
    nlinarith [mul_nonneg hp hw]
  have hfirst :
      (k:ℝ) * (p+w) * (Iprev*Tprev) ≤ A*D := by
    have hmul := mul_le_mul_of_nonneg_right hsep (mul_nonneg hi0 ht0)
    have hmul2 := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg k)
    calc
      (k:ℝ)*(p+w)*(Iprev*Tprev) =
          (k:ℝ)*((p+w)*(Iprev*Tprev)) := by ring
      _ ≤ (k:ℝ)*(((p+1)*(w+1))*(Iprev*Tprev)) := hmul2
      _ = A*D := by dsimp [A,D]; ring
  have hsecond :
      C * (p+w) * (Inow*Tnow) ≤ B*E := by
    have hmul := mul_le_mul_of_nonneg_right hsep (mul_nonneg hi1 ht1)
    have hmul2 := mul_le_mul_of_nonneg_left hmul hc
    calc
      C*(p+w)*(Inow*Tnow) =
          C*((p+w)*(Inow*Tnow)) := by ring
      _ ≤ C*(((p+1)*(w+1))*(Inow*Tnow)) := hmul2
      _ = B*E := by dsimp [B,E]; ring
  have hcross : A*D+B*E ≤ (A+B)*(D+E) := by
    nlinarith [mul_nonneg hA hE, mul_nonneg hB hD]
  have hbase := thetaMixedOneRightJetSeriesTerm_norm_le_two_gaussian_factors
    k x u v n w hx hx1 hu hv hw
  change ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
      (k:ℝ)*(p+w)*(Iprev*Tprev) + C*(p+w)*(Inow*Tnow) at hbase
  calc
    ‖thetaMixedOneRightJetSeriesTerm k x u v n w‖ ≤
        (k:ℝ)*(p+w)*(Iprev*Tprev) + C*(p+w)*(Inow*Tnow) := hbase
    _ ≤ A*D+B*E := add_le_add hfirst hsecond
    _ ≤ (A+B)*(D+E) := hcross
    _ = thetaMixedJetIndexFactor k x n * thetaMixedJetTailFactor k w := by
      dsimp [A,B,D,E,Iprev,Inow,Tprev,Tnow,p,C,
        thetaMixedJetIndexFactor, thetaMixedJetTailFactor]
      ring

end W5
