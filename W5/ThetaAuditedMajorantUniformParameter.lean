import W5.ThetaAuditedMajorantTailNumerical
import Mathlib.Analysis.Complex.Exponential

/-!
# Uniformity of the audited Gaussian theta tail in y = 1/x²

The integer auditor evaluates its omitted-square majorant only at the
two lower endpoints y=3 and y=64. This is rigorous only if the
parameter-dependent factor y^4 * exp(-((n²-1)*y)) is nonincreasing
for every omitted n>=2 and every y above its lower endpoint.

Here we prove precisely that monotonicity, without using any
unverified interval algorithm. We reuse Mathlib's
`Real.add_one_le_exp`, `Real.exp_nat_mul`, and
`Summable.tsum_le_tsum`; the already established half-ratio
and two <10^-35 finite Taylor bounds are imported.

This proves the exact NUMERICAL tail for every admissible
parameter y, rather than just for y=3 and y=64.
The theta-coefficient-to-majorant pointwise inequality is still
a separate required theorem, not silently assumed.
-/

namespace W5

/-- On c*a>=4 the true function y↦y⁴ exp(-c*y) is
nonincreasing for y>=a. This avoids redoing calculus:
Mathlib's elementary inequality 1+t≤exp t suffices. -/
theorem thetaFourthPowerExp_decay_mono
    (a y c : ℝ) (ha : 0 < a) (hay : a ≤ y)
    (hc : 4 ≤ c*a) :
    y^4 * Real.exp (-(c*y)) ≤
      a^4 * Real.exp (-(c*a)) := by
  have hy0 : 0 ≤ y := ha.le.trans hay
  have hdiff : 0 ≤ y-a := sub_nonneg.mpr hay
  have hstep : (y-a)/a ≤ c*(y-a)/4 := by
    apply (div_le_iff₀ ha).mpr
    have hmul : 0 ≤ (c*a-4)*(y-a) :=
      mul_nonneg (by linarith) hdiff
    nlinarith
  have hunit : y/a ≤ Real.exp (c*(y-a)/4) := by
    calc
      y/a = (y-a)/a+1 := by
        field_simp [ne_of_gt ha]
        ring
      _ ≤ Real.exp ((y-a)/a) :=
        Real.add_one_le_exp ((y-a)/a)
      _ ≤ Real.exp (c*(y-a)/4) :=
        Real.exp_le_exp.mpr hstep
  have hpower : (y/a)^4 ≤ Real.exp (c*(y-a)) := by
    calc
      (y/a)^4 ≤ (Real.exp (c*(y-a)/4))^4 :=
        pow_le_pow_left₀ (div_nonneg hy0 ha.le) hunit 4
      _ = Real.exp (c*(y-a)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hfactor : y^4 = a^4*(y/a)^4 := by
    field_simp [ne_of_gt ha]
  calc
    y^4 * Real.exp (-(c*y)) =
        a^4 * ((y/a)^4 * Real.exp (-(c*y))) := by
      rw [hfactor]
      ring
    _ ≤ a^4 *
        (Real.exp (c*(y-a)) * Real.exp (-(c*y))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _))
        (pow_nonneg ha.le 4)
    _ = a^4 * Real.exp (-(c*a)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Each square-index majorant carries the uniform exponential
monotonicity as soon as n>=2 and y>=a>=3. -/
theorem thetaMajorantTerm_parameter_mono
    (a y : ℝ) (ha : 3 ≤ a) (hay : a ≤ y)
    (n : ℕ) (hn : 2 ≤ n) :
    y^4 * thetaMajorantTerm y n ≤
      a^4 * thetaMajorantTerm a n := by
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hc3 : (3:ℝ) ≤ (n:ℝ)^2-1 := by
    nlinarith [sq_nonneg ((n:ℝ)-2)]
  have hc4 : 4 ≤ ((n:ℝ)^2-1)*a := by
    have h := mul_le_mul hc3 ha
      (by norm_num : (0:ℝ) ≤ 3)
      (by linarith : 0 ≤ (n:ℝ)^2-1)
    nlinarith
  have hd := thetaFourthPowerExp_decay_mono a y
    ((n:ℝ)^2-1) (by linarith) hay hc4
  calc
    y^4 * thetaMajorantTerm y n =
        (n:ℝ)^26 * (y^4 * Real.exp (-(((n:ℝ)^2-1)*y))) := by
      unfold thetaMajorantTerm
      ring
    _ ≤ (n:ℝ)^26 * (a^4 * Real.exp (-(((n:ℝ)^2-1)*a))) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = a^4 * thetaMajorantTerm a n := by
      unfold thetaMajorantTerm
      ring

/-- Existing geometric domination already implies summability of
the exact real majorant, so no new convergence argument is needed. -/
theorem thetaMajorantTerm_tail_summable
    (N : ℕ) (hN : 2 ≤ N) (y : ℝ) (hy : 3 ≤ y) :
    Summable (fun k : ℕ => thetaMajorantTerm y (N+k)) := by
  apply Summable.of_nonneg_of_le
    (fun k => by unfold thetaMajorantTerm; positivity)
    (thetaMajorantTerm_geometric_bound N hN y hy)
  exact summable_geometric_two.mul_right (thetaMajorantTerm y N)

/-- The ENTIRE infinite majorant decreases at the parameter
endpoint, after multiplication by its polynomial y⁴ factor. -/
theorem thetaMajorantTerm_uniform_tail
    (N : ℕ) (hN : 2 ≤ N)
    (a y : ℝ) (ha : 3 ≤ a) (hay : a ≤ y) :
    y^4 * (∑' k : ℕ, thetaMajorantTerm y (N+k)) ≤
      a^4 * (∑' k : ℕ, thetaMajorantTerm a (N+k)) := by
  have hsY : Summable (fun k : ℕ =>
      y^4 * thetaMajorantTerm y (N+k)) :=
    (thetaMajorantTerm_tail_summable N hN y (ha.trans hay)).mul_left _
  have hsA : Summable (fun k : ℕ =>
      a^4 * thetaMajorantTerm a (N+k)) :=
    (thetaMajorantTerm_tail_summable N hN a ha).mul_left _
  have hcmp : ∀ k : ℕ,
      y^4 * thetaMajorantTerm y (N+k) ≤
        a^4 * thetaMajorantTerm a (N+k) := by
    intro k
    exact thetaMajorantTerm_parameter_mono a y ha hay (N+k) (by omega)
  have h := hsY.tsum_le_tsum hcmp hsA
  simpa only [tsum_mul_left] using h

/-- The near-regime 10^-35 majorant estimate holds for ALL
real y>=3, not merely at the endpoint used by the Python code. -/
theorem thetaAuditorNearMajorant_uniform_lt_oneE35
    (y : ℝ) (hy : 3 ≤ y) :
    ((5*4096*30000000000 : ℝ) * y^4) *
      (∑' k : ℕ, thetaMajorantTerm y (12+k)) <
        1 / (10 : ℝ)^35 := by
  have h := thetaMajorantTerm_uniform_tail 12
    (by norm_num) 3 y (by norm_num) hy
  calc
    ((5*4096*30000000000 : ℝ) * y^4) *
      (∑' k : ℕ, thetaMajorantTerm y (12+k)) =
        (5*4096*30000000000 : ℝ) *
          (y^4*(∑' k : ℕ, thetaMajorantTerm y (12+k))) := by ring
    _ ≤ (5*4096*30000000000 : ℝ) *
          ((3:ℝ)^4*(∑' k : ℕ, thetaMajorantTerm 3 (12+k))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ((5*4096*30000000000 : ℝ) * (3:ℝ)^4) *
        (∑' k : ℕ, thetaMajorantTerm 3 (12+k)) := by ring
    _ < 1 / (10 : ℝ)^35 :=
      thetaAuditorNearMajorantTsum_lt_oneE35

/-- Similarly the full far-regime tail estimate holds for
ALL real y>=64, not only at the endpoint y=64. -/
theorem thetaAuditorFarMajorant_uniform_lt_oneE35
    (y : ℝ) (hy : 64 ≤ y) :
    ((5*4096*30000000000 : ℝ) * y^4) *
      (∑' k : ℕ, thetaMajorantTerm y (2+k)) <
        1 / (10 : ℝ)^35 := by
  have h := thetaMajorantTerm_uniform_tail 2
    (by norm_num) 64 y (by norm_num) hy
  calc
    ((5*4096*30000000000 : ℝ) * y^4) *
      (∑' k : ℕ, thetaMajorantTerm y (2+k)) =
        (5*4096*30000000000 : ℝ) *
          (y^4*(∑' k : ℕ, thetaMajorantTerm y (2+k))) := by ring
    _ ≤ (5*4096*30000000000 : ℝ) *
          ((64:ℝ)^4*(∑' k : ℕ, thetaMajorantTerm 64 (2+k))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = ((5*4096*30000000000 : ℝ) * (64:ℝ)^4) *
        (∑' k : ℕ, thetaMajorantTerm 64 (2+k)) := by ring
    _ < 1 / (10 : ℝ)^35 :=
      thetaAuditorFarMajorantTsum_lt_oneE35

/-- Map the entire R5 compact domain to y>=3, using only
the existing rational upper endpoint 145/256. -/
theorem thetaAuditor_y_ge_three
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (145:ℝ)/256) :
    (3:ℝ) ≤ 1/x^2 := by
  have hx2 : (0:ℝ) < x^2 := by positivity
  have hbound : x^2 ≤ ((145:ℝ)/256)^2 :=
    pow_le_pow_left₀ hx.le hxB 2
  apply (le_div_iff₀ hx2).mpr
  nlinarith [hbound]

/-- The original far-cell range x<=1/8 implies y>=64. -/
theorem thetaAuditor_y_ge_sixtyfour
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1:ℝ)/8) :
    (64:ℝ) ≤ 1/x^2 := by
  have hx2 : (0:ℝ) < x^2 := by positivity
  have hbound : x^2 ≤ ((1:ℝ)/8)^2 :=
    pow_le_pow_left₀ hx.le hxB 2
  apply (le_div_iff₀ hx2).mpr
  nlinarith [hbound]

/-- The actual real y=1/x² near-domain estimate, with no
numerical parameter approximations or interval-oracle axioms. -/
theorem thetaAuditorNearMajorant_on_x_domain
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (145:ℝ)/256) :
    ((5*4096*30000000000 : ℝ) * (1/x^2)^4) *
      (∑' k : ℕ, thetaMajorantTerm (1/x^2) (12+k)) <
        1 / (10 : ℝ)^35 :=
  thetaAuditorNearMajorant_uniform_lt_oneE35
    (1/x^2) (thetaAuditor_y_ge_three x hx hxB)

/-- The analogous x<=1/8 far-domain bound. -/
theorem thetaAuditorFarMajorant_on_x_domain
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1:ℝ)/8) :
    ((5*4096*30000000000 : ℝ) * (1/x^2)^4) *
      (∑' k : ℕ, thetaMajorantTerm (1/x^2) (2+k)) <
        1 / (10 : ℝ)^35 :=
  thetaAuditorFarMajorant_uniform_lt_oneE35
    (1/x^2) (thetaAuditor_y_ge_sixtyfour x hx hxB)

end W5
