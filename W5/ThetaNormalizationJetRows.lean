import W5.OriginalPsiJet
import W5.NormalizedKernelZeroth

/-!
A finite chain/product rule for the genuine normalization, avoiding
Faà di Bruno expansions of the 25 mixed derivatives. The gauge is
written as an exponential of a logarithm on the open positive patch.
With b=x/(4(1+xu)), its derivatives obey b'=-4b², g'=g(1/x-5b).
-/
namespace W5
open Filter
open scoped Topology

noncomputable def thetaNormSlope (x u : ℝ) : ℝ := x / (4*(1+x*u))
noncomputable def thetaNormShift (x u : ℝ) : ℝ := Real.log (1+x*u)/4
noncomputable def thetaNormGauge (x u : ℝ) : ℝ :=
  Real.exp (u/x - (5:ℝ)/4 * Real.log (1+x*u))

theorem thetaNormSlope_hasDerivAt (x u : ℝ) (h : 1+x*u ≠ 0) :
    HasDerivAt (thetaNormSlope x) (-4*(thetaNormSlope x u)^2) u := by
  have hbase : HasDerivAt (fun z : ℝ => 1+x*z) x u := by
    simpa using (((hasDerivAt_id u).const_mul x).const_add (1:ℝ))
  have hden := hbase.const_mul (4:ℝ)
  have hd : 4*(1+x*u) ≠ 0 := mul_ne_zero (by norm_num) h
  have hh := (hasDerivAt_const u x).div hden hd
  convert hh using 1
  · funext z
    rfl
  · simp only [thetaNormSlope]
    field_simp [h] <;> ring

theorem thetaNormShift_hasDerivAt (x u : ℝ) (h : 1+x*u ≠ 0) :
    HasDerivAt (thetaNormShift x) (thetaNormSlope x u) u := by
  have hbase : HasDerivAt (fun z : ℝ => 1+x*z) x u := by
    simpa using (((hasDerivAt_id u).const_mul x).const_add (1:ℝ))
  have hh := ((Real.hasDerivAt_log h).comp u hbase).const_mul ((1:ℝ)/4)
  convert hh using 1
  · funext z
    simp only [thetaNormShift, Function.comp_def, Pi.sub_apply]
    ring
  · unfold thetaNormSlope
    field_simp [h] <;> ring

theorem thetaNormGauge_hasDerivAt (x u : ℝ) (h : 1+x*u ≠ 0) :
    HasDerivAt (thetaNormGauge x)
      (thetaNormGauge x u*(1/x-5*thetaNormSlope x u)) u := by
  have harg : HasDerivAt (fun z : ℝ => z/x) (1/x) u := by
    convert (hasDerivAt_id u).const_mul (1/x) using 1 <;>
      first | rfl | funext z; simp only [id_eq]; ring | ring
  have hlog := (thetaNormShift_hasDerivAt x u h).const_mul (5:ℝ)
  have hsub := harg.sub hlog
  have hh := (Real.hasDerivAt_exp (u/x-5*thetaNormShift x u)).comp u hsub
  convert hh using 1
  · funext z
    simp only [thetaNormGauge, thetaNormShift, Function.comp_def, Pi.sub_apply]
    congr 1
    ring
  · unfold thetaNormGauge thetaNormShift
    congr 1 <;> ring

noncomputable def thetaNormJetPolynomial (a b : ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => (1:ℝ)
  | 1, 0 => (1:ℝ)*a^1 + (-5:ℝ)*b^1
  | 1, 1 => (1:ℝ)*b^1
  | 2, 0 => (1:ℝ)*a^2 + (-10:ℝ)*a^1*b^1 + (45:ℝ)*b^2
  | 2, 1 => (2:ℝ)*a^1*b^1 + (-14:ℝ)*b^2
  | 2, 2 => (1:ℝ)*b^2
  | 3, 0 => (1:ℝ)*a^3 + (-15:ℝ)*a^2*b^1 + (135:ℝ)*a^1*b^2 + (-585:ℝ)*b^3
  | 3, 1 => (3:ℝ)*a^2*b^1 + (-42:ℝ)*a^1*b^2 + (227:ℝ)*b^3
  | 3, 2 => (3:ℝ)*a^1*b^2 + (-27:ℝ)*b^3
  | 3, 3 => (1:ℝ)*b^3
  | 4, 0 => (1:ℝ)*a^4 + (-20:ℝ)*a^3*b^1 + (270:ℝ)*a^2*b^2 + (-2340:ℝ)*a^1*b^3 + (9945:ℝ)*b^4
  | 4, 1 => (4:ℝ)*a^3*b^1 + (-84:ℝ)*a^2*b^2 + (908:ℝ)*a^1*b^3 + (-4444:ℝ)*b^4
  | 4, 2 => (6:ℝ)*a^2*b^2 + (-108:ℝ)*a^1*b^3 + (686:ℝ)*b^4
  | 4, 3 => (4:ℝ)*a^1*b^3 + (-44:ℝ)*b^4
  | 4, 4 => (1:ℝ)*b^4
  | _, _ => 0

/-- Actual row of the one-variable gauged composition jet. -/
noncomputable def thetaNormJetSection (f : ℕ → ℝ → ℝ)
    (x t : ℝ) (m k : ℕ) (u : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (k+1),
    (thetaNormGauge x u *
      thetaNormJetPolynomial (1/x) (thetaNormSlope x u) k l) *
      f (m+l) (t+thetaNormShift x u)

theorem thetaNormJetSection_zero (f : ℕ → ℝ → ℝ) (x t : ℝ) (m : ℕ) (u : ℝ) :
    thetaNormJetSection f x t m 0 u =
      thetaNormGauge x u * f m (t+thetaNormShift x u) := by
  simp [thetaNormJetSection, thetaNormJetPolynomial]

theorem thetaNormJetSection_hasDerivAt
    (f : ℕ → ℝ → ℝ)
    (N : ℕ) (hf : ∀ m < N, ∀ t : ℝ, HasDerivAt (f m) (f (m+1) t) t)
    (x t u : ℝ) (m k : ℕ) (hk : k < 4) (hm : m+k < N)
    (hu : 1+x*u ≠ 0) :
    HasDerivAt (thetaNormJetSection f x t m k)
      (thetaNormJetSection f x t m (k+1) u) u := by
  let a : ℝ := 1/x
  let b : ℝ → ℝ := thetaNormSlope x
  have hb : HasDerivAt b (-4*(b u)^2) u :=
    thetaNormSlope_hasDerivAt x u hu
  have hg := thetaNormGauge_hasDerivAt x u hu
  have hs' := (thetaNormShift_hasDerivAt x u hu).const_add t
  interval_cases k
  · -- order 0
    have hP0 := (hb.pow 0).const_mul ((1:ℝ) * a^0)
    have hF0 := (hf (m+0) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h0 := (hg.mul hP0).mul hF0
    have h := h0
    convert h using 1
    · funext z
      simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def, Nat.add_zero, one_mul, zero_add, add_zero, pow_zero] <;>
      dsimp [a, b] <;> ring
    · simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def,
        Nat.add_zero, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one,
        one_mul, zero_mul, zero_add, add_zero] <;> norm_num <;> dsimp [a,b] <;> ring
  · -- order 1
    have hP0 := ((hb.pow 0).const_mul ((1:ℝ) * a^1)).add ((hb.pow 1).const_mul ((-5:ℝ) * a^0))
    have hF0 := (hf (m+0) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h0 := (hg.mul hP0).mul hF0
    have hP1 := (hb.pow 1).const_mul ((1:ℝ) * a^0)
    have hF1 := (hf (m+1) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h1 := (hg.mul hP1).mul hF1
    have h := (h0).add h1
    convert h using 1
    · funext z
      simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def, Nat.add_zero, one_mul, zero_add, add_zero, pow_zero] <;>
      dsimp [a, b] <;> ring
    · simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def,
        Nat.add_zero, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one,
        one_mul, zero_mul, zero_add, add_zero] <;> norm_num <;> dsimp [a,b] <;> ring
  · -- order 2
    have hP0 := (((hb.pow 0).const_mul ((1:ℝ) * a^2)).add ((hb.pow 1).const_mul ((-10:ℝ) * a^1))).add ((hb.pow 2).const_mul ((45:ℝ) * a^0))
    have hF0 := (hf (m+0) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h0 := (hg.mul hP0).mul hF0
    have hP1 := ((hb.pow 1).const_mul ((2:ℝ) * a^1)).add ((hb.pow 2).const_mul ((-14:ℝ) * a^0))
    have hF1 := (hf (m+1) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h1 := (hg.mul hP1).mul hF1
    have hP2 := (hb.pow 2).const_mul ((1:ℝ) * a^0)
    have hF2 := (hf (m+2) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h2 := (hg.mul hP2).mul hF2
    have h := ((h0).add h1).add h2
    convert h using 1
    · funext z
      simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def, Nat.add_zero, one_mul, zero_add, add_zero, pow_zero] <;>
      dsimp [a, b] <;> ring
    · simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def,
        Nat.add_zero, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one,
        one_mul, zero_mul, zero_add, add_zero] <;> norm_num <;> dsimp [a,b] <;> ring
  · -- order 3
    have hP0 := ((((hb.pow 0).const_mul ((1:ℝ) * a^3)).add ((hb.pow 1).const_mul ((-15:ℝ) * a^2))).add ((hb.pow 2).const_mul ((135:ℝ) * a^1))).add ((hb.pow 3).const_mul ((-585:ℝ) * a^0))
    have hF0 := (hf (m+0) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h0 := (hg.mul hP0).mul hF0
    have hP1 := (((hb.pow 1).const_mul ((3:ℝ) * a^2)).add ((hb.pow 2).const_mul ((-42:ℝ) * a^1))).add ((hb.pow 3).const_mul ((227:ℝ) * a^0))
    have hF1 := (hf (m+1) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h1 := (hg.mul hP1).mul hF1
    have hP2 := ((hb.pow 2).const_mul ((3:ℝ) * a^1)).add ((hb.pow 3).const_mul ((-27:ℝ) * a^0))
    have hF2 := (hf (m+2) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h2 := (hg.mul hP2).mul hF2
    have hP3 := (hb.pow 3).const_mul ((1:ℝ) * a^0)
    have hF3 := (hf (m+3) (by omega) (t+thetaNormShift x u)).comp u hs'
    have h3 := (hg.mul hP3).mul hF3
    have h := (((h0).add h1).add h2).add h3
    convert h using 1
    · funext z
      simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def, Nat.add_zero, one_mul, zero_add, add_zero, pow_zero] <;>
      dsimp [a, b] <;> ring
    · simp only [thetaNormJetSection, Finset.sum_range_succ, Finset.sum_range_zero,
        thetaNormJetPolynomial, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, Function.comp_def,
        Nat.add_zero, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one,
        one_mul, zero_mul, zero_add, add_zero] <;> norm_num <;> dsimp [a,b] <;> ring


theorem thetaNormPsiJet_hasDerivAt (m : ℕ) (hm : m < 8) (t : ℝ) :
    HasDerivAt (originalPsiJet m) (originalPsiJet (m+1) t) t := by
  have heq : originalPsiJet m = iteratedDeriv m Psi1 := by
    funext z
    exact originalPsiJet_eq_iteratedDeriv m z (by omega)
  rw [heq, originalPsiJet_eq_iteratedDeriv (m+1) t (by omega), iteratedDeriv_succ]
  apply DifferentiableAt.hasDerivAt
  interval_cases m
  · simpa only [iteratedDeriv_zero] using (Psi1_hasDerivAt t).differentiableAt
  · have hfun : iteratedDeriv 1 Psi1 = fun s : ℝ => -Phi s := by
      funext s
      rw [iteratedDeriv_one, Psi1_deriv]
    rw [hfun]
    exact (Phi_hasDerivAt t).differentiableAt.neg
  · exact (Psi1_second_differentiable t)
  · exact (Psi1_third_differentiable t)
  · exact (Psi1_fourth_differentiable t)
  · exact (Psi1_fifth_differentiable t)
  · exact (Psi1_sixth_differentiable t)
  · exact (Psi1_seventh_differentiable t)

/-- Iterate the common row recurrence on the genuine open logarithm patch. -/
theorem thetaNormJetSection_iterated
    (f : ℕ → ℝ → ℝ) (N : ℕ)
    (hf : ∀ m < N, ∀ t : ℝ, HasDerivAt (f m) (f (m+1) t) t)
    (x t u : ℝ) (m k : ℕ) (hk : k ≤ 4) (hm : m+k ≤ N)
    (hu : 0 < 1+x*u) :
    iteratedDeriv k (fun z => thetaNormGauge x z *
      f m (t+thetaNormShift x z)) u = thetaNormJetSection f x t m k u := by
  induction k generalizing u with
  | zero => simp only [iteratedDeriv_zero, thetaNormJetSection_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hopen : IsOpen {z : ℝ | 0 < 1+x*z} :=
        isOpen_lt continuous_const (by fun_prop)
      have heq : iteratedDeriv k (fun z => thetaNormGauge x z *
          f m (t+thetaNormShift x z)) =ᶠ[𝓝 u] thetaNormJetSection f x t m k := by
        filter_upwards [hopen.mem_nhds hu] with z hz
        exact ih (by omega) (by omega) z hz
      rw [Filter.EventuallyEq.deriv_eq heq]
      exact (thetaNormJetSection_hasDerivAt f N hf x t u m k (by omega)
        (by omega) (ne_of_gt hu)).deriv

noncomputable def thetaNormRow (x : ℝ) (i l : ℕ) : ℝ :=
  thetaNormJetPolynomial (1/x) (x/4) i l

theorem thetaNormRow_diag (x : ℝ) (i : ℕ) (hi : i ≤ 4) :
    thetaNormRow x i i = (x/4)^i := by
  interval_cases i <;> simp [thetaNormRow, thetaNormJetPolynomial]

theorem thetaNormRow_above (x : ℝ) (i l : ℕ) (hi : i ≤ 4) (hil : i < l) :
    thetaNormRow x i l = 0 := by
  interval_cases i <;>
    (rcases l with _ | l; · omega) <;>
    first | rfl | (rcases l with _ | l; · omega) <;>
    first | rfl | (rcases l with _ | l; · omega) <;>
    first | rfl | (rcases l with _ | l; · omega) <;>
    first | rfl | (rcases l with _ | l; · omega) <;> rfl

theorem thetaNormJetSection_origin (f : ℕ → ℝ → ℝ) (x t : ℝ) (m k : ℕ) :
    thetaNormJetSection f x t m k 0 =
      ∑ l ∈ Finset.range (k+1), thetaNormRow x k l * f (m+l) t := by
  simp [thetaNormJetSection, thetaNormGauge, thetaNormShift, thetaNormSlope, thetaNormRow]


end W5
