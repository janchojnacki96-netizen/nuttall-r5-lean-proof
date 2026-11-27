import Nuttall.ShiftCriticalCutoff
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Nuttall

open Filter

/-- The bound for the relative mass of a single outside slice in §4.1. -/
noncomputable def shiftRelativeTailRatio (r p : ℕ) (X : ℝ) : ℝ :=
  let m := 2*r
  let L := m-p
  16*(m:ℝ)*p*2^p*8^(L-1)*(192*(p:ℝ))^(2*p)*m.factorial *
    Real.exp (-X*(Real.exp (4*shiftCriticalCutoff r)/2-Real.exp 1))

private theorem shiftRelativeTail_prefactor_le (m p : ℕ) (hm : 3 ≤ m) (hp : 2*p ≤ m) :
    (p:ℝ)*(16*(m:ℝ)*p*2^p*8^(m-p-1)*(192*(p:ℝ))^(2*p)*m.factorial)
      ≤ (192*(m:ℝ))^(4*m) := by
  let D := 192*(m:ℝ)
  have hm₀ : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hp₀ : (p:ℝ) ≤ m := by exact_mod_cast (show p ≤ m by omega)
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hD16 : 16 ≤ D := by dsimp [D]; linarith
  have hmD : (m:ℝ) ≤ D := by dsimp [D]; linarith
  have hpD : (p:ℝ) ≤ D := hp₀.trans hmD
  have htwo : (2:ℝ)^p ≤ D^p := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have height : (8:ℝ)^(m-p-1) ≤ D^(m-p-1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hp192 : (192*(p:ℝ))^(2*p) ≤ D^(2*p) :=
    pow_le_pow_left₀ (by positivity) (by dsimp [D]; linarith) _
  have hfac : (m.factorial:ℝ) ≤ D^m :=
    (by exact_mod_cast m.factorial_le_pow : (m.factorial:ℝ) ≤ (m:ℝ)^m).trans
      (pow_le_pow_left₀ (by positivity) hmD _)
  calc
    _ ≤ D*(D*D*D*D^p*D^(m-p-1)*D^(2*p)*D^m) := by gcongr
    _ = D^(4+p+(m-p-1)+2*p+m) := by
      simp only [pow_add, pow_succ, pow_zero, one_mul]
      ring
    _ ≤ D^(4*m) := by
      exact pow_le_pow_right₀ hD (by omega)

theorem shiftRelativeTailRatio_mul_lt_quarter {r p : ℕ} (hr : 4 ≤ r) (hp : p ≤ r)
    {X : ℝ} (hX : Real.pi ≤ X) :
    (p:ℝ) * shiftRelativeTailRatio r p X < 1/4 := by
  let m := 2*r
  let A := (m:ℝ) * Real.log (192*(m:ℝ))
  have hmp : 2*p ≤ m := by dsimp [m]; omega
  have hm : (8:ℝ) ≤ m := by exact_mod_cast (show 8 ≤ m by dsimp [m]; omega)
  have hD : 0 < 192*(m:ℝ) := by linarith
  have hlog : 1 ≤ Real.log (192*(m:ℝ)) := by
    rw [← Real.exp_le_exp, Real.exp_log hD]
    linarith only [Real.exp_one_lt_three, hm]
  have hA : 8 ≤ A := by dsimp [A]; nlinarith only [hm, hlog]
  have hcut : Real.exp (4*shiftCriticalCutoff r) = 4*A := by
    unfold shiftCriticalCutoff
    rw [show 4*(Real.log (8*(r:ℝ)*Real.log (384*(r:ℝ)))/4) =
      Real.log (8*(r:ℝ)*Real.log (384*(r:ℝ))) by ring]
    have heq : 8*(r:ℝ)*Real.log (384*(r:ℝ)) = 4*A := by
      dsimp [A, m]
      push_cast
      rw [show 192*(2*(r:ℝ)) = 384*(r:ℝ) by ring]
      ring
    rw [heq, Real.exp_log (by linarith)]
  have hX3 : 3 ≤ X := Real.pi_gt_three.le.trans hX
  have hexp : Real.exp 1 ≤ A/2 := by linarith only [Real.exp_one_lt_three, hA]
  have hdecay : (9/2:ℝ)*A ≤ X*(2*A-Real.exp 1) := by
    calc
      _ = 3*((3/2:ℝ)*A) := by ring
      _ ≤ X*((3/2:ℝ)*A) := by gcongr
      _ ≤ X*(2*A-Real.exp 1) := by gcongr; linarith
  have hfac := shiftRelativeTail_prefactor_le m p (by dsimp [m]; omega) hmp
  have hpow : (192*(m:ℝ))^(4*m) = Real.exp (4*A) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hD]
    congr 1
    push_cast
    dsimp [A]
    ring
  have hsmall : Real.exp (-4) < 1/4 := by
    rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ (Real.exp_pos _)]
    linarith [Real.add_one_le_exp (4:ℝ)]
  calc
    _ = (p:ℝ)*(16*(m:ℝ)*p*2^p*8^(m-p-1)*(192*(p:ℝ))^(2*p)*m.factorial) *
        Real.exp (-X*(2*A-Real.exp 1)) := by
      rw [shiftRelativeTailRatio, hcut, show (4:ℝ)*A/2 = 2*A by ring]
      exact (mul_assoc _ _ _).symm
    _ ≤ Real.exp (4*A) * Real.exp (-X*(2*A-Real.exp 1)) :=
      mul_le_mul_of_nonneg_right (hfac.trans_eq hpow) (Real.exp_pos _).le
    _ ≤ Real.exp (-4) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith only [hdecay, hA]
    _ < 1/4 := hsmall

#print axioms shiftRelativeTailRatio_mul_lt_quarter

end Nuttall
