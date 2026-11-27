import Nuttall.PhiCompactNormalization
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Nuttall

open scoped BigOperators

private theorem phiCompactGaussian_abs_le {X q : ℝ}
    (hX : 3 ≤ X) (hq : 1 ≤ q) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    |phiCompactGaussian X q i j| ≤ 4*(q*X)^6 := by
  have hX₀ : 0 ≤ X := by linarith
  have he : 1 ≤ q*X := by
    calc
      _ ≤ X := by linarith
      _ = 1*X := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hq hX₀
  have ha : |-(q-1)*X| ≤ q*X := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hq), abs_of_nonneg hX₀]
    exact mul_le_mul_of_nonneg_right (by linarith) hX₀
  have hb : |-q*X| = q*X := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ q), abs_of_nonneg hX₀]
  have hbound (z : ℝ) (hz : |z| ≤ q*X) (m : ℕ) :
      |z^m / (m.factorial:ℝ)| ≤ (q*X)^m := by
    have hf : (1:ℝ) ≤ (m.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [abs_div, abs_pow, abs_of_pos (by linarith : (0:ℝ) < m.factorial)]
    exact (div_le_self (by positivity) hf).trans (pow_le_pow_left₀ (abs_nonneg _) hz _)
  unfold phiCompactGaussian
  calc
    _ ≤ ∑ k ∈ Finset.range (min i j + 1),
        |((-(q-1)*X)^(i-k) / ((i-k).factorial:ℝ)) *
          ((-(q-1)*X)^(j-k) / ((j-k).factorial:ℝ)) * ((-q*X)^k / (k.factorial:ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (min i j + 1), (q*X)^6 := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [abs_mul]
      have hmul := mul_le_mul (hbound _ ha (i-k)) (hbound _ ha (j-k))
        (abs_nonneg _) (by positivity : 0 ≤ (q*X)^(i-k))
      have hall := mul_le_mul hmul (hbound _ hb.le k) (abs_nonneg _)
        (by positivity : 0 ≤ (q*X)^(i-k) * (q*X)^(j-k))
      refine hall.trans ?_
      rw [← pow_add, ← pow_add]
      exact pow_le_pow_right₀ he (by
        have hk' := Finset.mem_range.mp hk
        omega)
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show min i j + 1 ≤ 4 by omega))
        (by positivity)

private theorem phiCompactPolynomial_abs_le {X q : ℝ}
    (hX : 3 ≤ X) (hq : 1 ≤ q) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    |phiCompactPolynomial X q i j| ≤ 32*q*(q*X)^7 := by
  have hq₀ : 0 ≤ q := by linarith
  have hX₀ : 0 ≤ X := by linarith
  have hqx : 3 ≤ q*X :=
    hX.trans (by simpa using mul_le_mul_of_nonneg_right hq hX₀)
  have hg := phiCompactGaussian_abs_le hX hq hi hj
  have h₁ : |if i = 0 then 0 else phiCompactGaussian X q (i-1) j| ≤ 4*(q*X)^6 := by
    split <;> first | simpa using (show 0 ≤ 4*(q*X)^6 by positivity) |
      exact phiCompactGaussian_abs_le hX hq (by omega) hj
  have h₂ : |if j = 0 then 0 else phiCompactGaussian X q i (j-1)| ≤ 4*(q*X)^6 := by
    split <;> first | simpa using (show 0 ≤ 4*(q*X)^6 by positivity) |
      exact phiCompactGaussian_abs_le hX hq hi (by omega)
  have h₃ : |if i = 0 ∨ j = 0 then 0 else phiCompactGaussian X q (i-1) (j-1)| ≤ 4*(q*X)^6 := by
    split <;> first | simpa using (show 0 ≤ 4*(q*X)^6 by positivity) |
      exact phiCompactGaussian_abs_le hX hq (by omega) (by omega)
  have hshift := (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃)
  have hfac : |2*q*X-3| ≤ 2*q*X := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 2*q*X-3)]
    linarith
  unfold phiCompactPolynomial
  rw [abs_mul, abs_of_nonneg hq₀]
  apply (mul_le_mul_of_nonneg_left (abs_add_le _ _) hq₀).trans
  simp only [abs_mul]
  simp only [abs_of_nonneg hq₀, abs_of_nonneg hX₀, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  refine (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul hfac hg (abs_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_left hshift (by positivity))) hq₀).trans ?_
  ring_nf
  exact le_rfl

private theorem power_mul_gaussian_le_at_start (X B d : ℝ) (hB : 0 < B)
    (hX : B ≤ X) (hd : 7/B ≤ d) :
    X^7 * Real.exp (-d*X) ≤ B^7 * Real.exp (-d*B) := by
  have hz : X/B ≤ Real.exp ((X-B)/B) := by
    convert Real.add_one_le_exp ((X-B)/B) using 1
    field_simp
    ring
  have h := pow_le_pow_left₀ (div_nonneg (hB.le.trans hX) hB.le) hz 7
  rw [div_pow, ← Real.exp_nat_mul] at h
  have hpow : X^7 ≤ B^7 * Real.exp (7*((X-B)/B)) := by
    norm_num only [Nat.cast_ofNat] at h
    simpa only [mul_comm] using (div_le_iff₀ (pow_pos hB _)).1 h
  have he : 7*((X-B)/B) + -d*X ≤ -d*B := by
    have hD := mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hX)
    calc
      _ = 7/B*(X-B) - d*X := by ring
      _ ≤ _ := by linarith only [hD]
  calc
    _ ≤ (B^7*Real.exp (7*((X-B)/B)))*Real.exp (-d*X) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = B^7*Real.exp (7*((X-B)/B) + -d*X) := by rw [Real.exp_add, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

private theorem phiCompactTerm_le_geometric {X B ρ : ℝ} {N i j : ℕ} (hB : 3 ≤ B) (hX : B ≤ X)
    (hN : 2 ≤ N) (hi : i < 4) (hj : j < 4) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hExp : Real.exp (-B) ≤ ρ) (hStep : (2:ℝ)^16 * ρ^(2*N+1) ≤ 1/2) (k : ℕ) :
    |phiCompactTerm X i j (N+k)| ≤
      (32*B^7*(N:ℝ)^16*ρ^(N^2-1))*(1/2:ℝ)^k := by
  have hB₀ : 0 < B := by linarith
  have hmajor (l : ℕ) (hl : N ≤ l) :
      |phiCompactTerm X i j l| ≤ 32*B^7*(l:ℝ)^16*ρ^(l^2-1) := by
    have hlR : (2:ℝ) ≤ l := by exact_mod_cast hN.trans hl
    have h₁ : (1:ℝ) ≤ (l:ℝ)^2 := by nlinarith only [hlR, sq_nonneg ((l:ℝ)-2)]
    have hd : 7/B ≤ (l:ℝ)^2-1 := by
      apply (div_le_iff₀ hB₀).2
      nlinarith only [hlR, hB, sq_nonneg ((l:ℝ)-2),
        mul_nonneg (sub_nonneg.mpr hB) (show 0 ≤ (l:ℝ)^2-1 by linarith)]
    have hl2 : 1 ≤ l^2 := by exact_mod_cast h₁
    have hex : Real.exp (-((l:ℝ)^2-1)*B) ≤ ρ^(l^2-1) := by
      rw [show -((l:ℝ)^2-1)*B = ((l^2-1:ℕ):ℝ)*(-B) by
        rw [Nat.cast_sub hl2, Nat.cast_one, Nat.cast_pow]; ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le hExp _
    unfold phiCompactTerm
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (32*(l:ℝ)^2*((l:ℝ)^2*X)^7)*Real.exp (-((l:ℝ)^2-1)*X) :=
        mul_le_mul_of_nonneg_right (phiCompactPolynomial_abs_le (hB.trans hX) h₁ hi hj)
          (Real.exp_pos _).le
      _ = (32*(l:ℝ)^16)*(X^7*Real.exp (-((l:ℝ)^2-1)*X)) := by ring
      _ ≤ (32*(l:ℝ)^16)*(B^7*Real.exp (-((l:ℝ)^2-1)*B)) :=
        mul_le_mul_of_nonneg_left (power_mul_gaussian_le_at_start X B _ hB₀ hX hd) (by positivity)
      _ = 32*B^7*(l:ℝ)^16*Real.exp (-((l:ℝ)^2-1)*B) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hex (by positivity)
  have hseq (l : ℕ) (hl : N ≤ l) :
      ((l+1:ℕ):ℝ)^16*ρ^((l+1)^2-1) ≤ ((l:ℝ)^16*ρ^(l^2-1))/2 := by
    have hN' : 2 ≤ l := hN.trans hl
    have hlR : (1:ℝ) ≤ l := by exact_mod_cast (show 1 ≤ l by omega)
    have he : (l+1)^2-1 = (l^2-1)+(2*l+1) := by
      have hpow : 1 ≤ l^2 := Nat.one_le_pow _ _ (by omega)
      have h : (l+1)^2 = l^2+(2*l+1) := by ring
      omega
    have hρ : ρ^(2*l+1) ≤ ρ^(2*N+1) := pow_le_pow_of_le_one hρ₀ hρ₁ (by omega)
    have hp : ((l+1:ℕ):ℝ)^16 ≤ (2*(l:ℝ))^16 :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) _
    rw [he, pow_add]
    calc
      _ ≤ (2*(l:ℝ))^16*(ρ^(l^2-1)*ρ^(2*N+1)) :=
        mul_le_mul hp (mul_le_mul_of_nonneg_left hρ (by positivity)) (by positivity) (by positivity)
      _ = ((l:ℝ)^16 * ρ^(l^2-1)) * ((2:ℝ)^16 * ρ^(2*N+1)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hStep (by positivity)).trans_eq (by ring)
  have hind (m : ℕ) : ((N+m:ℕ):ℝ)^16 * ρ^((N+m)^2-1) ≤
      (N:ℝ)^16 * ρ^(N^2-1) * (1/2:ℝ)^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        _ ≤ (((N+m:ℕ):ℝ)^16 * ρ^((N+m)^2-1))/2 := hseq (N+m) (by omega)
        _ ≤ _ := by
          rw [pow_succ (1/2:ℝ) m]
          exact (div_le_div_of_nonneg_right ih (show (0:ℝ) ≤ 2 by norm_num)).trans_eq (by ring)
  refine (hmajor (N+k) (by omega)).trans ?_
  calc
    _ = (32*B^7)*(((N+k:ℕ):ℝ)^16*ρ^((N+k)^2-1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hind k) (by positivity) |>.trans_eq (by ring)

private theorem phiCompactTail_generic {X B ρ : ℝ} {N i j : ℕ} (hB : 3 ≤ B) (hX : B ≤ X)
    (hN : 2 ≤ N) (hi : i < 4) (hj : j < 4) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hExp : Real.exp (-B) ≤ ρ) (hStep : (2:ℝ)^16 * ρ^(2*N+1) ≤ 1/2) :
    |∑' k, phiCompactTerm X i j (N+k)| ≤ 64*B^7*(N:ℝ)^16*ρ^(N^2-1) := by
  let C := 32*B^7*(N:ℝ)^16*ρ^(N^2-1)
  have hg : Summable (fun k : ℕ => (1/2:ℝ)^k) :=
    summable_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs])
  have hG := hg.mul_left C
  have hcomp (k : ℕ) : ‖phiCompactTerm X i j (N+k)‖ ≤ C*(1/2:ℝ)^k := by
    simpa only [Real.norm_eq_abs, C] using phiCompactTerm_le_geometric hB hX hN hi hj hρ₀ hρ₁
      hExp hStep k
  have hs := hG.of_nonneg_of_le (fun k => norm_nonneg (phiCompactTerm X i j (N+k))) hcomp
  calc
    _ ≤ ∑' k, ‖phiCompactTerm X i j (N+k)‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ, C*(1/2:ℝ)^k := hs.tsum_le_tsum hcomp hG
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num [Real.norm_eq_abs] : ‖(1/2:ℝ)‖ < 1)]
      dsimp [C]
      ring_nf

/-- The omitted terms of the compact rank-four checker fit in a small uniform interval. -/
theorem phiCompactTail_abs_le {X : ℝ} (hX : 3 ≤ X) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    |∑' k, phiCompactTerm X i j (4+k)| ≤ (1:ℝ)/1000 := by
  have he : Real.exp (-(3:ℝ)) ≤ 1/16 := by
    rw [Real.exp_neg, show (3:ℝ) = (3:ℕ)*(1:ℝ) by norm_num, Real.exp_nat_mul]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ) < 16)
      (show (16:ℝ) ≤ (Real.exp 1)^3 from
        (by norm_num : (16:ℝ) ≤ (2.7:ℝ)^3).trans
          (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 3))
  exact (phiCompactTail_generic (N := 4) (by norm_num : (3:ℝ) ≤ 3) hX (by decide) hi hj
    (by norm_num : (0:ℝ) ≤ 1/16) (by norm_num) he (by norm_num)).trans (by norm_num)

/-- Stronger suppression on the tail of the half-line, beginning at the second square. -/
theorem phiCompactFarTail_abs_le {X : ℝ} (hX : 16 ≤ X) {i j : ℕ} (hi : i < 4) (hj : j < 4) :
    |∑' k, phiCompactTerm X i j (2+k)| ≤ (1:ℝ)/10000 := by
  have he : Real.exp (-(16:ℝ)) ≤ 1/2^22 := by
    rw [Real.exp_neg, show (16:ℝ) = (16:ℕ)*(1:ℝ) by norm_num, Real.exp_nat_mul]
    simpa only [one_div] using inv_anti₀ (by positivity : (0:ℝ) < 2^22)
      (show (2:ℝ)^22 ≤ (Real.exp 1)^16 from
        (by norm_num : (2:ℝ)^22 ≤ (2.7:ℝ)^16).trans
          (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 16))
  exact (phiCompactTail_generic (N := 2) (by norm_num : (3:ℝ) ≤ 16) hX (by decide) hi hj
    (by norm_num : (0:ℝ) ≤ 1/2^22) (by norm_num) he (by norm_num)).trans (by norm_num)

#print axioms phiCompactTail_abs_le
#print axioms phiCompactFarTail_abs_le

end Nuttall
