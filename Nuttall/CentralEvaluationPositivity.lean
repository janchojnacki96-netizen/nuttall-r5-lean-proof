import Nuttall.EvaluationDeterminant
import Nuttall.LocalJetRegularity
import Nuttall.WronskianReduction

namespace Nuttall

open Set
open scoped ContDiff

/-- The evaluation determinant criterion with a countable exceptional set.
Only the highest Wronskian can lose its strict sign there. The initial functions
have locally Lipschitz derivatives through the last continuous order. -/
theorem det_eval_pos_of_familyWronskians {n : ℕ} {a b : ℝ} {S : Set ℝ}
    (hS : S.Countable) (f : Fin (n+1) → ℝ → ℝ)
    (hcont : ∀ j (m : ℕ), m+1 ≤ n → ContDiffOn ℝ m (f j) (Ioo a b))
    (hjet : ∀ j (m : ℕ), m+1 ≤ n → LocallyLipschitzOn (Ioo a b) (iteratedDeriv m (f j)))
    (hsmooth : ∀ j x, x ∈ Ioo a b → x ∉ S → ContDiffAt ℝ n (f j) x)
    (hW : ∀ k (hk : k ≤ n) x, x ∈ Ioo a b → (k = n → x ∉ S) →
      0 < familyWronskian (fun j : Fin (k+1) => f (j.castLE (Nat.succ_le_succ hk))) x)
    (u : Fin (n+1) → ℝ) (hu : StrictMono u) (huJ : ∀ i, u i ∈ Ioo a b)
    (huS : n = 0 → ∀ i, u i ∉ S) :
    0 < (Matrix.of (fun i j => f j (u i))).det := by
  induction n with
  | zero =>
    have h0 := hW 0 le_rfl (u 0) (huJ 0) (fun _ => huS rfl 0)
    simpa [familyWronskian, Matrix.det_fin_one] using h0
  | succ n ih =>
    have h0 (x : ℝ) (hx : x ∈ Ioo a b) : 0 < f 0 x := by
      have := hW 0 (by omega) x hx (by omega)
      simpa [familyWronskian, Matrix.det_fin_one] using this
    let q (j : Fin (n+1)) (x : ℝ) := f j.succ x / f 0 x
    let g (j : Fin (n+1)) := deriv (q j)
    have hne (x : ℝ) (hx : x ∈ Ioo a b) : f 0 x ≠ 0 := (h0 x hx).ne'
    have hqcont (j : Fin (n+1)) (m : ℕ) (hm : m+1 ≤ n+1) :
        ContDiffOn ℝ m (q j) (Ioo a b) :=
      (hcont j.succ m hm).div (hcont 0 m hm) hne
    have hqjet (j : Fin (n+1)) (m : ℕ) (hm : m+1 ≤ n+1) :
        LocallyLipschitzOn (Ioo a b) (iteratedDeriv m (q j)) :=
      locallyLipschitzOn_iteratedDeriv_div isOpen_Ioo
        (hcont j.succ m hm) (hcont 0 m hm) hne
        (fun k hk => hjet j.succ k (by omega)) (fun k hk => hjet 0 k (by omega)) m le_rfl
    apply det_eval_pos_of_reduced f u hu (fun i => h0 (u i) (huJ i)) hS
    · intro i j
      have hle : u i.castSucc ≤ u i.succ := hu.monotone (by simp [Fin.le_def])
      have hsub : uIcc (u i.castSucc) (u i.succ) ⊆ Ioo a b := by
        rw [uIcc_of_le hle]
        intro x hx
        exact ⟨(huJ i.castSucc).1.trans_le hx.1, hx.2.trans_lt (huJ i.succ).2⟩
      have hlip : LocallyLipschitzOn (Ioo a b) (q j) := by
        simpa only [iteratedDeriv_zero] using hqjet j 0 (by omega)
      obtain ⟨K, hK⟩ := (hlip.mono hsub).exists_lipschitzOnWith_of_compact isCompact_uIcc
      exact hK.absolutelyContinuousOnInterval
    · intro v hv hvI hvS
      have hvJ (i : Fin (n+1)) : v i ∈ Ioo a b :=
        ⟨(huJ i.castSucc).1.trans (hvI i).1, (hvI i).2.trans_lt (huJ i.succ).2⟩
      change 0 < (Matrix.of (fun i j => g j (v i))).det
      apply ih g _ _ _ _ v hv hvJ (fun _ => hvS)
      · intro j m hm
        apply isOpen_Ioo.contDiffOn_iff.2
        intro x hx
        exact (isOpen_Ioo.contDiffOn_iff.1 (hqcont j (m+1) (by omega)) hx).derivWithin
          (by push_cast; rfl)
      · intro j m hm
        change LocallyLipschitzOn (Ioo a b) (iteratedDeriv m (deriv (q j)))
        rw [← iteratedDeriv_succ']
        exact hqjet j (m+1) (by omega)
      · intro j x hx hxS
        exact ((hsmooth j.succ x hx hxS).div (hsmooth 0 x hx hxS) (hne x hx)).derivWithin
          (by push_cast; rfl)
      · intro k hk x hx hxS
        let F (j : Fin (k+2)) := f (j.castLE (by omega))
        have hFd (j : Fin (k+2)) : ContDiffAt ℝ (↑(k+1) : ℕ∞ω) (F j) x := by
          by_cases hkn : k = n
          · subst k
            exact hsmooth _ x hx (hxS rfl)
          · exact isOpen_Ioo.contDiffOn_iff.1 (hcont _ (k+1) (by omega)) hx
        have hsign := hW (k+1) (by omega) x hx (fun he => hxS (by omega))
        have hred := familyWronskian_eq_pow_mul_reduced F x hFd (hne x hx)
        change 0 < familyWronskian F x at hsign
        rw [hred] at hsign
        exact pos_of_mul_pos_right hsign (pow_nonneg (h0 x hx).le _)

#print axioms det_eval_pos_of_familyWronskians

end Nuttall
