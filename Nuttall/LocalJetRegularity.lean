import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace Nuttall

open Filter Set
open scoped Topology BigOperators ContDiff

private theorem locallyLipschitzOn_comp_pair {S : Set ℝ} {f g : ℝ → ℝ} {H : ℝ × ℝ → ℝ}
    (hf : LocallyLipschitzOn S f) (hg : LocallyLipschitzOn S g)
    (hH : ∀ x ∈ S, ContDiffAt ℝ 1 H (f x, g x)) :
    LocallyLipschitzOn S (fun x => H (f x, g x)) := by
  apply locallyLipschitzOn_iff_restrict.2
  let P (x : S) := (f x, g x)
  have hP : LocallyLipschitz P := hf.restrict.prodMk hg.restrict
  intro x
  obtain ⟨K, V, hV, hKV⟩ := (hH x x.prop).exists_lipschitzOnWith
  obtain ⟨L, U, hU, hLU⟩ := hP x
  refine ⟨K * L, U ∩ P ⁻¹' V, inter_mem hU (hP.continuous.continuousAt hV), ?_⟩
  exact hKV.comp (hLU.mono inter_subset_left) (mapsTo_preimage P V |>.mono_left inter_subset_right)

private theorem locallyLipschitzOn_mul_real {S : Set ℝ} {f g : ℝ → ℝ}
    (hf : LocallyLipschitzOn S f) (hg : LocallyLipschitzOn S g) :
    LocallyLipschitzOn S (fun x => f x * g x) :=
  locallyLipschitzOn_comp_pair (H := fun p => p.1 * p.2) hf hg (by intro x hx; fun_prop)

private theorem locallyLipschitzOn_div_real {S : Set ℝ} {f g : ℝ → ℝ}
    (hf : LocallyLipschitzOn S f) (hg : LocallyLipschitzOn S g) (h0 : ∀ x ∈ S, g x ≠ 0) :
    LocallyLipschitzOn S (fun x => f x / g x) :=
  locallyLipschitzOn_comp_pair (H := fun p => p.1 / p.2) hf hg (fun x hx =>
    contDiffAt_fst.div contDiffAt_snd (h0 x hx))

private theorem locallyLipschitzOn_finsetSum_real {ι : Type*} {S : Set ℝ}
    (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, LocallyLipschitzOn S (f i)) :
    LocallyLipschitzOn S (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LocallyLipschitz.const (α := ℝ) (0:ℝ)).locallyLipschitzOn
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private theorem locallyLipschitzOn_congr_real {S : Set ℝ} {f g : ℝ → ℝ}
    (hg : LocallyLipschitzOn S g) (h : EqOn f g S) :
    LocallyLipschitzOn S f := by
  apply locallyLipschitzOn_iff_restrict.2
  have heq : S.domRestrict f = S.domRestrict g := funext (fun x => h x.prop)
  rw [heq]
  exact hg.restrict

/-- Division by a nonvanishing function preserves local Lipschitz regularity
of all derivatives through the last continuously differentiable order. -/
theorem locallyLipschitzOn_iteratedDeriv_div {S : Set ℝ} (hS : IsOpen S)
    {f d : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f S) (hd : ContDiffOn ℝ n d S) (h0 : ∀ x ∈ S, d x ≠ 0)
    (hLf : ∀ m ≤ n, LocallyLipschitzOn S (iteratedDeriv m f))
    (hLd : ∀ m ≤ n, LocallyLipschitzOn S (iteratedDeriv m d)) :
    ∀ m ≤ n, LocallyLipschitzOn S (iteratedDeriv m (fun x => f x / d x)) := by
  let q (x : ℝ) := f x / d x
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hmn
    let g (i : ℕ) (x : ℝ) :=
      (m.choose (i+1) : ℝ) * iteratedDeriv (i+1) d x * iteratedDeriv (m-(i+1)) q x
    have hLg : LocallyLipschitzOn S (fun x => ∑ i ∈ Finset.range m, g i x) := by
      apply locallyLipschitzOn_finsetSum_real
      intro i hi
      have him := Finset.mem_range.1 hi
      exact locallyLipschitzOn_mul_real
        (locallyLipschitzOn_mul_real ((LocallyLipschitz.const _).locallyLipschitzOn)
          (hLd (i+1) (by omega)))
        (ih (m-(i+1)) (by omega) (by omega))
    have hLd0 : LocallyLipschitzOn S d := by
      simpa only [iteratedDeriv_zero] using hLd 0 (Nat.zero_le n)
    have hL := locallyLipschitzOn_div_real ((hLf m hmn).sub hLg) hLd0 h0
    apply locallyLipschitzOn_congr_real hL
    intro x hx
    change iteratedDeriv m q x =
      (iteratedDeriv m f x - ∑ i ∈ Finset.range m, g i x) / d x
    have heq : f =ᶠ[𝓝 x] d * q := by
      filter_upwards [hS.mem_nhds hx] with y hy
      change f y = d y * (f y / d y)
      field_simp [h0 y hy]
    have hfd : ContDiffAt ℝ m f x := (hS.contDiffOn_iff.1 hf hx).of_le (by exact_mod_cast hmn)
    have hdd : ContDiffAt ℝ m d x := (hS.contDiffOn_iff.1 hd hx).of_le (by exact_mod_cast hmn)
    have hqd : ContDiffAt ℝ m q x := hfd.div hdd (h0 x hx)
    have hmul := heq.iteratedDeriv_eq m
    rw [iteratedDeriv_mul hdd hqd, Finset.sum_range_succ'] at hmul
    simp only [Nat.choose_zero_right, Nat.cast_one, iteratedDeriv_zero, Nat.sub_zero, one_mul] at hmul
    change iteratedDeriv m f x = (∑ i ∈ Finset.range m, g i x) +
      d x * iteratedDeriv m q x at hmul
    apply (eq_div_iff (h0 x hx)).2
    linarith only [hmul]

#print axioms locallyLipschitzOn_iteratedDeriv_div

end Nuttall
