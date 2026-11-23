import W5.ThetaGammaWeightedExactTailBox

/-!
# Full TRUE theta Gamma moment from a recentered finite grid and exact tail

One Mathlib integral split and one real-sound QInterval sum combine:
* finite-grid quadratic/cubic signed Gamma interval enclosures;
* the exact exponential/incomplete-Gamma upper tail box.

The resulting computable QInterval bounds the ORIGINAL full
thetaAuditedOneWeightedMoment, for every k and rational y in [0,1],
under only rational endpoint checks and exact grid eligibility.
No per-k, per-cell, or per-bin analytic proofs remain.
-/

namespace W5
open MeasureTheory

/-- Generic soundness of appending a certified [H, infinity) tail
to a certified intervalIntegral on [0,H]. Reuses the existing
Mathlib integral_interval_add_Ioi lemma verbatim. -/
theorem thetaGammaFullMoment_containsReal_of_grid_and_tail
    (F : ℝ → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hInt : IntegrableOn F (Set.Ici (0:ℝ)) volume)
    (grid tail : QInterval)
    (hGrid : QInterval.ContainsReal grid
      (∫ w in (0:ℝ)..H, F w))
    (hTail : QInterval.ContainsReal tail
      (∫ w in Set.Ici H, F w ∂volume)) :
    QInterval.ContainsReal (QInterval.add grid tail)
      (∫ w in Set.Ici (0:ℝ), F w ∂volume) := by
  have h0 : IntegrableOn F (Set.Ioi (0:ℝ)) volume :=
    (integrableOn_Ici_iff_integrableOn_Ioi).1 hInt
  have hHInt : IntegrableOn F (Set.Ioi H) volume :=
    h0.mono_set (Set.Ioi_subset_Ioi hH)
  have hSplit :
      (∫ w in (0:ℝ)..H, F w) +
      (∫ w in Set.Ioi H, F w ∂volume) =
      (∫ w in Set.Ioi (0:ℝ), F w ∂volume) :=
    intervalIntegral.integral_interval_add_Ioi h0 hHInt
  rw [integral_Ici_eq_integral_Ioi] at hTail ⊢
  rw [← hSplit]
  exact QInterval.add_containsReal hGrid hTail

/-- One rationally computable enclosure for an original FULL
theta weighted Gamma moment: all finite w-bins plus one sharp tail. -/
def thetaGammaAutoFullMomentGridBox
    (steps k : ℕ) (y H : ℚ) (us : List ℚ) : QInterval :=
  QInterval.add
    ⟨(thetaGammaLowerGridBox k (y^2)
        (thetaGammaAutoRootGrid steps (y^2)) 0 us).lo,
      (thetaGammaUpperGridBox k (y^2)
        (thetaGammaAutoRootGrid steps (y^2)) 0 us).hi⟩
    (thetaGammaWeightedExactTailBox k y H)

/-- Genuine full original theta moment, uniformly for all moment
degrees k, with a fully computed exact rational interval output. -/
theorem thetaGammaAutoFullMomentGridBox_containsReal
    (steps k : ℕ) (y H : ℚ) (us : List ℚ)
    (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hGrid : thetaGammaAutoRootGridCheck
        steps (y^2) 0 us = true)
    (hLast : thetaGammaBinLast (0:ℝ)
       (us.map (fun z : ℚ => (z:ℝ))) = (H:ℝ))
    (hH : 0 ≤ H) (hHmax : H ≤ (1024:ℚ)/3)
    (hExp : 0 <
       (thetaBulkExpTaylorBox
          (QInterval.point (H/1024))).lo) :
    QInterval.ContainsReal
      (thetaGammaAutoFullMomentGridBox steps k y H us)
      (thetaAuditedOneWeightedMoment (y:ℝ) k) := by
  have hyR : (0:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy
  have hyR1 : (y:ℝ) ≤ 1 := by exact_mod_cast hy1
  have hHR : (0:ℝ) ≤ (H:ℝ) := by exact_mod_cast hH
  let F : ℝ → ℝ := fun w =>
    thetaGammaBinDensity k w *
      thetaGammaBinOriginalRoot ((y^2:ℚ):ℝ) w
  have hF (w : ℝ) :
      F w = (Real.exp (-w) *
        (1+w*(y:ℝ)^2)^((1:ℝ)/4))*w^k := by
    dsimp [F, thetaGammaBinDensity, thetaGammaBinOriginalRoot]
    simp only [Rat.cast_pow]
    have hArg : 1+(y:ℝ)^2*w = 1+w*(y:ℝ)^2 := by ring
    rw [hArg]
    ring
  have hFfun :
      F = (fun w : ℝ => (Real.exp (-w) *
        (1+w*(y:ℝ)^2)^((1:ℝ)/4))*w^k) :=
    funext hF
  have hInt0 :=
    thetaAuditedOneWeightedMoment_integrable_nonneg
      (y:ℝ) hyR hyR1 k
  have hInt : IntegrableOn F (Set.Ici (0:ℝ)) volume :=
    hInt0.congr_fun (fun w _ => (hF w).symm) measurableSet_Ici
  let G : QInterval :=
    ⟨(thetaGammaLowerGridBox k (y^2)
        (thetaGammaAutoRootGrid steps (y^2)) 0 us).lo,
      (thetaGammaUpperGridBox k (y^2)
        (thetaGammaAutoRootGrid steps (y^2)) 0 us).hi⟩
  let T : QInterval := thetaGammaWeightedExactTailBox k y H
  have hGG := thetaGammaAutoRootGrid_containsReal
    steps k (y^2) 0 us (sq_nonneg y) hGrid
  have hG : QInterval.ContainsReal G
      (∫ w in (0:ℝ)..(H:ℝ), F w) := by
    simpa only [G, F, hLast, Rat.cast_zero] using hGG
  have hT0 := thetaGammaWeightedExactTailBox_containsReal
    k y H hy hy1 hH hHmax hExp
  have hT : QInterval.ContainsReal T
      (∫ w in Set.Ici (H:ℝ), F w ∂volume) := by
    dsimp [T]
    rw [hFfun]
    exact hT0
  have hFinal := thetaGammaFullMoment_containsReal_of_grid_and_tail
    F (H:ℝ) hHR hInt G T hG hT
  have hFull :
      (∫ w in Set.Ici (0:ℝ), F w ∂volume) =
        thetaAuditedOneWeightedMoment (y:ℝ) k := by
    unfold thetaAuditedOneWeightedMoment
    rw [hFfun]
  rw [hFull] at hFinal
  exact hFinal

end W5
