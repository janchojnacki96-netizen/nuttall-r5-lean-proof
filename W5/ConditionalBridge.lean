import W5.FiniteCore
import W5.Statement

namespace W5

def FivePivotsGood (p : Fin 5 → ℝ) : Prop :=
  PivotSigns (p 0) (p 1) (p 2) (p 3) (p 4)

/-- Conditional only: the local analytic estimates and scaling remain premises. -/
theorem mainClaim_if_certificate_sound
    (pivot : ℝ → Fin 5 → ℝ)
    (scaleFactor : ℝ → Fin 5 → ℝ)
    (hx : ∀ t : ℝ, 0 ≤ t →
      0 ≤ xOfT t ∧ xOfT t ≤ (145 : ℝ) / 256)
    (hlocal : ∀ x : ℝ, Chain 0 endpoints x → FivePivotsGood (pivot x))
    (hscale : ∀ t : ℝ, 0 ≤ t →
      0 < scaleFactor t 0 ∧ 0 < scaleFactor t 1 ∧
      0 < scaleFactor t 2 ∧ 0 < scaleFactor t 3 ∧
      0 < scaleFactor t 4)
    (hdet : ∀ t : ℝ, 0 ≤ t →
      W 1 t = scaleFactor t 0 * pivot (xOfT t) 0 ∧
      W 2 t = scaleFactor t 1 * (pivot (xOfT t) 0 * pivot (xOfT t) 1) ∧
      W 3 t = scaleFactor t 2 *
        (pivot (xOfT t) 0 * pivot (xOfT t) 1 * pivot (xOfT t) 2) ∧
      W 4 t = scaleFactor t 3 *
        (pivot (xOfT t) 0 * pivot (xOfT t) 1 *
         pivot (xOfT t) 2 * pivot (xOfT t) 3) ∧
      W 5 t = scaleFactor t 4 *
        (pivot (xOfT t) 0 * pivot (xOfT t) 1 *
         pivot (xOfT t) 2 * pivot (xOfT t) 3 *
         pivot (xOfT t) 4)) :
    MainClaim := by
  intro t ht
  obtain ⟨hx0, hxmax⟩ := hx t ht
  have hp : FivePivotsGood (pivot (xOfT t)) :=
    hlocal (xOfT t) (cover_51 (xOfT t) hx0 hxmax)
  have hprod := productSigns_of_pivotSigns hp
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hprod
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hscale t ht
  obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hdet t ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hd1]; exact mul_pos hs1 hp1
  · rw [hd2]; exact mul_neg_of_pos_of_neg hs2 hp2
  · rw [hd3]; exact mul_neg_of_pos_of_neg hs3 hp3
  · rw [hd4]; exact mul_pos hs4 hp4
  · rw [hd5]; exact mul_pos hs5 hp5

end W5
