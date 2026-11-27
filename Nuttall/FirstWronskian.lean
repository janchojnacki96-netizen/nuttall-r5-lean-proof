import Nuttall.TailIteration
import W5.PhiPositivity

namespace Nuttall

open MeasureTheory Set

/-- Iterated tails of the theta kernel are strictly positive on the positive half-line. -/
theorem psi_pos (m : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 < psi m t := by
  induction m generalizing t with
  | zero => exact W5.Phi_pos t ht
  | succ m ih =>
    change 0 < ∫ s in Ici t, psi m s
    have hae : 0 ≤ᵐ[volume.restrict (Ici t)] psi m :=
      (ae_restrict_mem measurableSet_Ici).mono (fun s hs => (ih s (ht.trans hs)).le)
    apply (integral_pos_iff_support_of_nonneg_ae hae (psi_integrableOn m t)).2
    have hs : Ici t ⊆ Function.support (psi m) :=
      fun s hs => (ih s (ht.trans hs)).ne'
    calc
      0 < (volume.restrict (Ici t)) (Ici t) := by
        rw [Measure.restrict_apply measurableSet_Ici, inter_self, Real.volume_Ici]
        exact top_pos
      _ ≤ _ := measure_mono hs

/-- The order-one case needed by the upper-bound proof holds at every integration level. -/
theorem signed_wronskian_order_one_pos (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 < (-1 : ℝ)^(1*(1-1)/2) * wronskian (psi m) 1 t := by
  simpa [wronskian, Matrix.det_fin_one] using psi_pos m t ht

#print axioms signed_wronskian_order_one_pos

end Nuttall
