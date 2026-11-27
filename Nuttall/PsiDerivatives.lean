import Nuttall.TailIteration

namespace Nuttall

/-- Lowering the level by one differentiates a tail integral. -/
theorem psi_succ_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (psi (m+1)) (-psi m t) t :=
  tailIntegral_hasDerivAt (psi_continuous m) (psi_integrableOn m) t

theorem auxiliary_iterate_succ_hasDerivAt (m : ℕ) (t : ℝ) :
    HasDerivAt (tailIterate auxiliaryTheta (m+1))
      (-tailIterate auxiliaryTheta m t) t :=
  tailIntegral_hasDerivAt (tailIterate_auxiliary_continuous m)
    (tailIterate_auxiliary_integrableOn m) t

theorem iteratedDeriv_psi {k m : ℕ} (hkm : k ≤ m) (t : ℝ) :
    iteratedDeriv k (psi m) t = (-1 : ℝ)^k * psi (m-k) t := by
  induction k generalizing m t with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ m := by omega
    have hfun : iteratedDeriv k (psi m) =
        fun x => (-1 : ℝ)^k * psi (m-k) x := funext (ih hk)
    rw [iteratedDeriv_succ, hfun]
    have hm : m-k = (m-(k+1))+1 := by omega
    rw [hm]
    rw [((psi_succ_hasDerivAt (m-(k+1)) t).const_mul ((-1 : ℝ)^k)).deriv]
    rw [pow_succ]
    ring

/-- Wronskian entries up to the available levels of integration. -/
theorem wronskian_psi_eq_det {p m : ℕ} (hm : 2*(p-1) ≤ m) (t : ℝ) :
    wronskian (psi m) p t =
      (Matrix.of (fun (i j : Fin p) =>
        (-1 : ℝ)^(i.val+j.val) * psi (m-(i.val+j.val)) t)).det := by
  unfold wronskian
  congr 1
  apply Matrix.ext
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  exact iteratedDeriv_psi (by omega) t

#print axioms iteratedDeriv_psi
#print axioms wronskian_psi_eq_det

end Nuttall
