import Nuttall.PsiCompactRemainder
import Nuttall.PhiJetInterval

namespace Nuttall

open W5
open scoped BigOperators

private def addSymmetricError (I : QInterval) (ε : ℚ) : QInterval :=
  QInterval.add I ⟨-ε, ε⟩

private theorem addSymmetricError_containsReal {I : QInterval} {ε : ℚ} {x y : ℝ}
    (hI : I.ContainsReal x) (hε : |y-x| ≤ (ε:ℝ)) :
    (addSymmetricError I ε).ContainsReal y := by
  have hd : (⟨-ε, ε⟩ : QInterval).ContainsReal (y-x) := by
    simpa only [QInterval.ContainsReal, Rat.cast_neg] using abs_le.mp hε
  have he : x + (y-x) = y := by ring
  simpa only [addSymmetricError, he] using QInterval.add_containsReal hI hd

/-- Add the common geometric tail to an exact interval for the retained terms. -/
def phiCompactJetBox (E X q : QInterval) (j N : ℕ) : QInterval :=
  addSymmetricError (phiJetPrefixBox E X q j N)
    (((j.factorial:ℚ) * 8^j) * (20000 * (9/25:ℚ)^(N^2) / (1-9/25)))

theorem phiCompactJetBox_containsReal {E X q : QInterval} {t : ℝ}
    (ht : 0 ≤ t) (ht₂ : t ≤ 2)
    (hE : E.ContainsReal (Real.exp t)) (hX : X.ContainsReal (Real.pi * Real.exp (4*t)))
    (hq : q.ContainsReal (Real.exp (-(Real.pi * Real.exp (4*t)))))
    (hX₀ : 0 ≤ X.lo) (hq₀ : 0 ≤ q.lo) (j N : ℕ) (hN : 1 ≤ N) :
    (phiCompactJetBox E X q j N).ContainsReal (iteratedDeriv j Phi t) := by
  apply addSymmetricError_containsReal (phiJetPrefixBox_containsReal hE hX hq hX₀ hq₀ j N)
  rw [iteratedDeriv_phi_eq_tsum,
    ← (auxiliaryWeightedSummand_summable (phiJetPolynomial j) t).sum_add_tsum_nat_add N,
    add_sub_cancel_left]
  simpa only [Real.norm_eq_abs, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_div, Rat.cast_sub, Rat.cast_one] using phiJet_geometric_tail j N hN ht ht₂

/-- Compute the preceding anchor using derivative intervals at the left end
and an enclosure of the integral at the right end. -/
def psiOnePanelBox (right : QInterval) (jets : ℕ → QInterval) (d : ℕ) (h : ℚ) : QInterval :=
  let poly := QInterval.sumBox (Finset.range d)
    (fun j => QInterval.mul (jets j) (QInterval.point (h^(j+1) / ((j+1).factorial:ℚ))))
  addSymmetricError (QInterval.add right poly)
    ((((d.factorial:ℚ) * 8^d) * 10^6) * h^(d+1) / ((d+1).factorial:ℚ))

/-- The contribution of a panel is independent of the enclosure to its right. -/
theorem psiOnePanelBox_eq_add_zero (right : QInterval) (jets : ℕ → QInterval)
    (d : ℕ) (h : ℚ) :
    psiOnePanelBox right jets d h = QInterval.add right (psiOnePanelBox (QInterval.point 0) jets d h) := by
  cases right
  simp [psiOnePanelBox, addSymmetricError, QInterval.add, QInterval.point, add_assoc]

theorem psiOnePanelBox_containsReal {right : QInterval} {jets : ℕ → QInterval}
    {a : ℝ} {h : ℚ} {d : ℕ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hb : a+(h:ℝ) ≤ 2)
    (hright : right.ContainsReal (psi 1 (a+(h:ℝ))))
    (hjets : ∀ j ∈ Finset.range d, (jets j).ContainsReal (iteratedDeriv j Phi a)) :
    (psiOnePanelBox right jets d h).ContainsReal (psi 1 a) := by
  have hpoly : QInterval.ContainsReal (QInterval.sumBox (Finset.range d)
      (fun j => QInterval.mul (jets j) (QInterval.point (h^(j+1) / ((j+1).factorial:ℚ)))))
      (psiPanelCorrection 0 d a (h:ℝ)) := by
    unfold psiPanelCorrection
    apply QInterval.sumBox_containsReal
    intro j hj
    have hterm := QInterval.mul_containsReal (hjets j hj)
      (show (QInterval.point (h^(j+1) / ((j+1).factorial:ℚ))).ContainsReal
        ((h:ℝ)^(j+1) / ((j+1).factorial:ℝ)) by simp [QInterval.ContainsReal, QInterval.point])
    simpa only [psi, mul_div_assoc] using hterm
  apply addSymmetricError_containsReal (QInterval.add_containsReal hright hpoly)
  simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_div] using
    (psiOne_panel_error_le (d := d) ha (by exact_mod_cast hh) hb)

/-- Backwards propagation of the same panel checker along a uniform grid. -/
def psiOneUniformGridBox (right : QInterval) (jets : ℕ → ℕ → QInterval)
    (d : ℕ) (h : ℚ) : ℕ → ℕ → QInterval
  | _, 0 => right
  | i, n+1 => psiOnePanelBox (psiOneUniformGridBox right jets d h (i+1) n) (jets i) d h

/-- Soundness for any number of consecutive panels, including the 64 panels
of the compact certificate. -/
theorem psiOneUniformGridBox_containsReal (right : QInterval) (jets : ℕ → ℕ → QInterval)
    (d : ℕ) {a : ℝ} {h : ℚ} (ha : 0 ≤ a) (hh : 0 ≤ h) (i n : ℕ)
    (hb : a+((i+n:ℕ):ℝ)*(h:ℝ) ≤ 2)
    (hright : right.ContainsReal (psi 1 (a+((i+n:ℕ):ℝ)*(h:ℝ))))
    (hjets : ∀ k ∈ Finset.Ico i (i+n), ∀ j ∈ Finset.range d,
      (jets k j).ContainsReal (iteratedDeriv j Phi (a+(k:ℝ)*(h:ℝ)))) :
    (psiOneUniformGridBox right jets d h i n).ContainsReal (psi 1 (a+(i:ℝ)*(h:ℝ))) := by
  have hhR : 0 ≤ (h:ℝ) := by exact_mod_cast hh
  induction n generalizing i with
  | zero => simpa only [Nat.add_zero, psiOneUniformGridBox] using hright
  | succ n ih =>
    have hidx : i + (n+1) = (i+1)+n := by omega
    have hnext : a + ((i+1:ℕ):ℝ)*(h:ℝ) = a+(i:ℝ)*(h:ℝ)+(h:ℝ) := by
      push_cast
      ring
    have hpoint : a+(i:ℝ)*(h:ℝ)+(h:ℝ) ≤ 2 := by
      rw [← hnext]
      have hle : ((i+1:ℕ):ℝ) ≤ ((i+(n+1):ℕ):ℝ) := by
        exact_mod_cast (show i+1 ≤ i+(n+1) by omega)
      exact (add_le_add_right (mul_le_mul_of_nonneg_right hle hhR) a).trans hb
    have hprev :=
      ih (i+1) (by rwa [hidx] at hb) (by rwa [hidx] at hright) (by
        intro k hk j hj
        rw [Finset.mem_Ico] at hk
        apply hjets k (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) j hj)
    rw [psiOneUniformGridBox]
    apply psiOnePanelBox_containsReal (by positivity) hh hpoint (by rwa [hnext] at hprev)
    intro j hj
    exact hjets i (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) j hj

#print axioms phiCompactJetBox_containsReal
#print axioms psiOneUniformGridBox_containsReal

end Nuttall
