import W5.ThetaLastCellReplayGamma0
import W5.ThetaLastCellReplayGamma1
import W5.ThetaLastCellReplayGamma2
import W5.ThetaLastCellReplayExp
import W5.ThetaLastCellCompactDyadicGaussian
import W5.ThetaLastCellCompactDyadicGammaA
import W5.ThetaLastCellCompactDyadicGammaB

namespace W5

/-- Enlarging a rational enclosure preserves genuine real containment. -/
theorem thetaLastCellReplayWiden {A B : QInterval} {x : ℝ}
    (hlo : A.lo ≤ B.lo) (hhi : B.hi ≤ A.hi)
    (h : QInterval.ContainsReal B x) : QInterval.ContainsReal A x := by
  have hloR : (A.lo:ℝ) ≤ (B.lo:ℝ) := by exact_mod_cast hlo
  have hhiR : (B.hi:ℝ) ≤ (A.hi:ℝ) := by exact_mod_cast hhi
  exact ⟨hloR.trans h.1, h.2.trans hhiR⟩

theorem thetaLastCellReplayMomentFit (k : Fin 9) :
    (thetaLastCellReplayMomentWitness k.val).lo ≤
      (thetaGammaRunningCellNine 8 thetaLastCellA thetaLastCellB 1 thetaLastCellGrid k).lo ∧
    (thetaGammaRunningCellNine 8 thetaLastCellA thetaLastCellB 1 thetaLastCellGrid k).hi ≤
      (thetaLastCellReplayMomentWitness k.val).hi := by
  fin_cases k
  · have h := thetaLastCellReplayGamma0_checked (0:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma0_checked (1:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma0_checked (2:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma1_checked (0:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma1_checked (1:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma1_checked (2:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma2_checked (0:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma2_checked (1:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h
  · have h := thetaLastCellReplayGamma2_checked (2:Fin 3)
    rw [thetaLastCellReplayGammaGroupSource_apply] at h
    exact h

theorem thetaLastCellReplayMoment_containsReal
    (x : ℝ) (hax : (thetaLastCellA:ℝ) ≤ x)
    (hxb : x ≤ (thetaLastCellB:ℝ)) (k : ℕ) (hk : k < 9) :
    QInterval.ContainsReal (thetaLastCellReplayMomentWitness k)
      (thetaAuditedOneWeightedMoment x k) := by
  have hfit := thetaLastCellReplayMomentFit ⟨k,hk⟩
  rw [thetaGammaRunningCellNine_apply] at hfit
  have h := thetaGammaRunningRoundedCellMomentBox_containsReal
    8 k thetaLastCellA thetaLastCellB 1 thetaLastCellGrid x
    (by norm_num [thetaLastCellA]) (by norm_num) hax hxb
    (by norm_num [thetaLastCellB])
    (by simpa using thetaLastCellGammaA_checked)
    (by simpa using thetaLastCellGammaB_checked)
  exact thetaLastCellReplayWiden hfit.1 hfit.2 (by simpa using h)

theorem thetaLastCellReplayExp_containsReal
    (x : ℝ) (hax : (thetaLastCellA:ℝ) ≤ x)
    (hxb : x ≤ (thetaLastCellB:ℝ)) (n : ℕ) (hn2 : 2 ≤ n) (hn7 : n < 7) :
    QInterval.ContainsReal (thetaLastCellReplayExpWitness n)
      (Real.exp (-((n:ℝ)^2-1)/x^2)) := by
  have hfit :
      (thetaLastCellReplayExpWitness n).lo ≤
        (thetaLastCellCachedExp thetaLastCellA thetaLastCellB n).lo ∧
      (thetaLastCellCachedExp thetaLastCellA thetaLastCellB n).hi ≤
        (thetaLastCellReplayExpWitness n).hi :=
    thetaLastCellReplayExp_checked ⟨n,hn7⟩ hn2
  rw [thetaLastCellCachedExp_eq thetaLastCellA thetaLastCellB n hn2] at hfit
  have hEl := thetaLastCellGaussianEligible_checked ⟨n,hn7⟩ hn2
  have h := thetaBulkFixedGaussianExpBox_containsReal
    thetaLastCellA thetaLastCellB x n (by norm_num [thetaLastCellA])
    hax hxb hn2 hEl.1 hEl.2
  exact thetaLastCellReplayWiden hfit.1 hfit.2 h

/-- Existing nine-moment theorem, with the already checked small input table. -/
theorem thetaLastCellReplayFirst_containsReal
    (x : ℝ) (hx : 0 < x)
    (hax : (thetaLastCellA:ℝ) ≤ x) (hxb : x ≤ (thetaLastCellB:ℝ))
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaLastCellReplayFirst i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  have hb1 : (thetaLastCellB:ℝ) ≤ 1 := by norm_num [thetaLastCellB]
  have hdiag : QInterval.ContainsReal
      (thetaFirstCellGammaUniformDiagonal i j)
      (if i = j then (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ) else 0) := by
    by_cases hij : i = j
    · subst j
      simp [thetaFirstCellGammaUniformDiagonal, QInterval.ContainsReal, Rat.cast_div, Rat.cast_pow]
    · simp [thetaFirstCellGammaUniformDiagonal, QInterval.ContainsReal, hij]
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx (hxb.trans hb1) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox thetaLastCellA thetaLastCellB)
    (thetaGeneralCellCubicBinomialCoefficientBox thetaLastCellA thetaLastCellB i j)
    thetaLastCellReplayMomentWitness
    hdiag
    (thetaOneSquareCellScaleBox_containsReal thetaLastCellA thetaLastCellB x hax hxb)
    (fun k _ => thetaGeneralCellCubicBinomialCoefficientBox_containsReal
      thetaLastCellA thetaLastCellB x hax hxb i j k)
    (fun k hk => thetaLastCellReplayMoment_containsReal x hax hxb k (Finset.mem_range.mp hk))

/-- Genuine theta entry enclosure using only the checked input witnesses.
The infinite analytic tail and original signed coefficient identities
are exactly the earlier certified ones. -/
theorem thetaLastCellReplaySource_containsReal
    (x : ℝ) (hx : 0 < x)
    (hax : (thetaLastCellA:ℝ) ≤ x) (hxb : x ≤ (thetaLastCellB:ℝ))
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaLastCellReplaySource i j) (thetaCoefficient x i j) := by
  have ha : (0:ℚ) < thetaLastCellA := by norm_num [thetaLastCellA]
  have hb : (thetaLastCellB:ℝ) ≤ (145:ℝ)/256 := by norm_num [thetaLastCellB]
  have hb1 : (thetaLastCellB:ℝ) ≤ 1 := by norm_num [thetaLastCellB]
  have hx1 : x ≤ 1 := hxb.trans hb1
  let J := thetaLastCellTermBox thetaLastCellReplayFirst thetaLastCellReplayExpWitness
    thetaLastCellA thetaLastCellB i j
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal (J n) (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [J, thetaLastCellTermBox, thetaAuditedSeriesTerm_zero,
        QInterval.ContainsReal, QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        change QInterval.ContainsReal (thetaLastCellReplayFirst i j)
          (thetaAuditedSeriesTerm x i j 1)
        exact thetaLastCellReplayFirst_containsReal x hx hax hxb i j
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        have h := thetaBulkSignedOriginalTermBox_containsReal
          thetaLastCellA thetaLastCellB x ha hx hax hxb hb1 i j n (by omega)
          (thetaLastCellReplayExpWitness n)
          (thetaLastCellReplayExp_containsReal x hax hxb n hn2 hn7)
        simpa only [J, thetaLastCellTermBox, if_neg hn0, if_neg hn1] using h
  have htail := thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add (thetaAuditedPrefixInterval 7 J) thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j J
    (QInterval.add (thetaAuditedPrefixInterval 7 J) thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

end W5
