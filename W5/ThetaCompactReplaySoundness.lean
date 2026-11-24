import W5.ThetaCompactReplayData

/-!
# One soundness proof for all compact replay cells

Every analytic ingredient is reused from the last-cell proof and its
already-proved original Gamma, signed-term, exact-tail and LDL lemmas.
The independent finite checks are the only hypotheses on stored data.
-/

namespace W5

theorem thetaCompactReplayLowerSum_bound
    (d : ThetaCompactReplayCellData)
    (hBins : ∀ i : Fin 12, ThetaCompactReplayBinFits d i) (k : Fin 9) :
    thetaCompactReplaySum12 (fun i => d.lower i k) ≤
      (thetaGammaLowerGridBox k.val (d.a^2)
        (thetaGammaAutoRootGrid d.steps (d.a^2)) 0 thetaLastCellGrid).lo := by
  have h (i : Fin 12) :
      d.lower i k ≤
        (thetaGammaLowerNineBin d.steps (d.a^2)
          (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).lo := by
    have h0 : d.lower i k ≤
        (thetaGammaMemoLowerNineBin thetaLastCellWExp d.steps (d.a^2)
          (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).lo :=
      (hBins i k).1
    rw [thetaGammaMemoLowerNineBin_eq thetaLastCellWExp thetaLastCellWExp_eq] at h0
    exact h0
  rw [thetaLastCellGrid_explicit]
  simp only [thetaGammaLowerGridBox, QInterval.add, QInterval.point]
  exact add_le_add (h (0:Fin 12)) (add_le_add (h (1:Fin 12)) (add_le_add (h (2:Fin 12)) (add_le_add (h (3:Fin 12)) (add_le_add (h (4:Fin 12)) (add_le_add (h (5:Fin 12)) (add_le_add (h (6:Fin 12)) (add_le_add (h (7:Fin 12)) (add_le_add (h (8:Fin 12)) (add_le_add (h (9:Fin 12)) (add_le_add (h (10:Fin 12)) (add_le_add (h (11:Fin 12)) (le_refl (0:ℚ)))))))))))))

theorem thetaCompactReplayUpperSum_bound
    (d : ThetaCompactReplayCellData)
    (hBins : ∀ i : Fin 12, ThetaCompactReplayBinFits d i) (k : Fin 9) :
    (thetaGammaUpperGridBox k.val (d.b^2)
      (thetaGammaAutoRootGrid d.steps (d.b^2)) 0 thetaLastCellGrid).hi ≤
      thetaCompactReplaySum12 (fun i => d.upper i k) := by
  have h (i : Fin 12) :
      (thetaGammaUpperNineBin d.steps (d.b^2)
          (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).hi ≤
        d.upper i k := by
    have h0 : (thetaGammaMemoUpperNineBin thetaLastCellWExp d.steps (d.b^2)
          (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).hi ≤ d.upper i k :=
      (hBins i k).2
    rw [thetaGammaMemoUpperNineBin_eq thetaLastCellWExp thetaLastCellWExp_eq] at h0
    exact h0
  rw [thetaLastCellGrid_explicit]
  simp only [thetaGammaUpperGridBox, QInterval.add, QInterval.point]
  exact add_le_add (h (0:Fin 12)) (add_le_add (h (1:Fin 12)) (add_le_add (h (2:Fin 12)) (add_le_add (h (3:Fin 12)) (add_le_add (h (4:Fin 12)) (add_le_add (h (5:Fin 12)) (add_le_add (h (6:Fin 12)) (add_le_add (h (7:Fin 12)) (add_le_add (h (8:Fin 12)) (add_le_add (h (9:Fin 12)) (add_le_add (h (10:Fin 12)) (add_le_add (h (11:Fin 12)) (le_refl (0:ℚ)))))))))))))

/-- Transfer the checked bin endpoints to the original monotone
full moment on the entire x-cell. -/
theorem thetaCompactReplayMoment_containsReal
    (d : ThetaCompactReplayCellData) (hElig : ThetaCompactReplayEligible d)
    (hGamma : ThetaCompactReplayGammaFits d)
    (x : ℝ) (hax : (d.a:ℝ) ≤ x) (hxb : x ≤ (d.b:ℝ))
    (k : ℕ) (hk : k < 9) :
    QInterval.ContainsReal (d.M k) (thetaAuditedOneWeightedMoment x k) := by
  rcases hElig with ⟨ha, _, hb, _, hA, hB⟩
  rcases hGamma with ⟨hBins, hSums⟩
  have haR : (0:ℝ) ≤ (d.a:ℝ) := by exact_mod_cast ha.le
  have hb1Q : d.b ≤ 1 := hb.trans (by norm_num)
  have hb1R : (d.b:ℝ) ≤ 1 := by exact_mod_cast hb1Q
  let K : Fin 9 := ⟨k,hk⟩
  have hfit := hSums K
  have hlo : (thetaCompactReplayGammaBox d K).lo ≤
      (thetaGammaAutoMomentBox d.steps k d.a thetaLastCellGrid).lo := by
    simpa only [thetaCompactReplayGammaBox, thetaGammaAutoMomentBox,
      thetaGammaAutoFullMomentGridBox, thetaGammaWeightedExactTailBox,
      QInterval.add, add_zero, K] using thetaCompactReplayLowerSum_bound d hBins K
  have hhi : (thetaGammaAutoMomentBox d.steps k d.b thetaLastCellGrid).hi ≤
      (thetaCompactReplayGammaBox d K).hi := by
    simp only [thetaCompactReplayGammaBox, thetaGammaAutoMomentBox,
      thetaGammaAutoFullMomentGridBox, thetaGammaWeightedExactTailBox,
      QInterval.add, thetaLastCellGrid_last, thetaLastCellWExp_eq, K]
    exact add_le_add (thetaCompactReplayUpperSum_bound d hBins K) le_rfl
  have hA0 := thetaGammaAutoMomentBox_containsReal_of_check
    d.steps k d.a thetaLastCellGrid hA
  have hB0 := thetaGammaAutoMomentBox_containsReal_of_check
    d.steps k d.b thetaLastCellGrid hB
  have hcell := thetaAuditedOneWeightedMoment_cell_interval
    (d.a:ℝ) x (d.b:ℝ) haR hax hxb hb1R k _ _ hA0 hB0
  exact thetaLastCellReplayWiden
    (A := d.M k)
    (B := (⟨(thetaGammaAutoMomentBox d.steps k d.a thetaLastCellGrid).lo,
      (thetaGammaAutoMomentBox d.steps k d.b thetaLastCellGrid).hi⟩ : QInterval))
    (hfit.1.trans hlo) (hhi.trans hfit.2) hcell

theorem thetaCompactReplayExp_containsReal
    (d : ThetaCompactReplayCellData) (hElig : ThetaCompactReplayEligible d)
    (hFit : ThetaCompactReplayExpFits d)
    (x : ℝ) (hax : (d.a:ℝ) ≤ x) (hxb : x ≤ (d.b:ℝ))
    (n : ℕ) (hn2 : 2 ≤ n) (hn7 : n < 7) :
    QInterval.ContainsReal (d.E n)
      (Real.exp (-((n:ℝ)^2-1)/x^2)) := by
  rcases hElig with ⟨ha, _, _, hExp, _, _⟩
  have hfit : (d.E n).lo ≤ (thetaLastCellCachedExp d.a d.b n).lo ∧
      (thetaLastCellCachedExp d.a d.b n).hi ≤ (d.E n).hi :=
    hFit ⟨n,hn7⟩ hn2
  rw [thetaLastCellCachedExp_eq d.a d.b n hn2] at hfit
  have hEl := hExp ⟨n,hn7⟩ hn2
  have h := thetaBulkFixedGaussianExpBox_containsReal d.a d.b x n
    ha hax hxb hn2 hEl.1 hEl.2
  exact thetaLastCellReplayWiden hfit.1 hfit.2 h

theorem thetaCompactReplayFirst_containsReal
    (d : ThetaCompactReplayCellData) (x : ℝ) (hx : 0 < x)
    (hax : (d.a:ℝ) ≤ x) (hxb : x ≤ (d.b:ℝ)) (hb1 : (d.b:ℝ) ≤ 1)
    (hM : ∀ k < 9, QInterval.ContainsReal (d.M k) (thetaAuditedOneWeightedMoment x k))
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaCompactReplayFirst d i j)
      (thetaAuditedSeriesTerm x i j 1) := by
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
    (thetaOneSquareCellScaleBox d.a d.b)
    (thetaGeneralCellCubicBinomialCoefficientBox d.a d.b i j)
    d.M hdiag
    (thetaOneSquareCellScaleBox_containsReal d.a d.b x hax hxb)
    (fun k _ => thetaGeneralCellCubicBinomialCoefficientBox_containsReal
      d.a d.b x hax hxb i j k)
    (fun k hk => hM k (Finset.mem_range.mp hk))

/-- Use the verified original n=1 polynomial and n>=2 signed terms,
plus the already-certified infinite n>=7 tail. -/
theorem thetaCompactReplaySource_containsReal
    (d : ThetaCompactReplayCellData) (hElig : ThetaCompactReplayEligible d)
    (hGamma : ThetaCompactReplayGammaFits d) (hExp : ThetaCompactReplayExpFits d)
    (x : ℝ) (hx : 0 < x) (hax : (d.a:ℝ) ≤ x) (hxb : x ≤ (d.b:ℝ))
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaCompactReplaySource d i j) (thetaCoefficient x i j) := by
  have ha : (0:ℚ) < d.a := hElig.1
  have hb : (d.b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (d.b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by exact_mod_cast hElig.2.2.1
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  have hb1 : (d.b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := hxb.trans hb1
  let J := thetaLastCellTermBox (thetaCompactReplayFirst d) d.E d.a d.b i j
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal (J n) (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [J, thetaLastCellTermBox, thetaAuditedSeriesTerm_zero,
        QInterval.ContainsReal, QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        change QInterval.ContainsReal (thetaCompactReplayFirst d i j)
          (thetaAuditedSeriesTerm x i j 1)
        exact thetaCompactReplayFirst_containsReal d x hx hax hxb hb1
          (fun k hk => thetaCompactReplayMoment_containsReal d hElig hGamma x hax hxb k hk)
          i j
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        have h := thetaBulkSignedOriginalTermBox_containsReal
          d.a d.b x ha hx hax hxb hb1 i j n (by omega) (d.E n)
          (thetaCompactReplayExp_containsReal d hElig hExp x hax hxb n hn2 hn7)
        simpa only [J, thetaLastCellTermBox, if_neg hn0, if_neg hn1] using h
  have htail := thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add (thetaAuditedPrefixInterval 7 J) thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j J
    (QInterval.add (thetaAuditedPrefixInterval 7 J) thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

theorem thetaCompactReplayMatrixFits_sound
    (d : ThetaCompactReplayCellData) (hFit : ThetaCompactReplayMatrixFits d) :
    ThetaUpperMatrixRefines d.W (thetaCompactReplaySource d) := by
  intro i j hij
  have h := hFit i j hij
  simpa only [thetaCompactReplayUpperSource, thetaDirectCacheMatrix_eq,
    Matrix.of_apply, if_pos hij] using h

/-- One sound theorem, instantiated by every independently checked cell. -/
theorem thetaCompactReplayCertificate_of_checks
    (d : ThetaCompactReplayCellData)
    (hArith : ThetaCompactReplayArithmeticFits d)
    (hGamma : ThetaCompactReplayGammaFits d) :
    ThetaUpperRealCellCertificate d.a d.b := by
  rcases hArith with ⟨hElig, hExp, hFit, hLDL⟩
  have hPivot : intervalLDL5AlternatingCheck (thetaSymmetricIntervals d.W) = true := by
    rw [← thetaDirectLDLCheck_eq]
    exact hLDL
  apply thetaUpperRealCellCertificate_of_checked d.a d.b d.W hPivot
  intro x hx hax hxb i j hij
  exact thetaUpperMatrixRefines_containsReal d.W (thetaCompactReplaySource d)
    (thetaCompactReplayMatrixFits_sound d hFit) (thetaCoefficient x i j)
    i j hij
    (thetaCompactReplaySource_containsReal d hElig hGamma hExp x hx hax hxb i j)

/-- Widen the rational coordinate cell for numerical efficiency,
then restrict the genuine real theorem to the original exact endpoints. -/
theorem thetaCompactReplayCertificate_restrict
    (d : ThetaCompactReplayCellData) (a b : ℚ)
    (hArith : ThetaCompactReplayArithmeticFits d) (hGamma : ThetaCompactReplayGammaFits d)
    (ha : d.a ≤ a) (hb : b ≤ d.b) : ThetaUpperRealCellCertificate a b := by
  obtain ⟨C, hLDL, hC⟩ := thetaCompactReplayCertificate_of_checks d hArith hGamma
  refine ⟨C, hLDL, ?_⟩
  intro x hx hax hxb i j hij
  have haR : (d.a:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hbR : (b:ℝ) ≤ (d.b:ℝ) := by exact_mod_cast hb
  exact hC x hx (haR.trans hax) (hxb.trans hbR) i j hij

end W5
