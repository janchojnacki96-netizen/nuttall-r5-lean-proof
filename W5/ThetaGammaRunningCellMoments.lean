import W5.ThetaGammaRoundedRunningGrid

/-!
# Reuse bounded-denominator Gamma bin sums on whole original x-cells

The running Gamma-grid accumulator in ThetaGammaRoundedRunningGrid
encloses the old, already sound exact-rational endpoint integrals.
This module applies the ALREADY proved monotone cell bridge once and
transfers those endpoint enclosures to every x in [a,b], any n>=1
and any moment degree k.

There is no numerical assumption, no new analytic integral, and no
per-cell or per-degree proof. A fixed-scale rounded version can be
plugged directly into the previously certified signed theta terms.
-/

namespace W5

/-- Running-rounded full Gamma moments on the two x/n endpoints,
which bound the ORIGINAL moment uniformly over the whole cell. -/
def thetaGammaRunningAutoCellMomentBox (steps k : ℕ)
    (a b : ℚ) (n : ℕ) (us : List ℚ) : QInterval :=
  ⟨(thetaGammaRunningAutoMomentBox steps k (a/(n:ℚ)) us).lo,
    (thetaGammaRunningAutoMomentBox steps k (b/(n:ℚ)) us).hi⟩

/-- Reuse the existing analytic cell-monotonicity proof verbatim:
only the two certified endpoint intervals become wider by outward
rounding after EACH integration bin. -/
theorem thetaGammaRunningAutoCellMomentBox_containsReal
    (steps k : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hn : 0 < n)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck
      steps (a/(n:ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b/(n:ℚ)) us = true) :
    QInterval.ContainsReal
      (thetaGammaRunningAutoCellMomentBox steps k a b n us)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  have hOld := thetaGammaAutoCellMomentBox_containsReal
    steps k a b n us x ha hn hax hxb hb hA hB
  have hloQ :=
    (thetaGammaRunningAutoMomentBox_encloses_old
      steps k (a/(n:ℚ)) us).1
  have hhiQ :=
    (thetaGammaRunningAutoMomentBox_encloses_old
      steps k (b/(n:ℚ)) us).2
  have hloR :
      ((thetaGammaRunningAutoMomentBox steps k (a/(n:ℚ)) us).lo : ℝ) ≤
      ((thetaGammaAutoMomentBox steps k (a/(n:ℚ)) us).lo : ℝ) := by
    exact_mod_cast hloQ
  have hhiR :
      ((thetaGammaAutoMomentBox steps k (b/(n:ℚ)) us).hi : ℝ) ≤
      ((thetaGammaRunningAutoMomentBox steps k (b/(n:ℚ)) us).hi : ℝ) := by
    exact_mod_cast hhiQ
  change
    ((thetaGammaRunningAutoMomentBox steps k (a/(n:ℚ)) us).lo : ℝ) ≤
      thetaAuditedOneWeightedMoment (x/(n:ℝ)) k ∧
    thetaAuditedOneWeightedMoment (x/(n:ℝ)) k ≤
      ((thetaGammaRunningAutoMomentBox steps k (b/(n:ℚ)) us).hi : ℝ)
  exact ⟨hloR.trans hOld.1, hOld.2.trans hhiR⟩

/-- Optional 768-bit early outward rounding AFTER per-bin running
accumulation, before downstream signed polynomial expansions. -/
def thetaGammaRunningRoundedCellMomentBox
    (steps k : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) : QInterval :=
  thetaBulkRoundedQInterval
    (thetaGammaRunningAutoCellMomentBox steps k a b n us)

theorem thetaGammaRunningRoundedCellMomentBox_containsReal
    (steps k : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hn : 0 < n)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck
      steps (a/(n:ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b/(n:ℚ)) us = true) :
    QInterval.ContainsReal
      (thetaGammaRunningRoundedCellMomentBox steps k a b n us)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  exact thetaBulkRoundedQInterval_containsReal _
    (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k)
    (thetaGammaRunningAutoCellMomentBox_containsReal
      steps k a b n us x ha hn hax hxb hb hA hB)

/-- Choose fast true running Gamma moments only for specified degrees
of the n=1 theta term, keeping previously checked coarse enclosures
for all unselected degrees. -/
def thetaGammaRunningSelectedMomentBox
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) : QInterval :=
  if k ∈ K then
    thetaGammaRunningRoundedCellMomentBox steps k a b 1 us
  else
    thetaNthCubicGammaMomentBox a b 1 k

/-- Soundness of the selected running Gamma moments for ALL k. -/
theorem thetaGammaRunningSelectedMomentBox_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) (x : ℝ)
    (ha : (0:ℚ) ≤ a)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true) :
    QInterval.ContainsReal
      (thetaGammaRunningSelectedMomentBox steps a b us K k)
      (thetaAuditedOneWeightedMoment x k) := by
  by_cases hk : k ∈ K
  · have h := thetaGammaRunningRoundedCellMomentBox_containsReal
      steps k a b 1 us x ha (by norm_num) hax hxb hb
      (by simpa using hA) (by simpa using hB)
    simpa [thetaGammaRunningSelectedMomentBox, hk] using h
  · have h := thetaGammaDegreeSelectedMomentBox_containsReal
      steps a b us K k x ha hax hxb hb hA hB
    simpa [thetaGammaRunningSelectedMomentBox,
      thetaGammaDegreeSelectedMomentBox, hk] using h

end W5
