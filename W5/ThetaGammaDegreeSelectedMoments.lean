import W5.ThetaGammaSharperFirstSquare

/-!
# Selective original first-square Gamma moment precision

The certified n = 1 matrix needs only nine Gamma moments (k = 0,...,8).
The old global quadratic/cubic enclosures are very wide for the highest
moment degrees. Re-evaluating ALL nine moments with expensive rational
Gamma grids is unnecessary when only a few degrees dominate the final
LDL pivot uncertainty.

This file lets a finite set K choose precisely which moment degrees use
the verified finite-grid/infinite-tail algorithm. Other degrees retain
the already proved coarse cubic moment enclosure.

The same original signed coefficients, diagonal and scale are used.
No new analysis, axiom or unchecked numerical statement is introduced.
-/

namespace W5

/-- Each individual Gamma moment may use either the exact-root
rational grid plus exact exponential tail, or the existing cubic
Gamma enclosure. The choice is computable and can vary with k. -/
def thetaGammaDegreeSelectedMomentBox
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) : QInterval :=
  if k ∈ K then
    thetaGammaAutoCellMomentBox steps k a b 1 us
  else
    thetaNthCubicGammaMomentBox a b 1 k

/-- Uniform real correctness of the degree-selective enclosure,
including arbitrary unselected degrees. -/
theorem thetaGammaDegreeSelectedMomentBox_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) (x : ℝ)
    (ha : (0:ℚ) ≤ a)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true) :
    QInterval.ContainsReal
      (thetaGammaDegreeSelectedMomentBox steps a b us K k)
      (thetaAuditedOneWeightedMoment x k) := by
  by_cases hk : k ∈ K
  · have hm := thetaGammaAutoCellMomentBox_containsReal
      steps k a b 1 us x ha (by norm_num)
      hax hxb hb1
      (by simpa using hA) (by simpa using hB)
    simpa [thetaGammaDegreeSelectedMomentBox, hk] using hm
  · have hc := thetaNthCubicGammaMomentBox_containsReal
      a b x (by exact_mod_cast ha) hax hxb hb1 1 k (by omega)
    simpa [thetaGammaDegreeSelectedMomentBox, hk] using hc

/-- One ORIGINAL n=1 matrix whose moment accuracy can be tuned
independently for k=0,...,8. All 25 entries share this evaluator. -/
def thetaGammaDegreeSelectedFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ThetaIntervalMatrix :=
  fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      (thetaGammaDegreeSelectedMomentBox steps a b us K) 9

/-- One proof covers EVERY coefficient and EVERY selection of
moment degrees K. It reuses the existing nine-moment signed
interval theorem and never changes the theta integrand. -/
theorem thetaGammaDegreeSelectedFirstSquareMatrix_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaGammaDegreeSelectedFirstSquareMatrix steps a b us K i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  have hdiag : QInterval.ContainsReal
      (thetaFirstCellGammaUniformDiagonal i j)
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) := by
    by_cases hij : i = j
    · subst j
      simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, Rat.cast_div, Rat.cast_pow]
    · simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, hij]
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx (hxb.trans hb1) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
    (thetaGammaDegreeSelectedMomentBox steps a b us K)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaGeneralCellCubicBinomialCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ =>
      thetaGammaDegreeSelectedMomentBox_containsReal
        steps a b us K k x ha hax hxb hb1 hA hB)

end W5
