import W5.ThetaCoarseGammaMomentBoxes
import W5.ThetaRemaining50ReducedTermCertificate

/-!
# All positive square indices: reuse existing Mathlib Gamma moment boxes

Reuse EXACT sources from the preceding all-square-index working branch:
* ThetaAllSquareIndexNineMoments: the original n-th true theta
  term is a nine-moment Lebesgue integral, with its sound QInterval
  composition;
* ThetaCoarseGammaMomentBoxes: the nine actual moments at x/n
  have explicit rational boxes for all n>0.

This adapter removes ALL NINE moment-enclosure hypotheses for
the remaining n=2,...,11 term certificates. It retains the genuine
base-term, scale, exponential and polynomial-coefficient real
enclosures as separate obligations, and does not assert containment
in the tight original audited matrices. No original arithmetic
or analytic proof is copied into this adapter.
-/

namespace W5

/-- Arbitrary positive square index: exact real interval soundness
using an already proved coarse rational Gamma enclosure. There are
NO unproved weighted-moment hypotheses or extra integrations. -/
theorem thetaAuditedSeriesTerm_box_of_coarseGamma
    (b : ℚ) (x : ℝ) (hx : 0 < x)
    (hxb : x ≤ (b : ℝ)) (hb1 : (b : ℝ) ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 0 < n)
    (B X E : QInterval) (C : ℕ → QInterval)
    (hB : QInterval.ContainsReal B (thetaCertificateBaseTerm x i j n))
    (hX : QInterval.ContainsReal X (x^2/4))
    (hE : QInterval.ContainsReal E
      (Real.exp (-((n:ℝ)^2-1)/x^2)))
    (hC : ∀ k ∈ Finset.range 9,
      QInterval.ContainsReal (C k)
        ((thetaCorrectionWPolynomial
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) i j).coeff k)) :
    QInterval.ContainsReal
      (QInterval.sub B
        (QInterval.mul X
          (QInterval.mul E
            (QInterval.finsetSum (Finset.range 9)
              (fun k => QInterval.mul (C k)
                (thetaNthCoarseGammaMomentBox b n k))))))
      (thetaAuditedSeriesTerm x i j n) := by
  exact thetaAuditedSeriesTerm_nine_moment_box_containsReal
    x hx (hxb.trans hb1) i j n hn B X E C
    (thetaNthCoarseGammaMomentBox b n)
    hB hX hE hC
    (fun k _ =>
      thetaNthCoarseGammaMomentBox_containsReal
        b x hx.le hxb hb1 n k hn)

end W5
