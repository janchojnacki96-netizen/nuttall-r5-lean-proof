import W5.ThetaActualNormalizedKernelCertificateSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Transport ALL mixed jets of the genuine kernel through its local equality

The actual original normalizedKernel is equal, on an explicit open
two-dimensional Taylor box, to the true certificate Gaussian series
(#113). Mathlib already proves
  Set.EqOn.iteratedDeriv_of_isOpen
for arbitrary derivative orders. There is no need to reprove
differentiation of locally equal functions.

We use that library lemma twice:
1. fix u in the open box, transport any j-th v-derivative at v=0;
2. transport any i-th u-derivative of those two functions at u=0.

Thus ALL 25 analyticCoeff entries (and in fact all natural
derivative orders) are identified with the mixed jets of the
certificate Gaussian SERIES AS A FUNCTION. This theorem does not
interchange derivatives with the infinite sum or improper integral.

The remaining analytic burden is to COMPUTE those series jets via
the existing Gaussian derivative majorants/Fubini lemmas, and to
identify their normalized values with thetaCoefficient.
-/

namespace W5

/-- Equality of all mixed original-kernel derivatives and the
mixed derivatives of the exact transformed Gaussian certificate
series at (u,v)=(0,0). The proof is entirely local and does not
differentiate a series termwise. -/
theorem normalizedKernel_mixedJets_eq_certificateGaussianSeries
    (x : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (i j : ℕ) :
    iteratedDeriv i
      (fun u : ℝ =>
        iteratedDeriv j (fun v : ℝ => normalizedKernel x u v) 0) 0 =
    iteratedDeriv i
      (fun u : ℝ =>
        iteratedDeriv j
          (fun v : ℝ =>
            ∑' n : ℕ, thetaCertificateGaussianFullTerm x u v n) 0) 0 := by
  let S : Set ℝ := Set.Ioo (-(x/8)) (x/8)
  have hsopen : IsOpen S := isOpen_Ioo
  have hx8 : 0 < x/8 := by positivity
  have hzero : (0:ℝ) ∈ S := by
    change -(x/8) < 0 ∧ 0 < x/8
    constructor <;> linarith
  have hbox (z : ℝ) (hz : z ∈ S) : |z| ≤ x/8 := by
    change -(x/8) < z ∧ z < x/8 at hz
    exact abs_le.mpr ⟨hz.1.le, hz.2.le⟩
  have hsections (u : ℝ) (hu : u ∈ S) :
      Set.EqOn
        (fun v : ℝ => normalizedKernel x u v)
        (fun v : ℝ =>
          ∑' n : ℕ, thetaCertificateGaussianFullTerm x u v n) S := by
    intro v hv
    exact normalizedKernel_eq_thetaCertificateGaussianFullSeries
      x u v hx hxB (hbox u hu) (hbox v hv)
  have houter :
      Set.EqOn
        (fun u : ℝ =>
          iteratedDeriv j (fun v : ℝ => normalizedKernel x u v) 0)
        (fun u : ℝ =>
          iteratedDeriv j
            (fun v : ℝ =>
              ∑' n : ℕ, thetaCertificateGaussianFullTerm x u v n) 0) S := by
    intro u hu
    exact ((hsections u hu).iteratedDeriv_of_isOpen hsopen j) hzero
  exact (houter.iteratedDeriv_of_isOpen hsopen i) hzero

/-- Mixed Taylor coefficient of the *actual certificate Gaussian
series*, with exactly the original factorial normalization.
It is a derivative of the complete function, NOT a formal sum
of differentiated coefficients. -/
noncomputable def thetaCertificateGaussianAnalyticCoeff
    (x : ℝ) (i j : Fin 5) : ℝ :=
  (iteratedDeriv i.val
    (fun u : ℝ =>
      iteratedDeriv j.val
        (fun v : ℝ =>
          ∑' n : ℕ, thetaCertificateGaussianFullTerm x u v n) 0) 0) /
    ((Nat.factorial i.val : ℝ) * (Nat.factorial j.val : ℝ))

/-- All 25 ORIGINAL analytic coefficients agree with the
corresponding complete Gaussian-series analytic coefficients,
without any assumption about termwise differentiation.

The final thetaTransformCorrect proof needs to identify the
coefficients of this series with the already-defined
thetaCoefficient polynomial integral expression. -/
theorem analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
    (x : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (i j : Fin 5) :
    analyticCoeff x i j =
      thetaCertificateGaussianAnalyticCoeff x i j := by
  unfold analyticCoeff thetaCertificateGaussianAnalyticCoeff
  rw [normalizedKernel_mixedJets_eq_certificateGaussianSeries
    x hx hxB i.val j.val]

end W5
