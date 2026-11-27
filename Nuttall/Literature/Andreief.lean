import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Nuttall.Literature

open MeasureTheory

/-- Andréief's determinant integration identity, in its real σ-finite
measure formulation with absolute integrability of every paired product.
See P. J. Forrester, “Meet Andréief, Bordeaux 1886, and Andreev, Kharkov
1882–83”, Eq. (1.7) and §2.1, https://arxiv.org/abs/1806.10411.
Both determinants here are transposes of the corresponding node-by-function form. -/
axiom andreief {p : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (f g : Fin p → ℝ → ℝ) (h : ∀ i j, Integrable (fun s => f i s * g j s) μ) :
    ((p.factorial : ℝ) *
      (Matrix.of (fun (i j : Fin p) => ∫ s, f i s * g j s ∂μ)).det) =
    ∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => f i (x j))).det *
      (Matrix.of (fun (i j : Fin p) => g i (x j))).det ∂Measure.pi (fun _ => μ)

end Nuttall.Literature
