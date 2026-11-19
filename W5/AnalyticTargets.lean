import W5.Statement

/-!
Explicit analytic targets for the order-five certificate.
These definitions are not proofs of the equalities or inequalities.
-/
namespace W5
open MeasureTheory

noncomputable def normalizedKernel (x u v : ℝ) : ℝ :=
  let y : ℝ := 1 / x ^ (2 : ℕ)
  let t : ℝ := Real.log (y / Real.pi) / 4
  let su : ℝ := Real.log (1 + x*u) / 4
  let sv : ℝ := Real.log (1 + x*v) / 4
  (2 * Real.pi ^ ((1 : ℝ)/4) * Real.exp y / y ^ ((5 : ℝ)/4)) *
    (Real.exp (u/x) * Real.exp (v/x) /
      ((1+x*u) ^ ((5 : ℝ)/4) * (1+x*v) ^ ((5 : ℝ)/4))) *
    Psi1 (t + su + sv)

noncomputable def analyticCoeff (x : ℝ) (i j : Fin 5) : ℝ :=
  (iteratedDeriv i.val
     (fun u : ℝ => iteratedDeriv j.val
        (fun v : ℝ => normalizedKernel x u v) 0) 0) /
    ((Nat.factorial i.val : ℝ) * (Nat.factorial j.val : ℝ))

noncomputable def coefficientPolynomial (i j : Fin 5) (d q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (min i.val j.val + 1),
    ((-1 : ℝ) ^ (i.val + j.val - k) *
       d ^ (i.val + j.val - 2*k) * q ^ k) /
      ((Nat.factorial k : ℝ) *
       (Nat.factorial (i.val-k) : ℝ) *
       (Nat.factorial (j.val-k) : ℝ))

noncomputable def thetaCoefficient (x : ℝ) (i j : Fin 5) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else
    let p : ℝ := (n : ℝ)^2
    let d0 : ℝ := (p - 1) / x
    let integral : ℝ :=
      ∫ w in Set.Ici (0:ℝ),
        Real.exp (-w) *
          (1 + w*x^2/p) ^ ((1:ℝ)/4) *
          coefficientPolynomial i j (d0 + w*x) (p + w*x^2)
          ∂MeasureTheory.volume
    p * Real.exp (-(p-1)/x^2) *
      (coefficientPolynomial i j d0 p - x^2/(4*p)*integral)

/-- NOT YET PROVED: theta representation and differentiation. -/
def thetaTransformCorrect : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ (145:ℝ)/256 →
    ∀ i j : Fin 5, analyticCoeff x i j = thetaCoefficient x i j

/-- NOT YET PROVED: sound certified signs on the entire compact range. -/
def analyticMatrixPositive : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ (145:ℝ)/256 →
    (0 < (Matrix.of (fun (i j : Fin 1) =>
       thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det) ∧
    ((Matrix.of (fun (i j : Fin 2) =>
       thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det < 0) ∧
    ((Matrix.of (fun (i j : Fin 3) =>
       thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det < 0) ∧
    (0 < (Matrix.of (fun (i j : Fin 4) =>
       thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)).det) ∧
    (0 < (Matrix.of (fun (i j : Fin 5) =>
       thetaCoefficient x i j)).det)
end W5
