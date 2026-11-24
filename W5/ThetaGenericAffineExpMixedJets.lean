import W5.ThetaGaussianModelLowOrder
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# One recurrence for arbitrary mixed pointwise Gaussian jets

After j right derivatives at v=0 the elementary Gaussian is
(-d-q*u)^j * exp(-d*u). A single affine-exponential recurrence handles
all remaining left derivatives without a per-order calculus proof.
The final 5x5 identification uses only finite polynomial arithmetic.
No interchange with the original improper integral or series is claimed.
-/

namespace W5

noncomputable def thetaAffineExpJet (A B C : ℝ) :
    ℕ → ℕ → ℝ → ℝ
  | 0, j, u => (A+B*u)^j * Real.exp (C*u)
  | i+1, j, u =>
      C * thetaAffineExpJet A B C i j u +
        ((j:ℝ)*B) * thetaAffineExpJet A B C i (j-1) u

/-- Reusable arbitrary-order derivative recurrence, including j=0. -/
theorem thetaAffineExpJet_hasDerivAt (A B C : ℝ) :
    ∀ (i j : ℕ) (u : ℝ),
      HasDerivAt (thetaAffineExpJet A B C i j)
        (thetaAffineExpJet A B C (i+1) j u) u := by
  intro i
  induction i with
  | zero =>
      intro j u
      have hlin : HasDerivAt (fun z : ℝ => A+B*z) B u := by
        convert (((hasDerivAt_id u).const_mul B).const_add A) using 1
        funext z
        simp only [id_eq]
        ring
      have hscale : HasDerivAt (fun z : ℝ => C*z) C u := by
        simpa only [id_eq, mul_one] using ((hasDerivAt_id u).const_mul C)
      have hexp : HasDerivAt (fun z : ℝ => Real.exp (C*z))
          (C * Real.exp (C*u)) u := by
        convert (Real.hasDerivAt_exp (C*u)).comp u hscale using 1 <;>
          (try simp only [Function.comp_def]) <;> ring
      have h := (hlin.pow j).mul hexp
      change HasDerivAt
        (fun z : ℝ => (A+B*z)^j * Real.exp (C*z))
        (C * ((A+B*u)^j * Real.exp (C*u)) +
          ((j:ℝ)*B) * ((A+B*u)^(j-1) * Real.exp (C*u))) u
      convert h using 1 <;> simp only [Pi.pow_apply, Pi.mul_apply] <;> ring
  | succ i ih =>
      intro j u
      have h := ((ih j u).const_mul C).add
        ((ih (j-1) u).const_mul ((j:ℝ)*B))
      exact h

theorem thetaAffineExp_iteratedDeriv (A B C : ℝ) (i j : ℕ) (u : ℝ) :
    iteratedDeriv i (fun z : ℝ => (A+B*z)^j * Real.exp (C*z)) u =
      thetaAffineExpJet A B C i j u := by
  induction i generalizing u with
  | zero => rfl
  | succ i ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv i
          (fun z : ℝ => (A+B*z)^j * Real.exp (C*z)) =
          thetaAffineExpJet A B C i j := by
        funext z
        exact ih z
      rw [heq]
      exact (thetaAffineExpJet_hasDerivAt A B C i j u).deriv

/-- All right derivatives of the unweighted elementary Gaussian. -/
theorem thetaGaussianModel_iteratedDeriv_right_all
    (d q u : ℝ) (j : ℕ) (v : ℝ) :
    iteratedDeriv j (fun z : ℝ => thetaGaussianModel d q u z) v =
      (-d-q*u)^j * thetaGaussianModel d q u v := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv j (fun z : ℝ => thetaGaussianModel d q u z) =
          (fun z : ℝ => (-d-q*u)^j * thetaGaussianModel d q u z) := by
        funext z
        exact ih z
      rw [heq]
      have h := ((thetaGaussianModel_right_hasDerivAt d q u v).const_mul
        ((-d-q*u)^j)).deriv
      rw [h, pow_succ]
      ring

/-- Actual mixed derivatives at v=0, for all natural i and j. -/
theorem thetaGaussianModel_mixed_iteratedDeriv_all
    (d q : ℝ) (i j : ℕ) (u : ℝ) :
    iteratedDeriv i
      (fun z : ℝ => iteratedDeriv j
        (fun v : ℝ => thetaGaussianModel d q z v) 0) u =
      thetaAffineExpJet (-d) (-q) (-d) i j u := by
  have heq :
      (fun z : ℝ => iteratedDeriv j
        (fun v : ℝ => thetaGaussianModel d q z v) 0) =
      (fun z : ℝ => ((-d)+(-q)*z)^j * Real.exp ((-d)*z)) := by
    funext z
    rw [thetaGaussianModel_iteratedDeriv_right_all]
    simp only [thetaGaussianModel, add_zero, mul_zero, sub_zero]
    congr 1
    ring
  rw [heq]
  exact thetaAffineExp_iteratedDeriv (-d) (-q) (-d) i j u

/-- One finite algebraic check matches the arbitrary-order recurrence
with all normalized B_ij polynomials of the independent certificate. -/
theorem thetaAffineExpJet_zero_eq_coefficientPolynomial
    (d q : ℝ) (i j : Fin 5) :
    thetaAffineExpJet (-d) (-q) (-d) i.val j.val 0 /
        ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ)) =
      coefficientPolynomial i j d q := by
  fin_cases i <;> fin_cases j <;>
    norm_num [thetaAffineExpJet, coefficientPolynomial,
      Finset.sum_range_succ, Nat.factorial] <;> ring

/-- The actual elementary Gaussian mixed Taylor coefficients are
exactly the certificate polynomials at ALL 25 indices. -/
theorem thetaGaussianModel_mixed_taylor_eq_coefficientPolynomial
    (d q : ℝ) (i j : Fin 5) :
    iteratedDeriv i.val
        (fun z : ℝ => iteratedDeriv j.val
          (fun v : ℝ => thetaGaussianModel d q z v) 0) 0 /
        ((Nat.factorial i.val:ℝ)*(Nat.factorial j.val:ℝ)) =
      coefficientPolynomial i j d q := by
  rw [thetaGaussianModel_mixed_iteratedDeriv_all]
  exact thetaAffineExpJet_zero_eq_coefficientPolynomial d q i j

end W5
