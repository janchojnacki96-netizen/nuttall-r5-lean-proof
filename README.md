# Nuttall r=5 — theta-kernel proof formalization

**STATUS (18 November 2026): Partial formalization, NOT an unconditional proof.**

This private repository tests the order-five Wronskian sign
conjecture for the first integrated Riemann theta kernel. The target
is `W5.MainClaim`; **no unconditional theorem `W5.nuttall_r5` exists**.

## Three computational checks

1. `certificate/certyfikat_theta_W5.cpp`: original interval program,
   run independently under GCC and Clang. Expected: **51 cells**.
2. `certificate/audyt_theta_W5_integer.py`: independent 768-bit
   arbitrary-precision fixed-point arithmetic, recomputing the
   signed LDL pivots for **255 checks**. The exact 51 input cells are
   in `certificate/w5_przedzialy.txt`.
3. `certificate/verify_polynomial_majorant_w5.py`: **50 exact
   rational-polynomial checks** for
   `5(1+d)^8(1+q)^4 +/- B_ij(d,q)`, `i,j=0,...,4`, which have
   nonnegative coefficients.

The scripts are executable reproducibility checks. Their mathematical
correctness has **not** been fully proved by Lean and their successful
execution does not close the analytic part of the conjecture.

## Formal work proved in Lean

- Precise definitions of the theta kernel, `Psi1`, the Wronskians.
- 51 adjacent rational intervals and the covering lemma.
- Algebraic sign consequences from LDL pivots.
- General determinant sign invariance under congruence, positive
  lower-triangular transforms and positive scalar factors.
- Positivity of the normalization constant.
- Elementary ratio bound controlling a geometric majorant of the
  omitted theta squares.
- Exact sound addition/multiplication of rational intervals and
  directed integer quotient inequalities.
- Boundary-model coefficient evaluations.
- Elementary theta exponential coordinate identity (new;
  inspect CI status before considering this proven).

`W5/CoefficientTailBound.lean` attempts the complete absolute
bound for all 25 coefficient polynomials. **Its Lean compilation
must be checked against the latest workflow.** The independent
rational verifier establishes the corresponding finite algebra
outside Lean.

## Essential open mathematical proof obligations

- Formal justification for exchanging theta sums, integrals and
  derivatives. See `notes/ANALYTIC_TRANSFORM.md`.
- Prove the specific relation between the transformed coefficient
  matrix and `Psi1`'s Wronskians. A generic algebraic congruence
  theorem alone does **not** supply that relation.
- Formalize soundness of all 768-bit fixed-point operations, fourth
  roots, exponentials, incomplete-gamma moments and uniform tail.
- Bring the 255 computed pivot inequalities into trusted Lean
  checking and prove an unconditional `W5.nuttall_r5 : W5.MainClaim`.
- Perform a final axiom audit of the theorem and verify the
  definitions against the analytic statement.

GitHub Actions will show a green `lake-build` when the **existing
partial** lemmas type-check; that is intentionally distinct from
claiming a proof of the full W5 sign conjecture.

## Navigation

- Draft PR #1: source development and CI
- Issue #2: all remaining mathematical obligations
