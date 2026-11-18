# Nuttall order five — Lean 4 formalization (work in progress)

**Status: NOT A COMPLETE PROOF.** The integer interval checker from the
preceding audit reports 51 cells and 255 sign checks, but the analytic
derivations and the soundness of the certificate are not yet in Lean.

The CI workflow `.github/workflows/lean.yml` uses the pinned Lean/Mathlib
toolchain to run `lake build`. A green CI result means only that currently
stated lemmas type-check; it is not evidence that the Riemann theta W5
sign theorem has been proved.

## Modules

- `W5/Statement.lean` — theta kernel, first integral, Wronskians, main claim.
- `W5/FiniteCore.lean` — exact partition and pivot-sign implication.
- `W5/ConditionalBridge.lean` — implication requiring analytic hypotheses.
- `W5/Range.lean` — range bound for the compact coordinate.
- `W5/CurvatureBridge.lean` — conditional curvature sign consequence.
- `W5/BoundaryPivots.lean` — signs of the limiting model.
- `W5/AnalyticTargets.lean` — exact analytic definitions and targets.

Open obligations: prove the theta transform, sound real interval bounds
and tail estimates, and the determinant-congruence identities in Lean.
Then prove an **unconditional** `theorem nuttall_r5 : MainClaim` and
audit its axioms. No such final theorem is included yet.

Branch `work/lean-ci-bootstrap` is a CI/bootstrap branch, not a completed theorem.
