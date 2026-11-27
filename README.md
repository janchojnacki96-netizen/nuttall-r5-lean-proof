# Nuttall — formalization of the Riemann theta kernel results

The [bilingual preprint and computational supplement](papers/linear-bounds/)
give the mathematical statements and reproduction instructions.

The [order-five proof](W5/NuttallR5.lean) verifies the required Wronskian
signs for the first tail integral on the entire nonnegative half-line.
See [the verified R5 revision and CI run](https://github.com/janchojnacki96-netizen/nuttall-r5-lean-proof/actions/runs/45486606898)
for its build and axiom audit.

The [preprint formalization](Nuttall/Existence.lean) uses the same definition of
the theta kernel. It proves the reduction in Theorem 1.2 from eventual
positivity at integration level `2 * R` to existence of a finite level for
each prescribed order. The analytic estimate in Section 4.1 is the
hypothesis of this reduction. The project introduces no literature axioms at
this stage.

Build the preprint modules with `lake build Nuttall` after obtaining the
pinned Mathlib dependencies with `lake update` and `lake exe cache get Mathlib`.
