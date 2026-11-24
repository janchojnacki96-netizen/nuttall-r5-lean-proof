# Canonical R5 formalization and reuse map

This branch is the proposed **single integration branch** for the user's
Nuttall R5 Lean development. The default branch is NOT changed here.

## Imported by existing Git blobs and commit ancestry
- CI-green #114: actual original coefficient (0,0) equals audited theta (0,0)
- CI-green #115: local Mathlib EqOn transport of ALL original kernel mixed jets
- CI-green #116: original normalized kernel and transformed integrated series
- CI-green #117: 51-cell conditional transfer to original kernel minor signs
- CI-green #120: fixed-scale integer floor/ceiling soundness (already in #129 lineage)
- CI-green #123: 255 concrete exact-rational LDL pivot checks
- CI-green #125–#129: audited matrix chain, real enclosures as explicit obligations,
  finite-prefix/tail reductions, summability, signed real interval arithmetic

Existing source modules are referenced using identical Git blob IDs, not
duplicated or rewritten. The later version of the original integer audit
script from #129 is kept in place. The new adapter
`ThetaAuditedNormalizedKernelBridge.lean` reuses existing certified
theorems and does not copy their analytic or matrix proofs.

## Explicitly OPEN
1. For all 51 cells × 15 independent coefficient entries, show the
   *actual transcendental thetaCoefficient* lies between the imported
   rational 768-bit endpoints (not merely that the 255 finite pivots pass).
2. Identify the other 24 original normalized-kernel Gaussian-series
   Taylor jets with their theta coefficients. The (0,0) equality is proved.
3. Review the final R5 Nuttall statement, assumptions and range bridge.

## Held outside until independently CI-green
- #130: fixed-point sqrt rounding
- #131: quantitative Taylor remainder bound
- #132: fixed-point polynomial powers

Avoid importing those while their CI results remain pending/failing.
For the next analytic work, reuse Mathlib and the audited fixed-point
operators; do not add another duplicate generic interval library.
