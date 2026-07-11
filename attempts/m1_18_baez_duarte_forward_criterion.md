# M1-18 Baez-Duarte Forward Criterion

Date: 2026-07-11

Fixed gap: `G2/forward/delta-to-zero-and-assembly`.

## Target

Compile `Mathlib.RiemannHypothesis ->` the aligned complex positive-natural target closure, then
combine it with the checked M1-16 reverse implication.

## Attempts and Route Changes

1. The preregistered route proposed choosing the anonymous M1-17 fixed-delta limit. This was
   rejected because it introduced avoidable choice and convergence-in-measure bookkeeping.
2. The successful route stays finite: package `X_epsilon f_(2 epsilon,N)`, prove its exact finite
   Mellin/Fourier formula, and bound finite transform minus the zeta-ratio limit directly.
3. The tail assembly requires `X_epsilon(f + x^epsilon chi)`. The correction
   `x^epsilon chi -> chi` was therefore formalized before final weight removal.

## Result

The finite and epsilon limits, diagonal assembly, exact tail transfer, real/complex closure, and
`riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure` all compile. No `sorry`, `admit`,
new axiom, or encoded analytic premise is used.

`result_class`: `KNOWN_THEOREM_FORMALIZED`.

This closes the published criterion formalization. It does not prove RH, since neither side of the
equivalence is established unconditionally.

Full `lake build` passes with 8608 jobs. Incomplete-proof, explicit-declaration, and whitespace
scans pass. The final equivalence uses only `propext`, `Classical.choice`, and `Quot.sound`.
