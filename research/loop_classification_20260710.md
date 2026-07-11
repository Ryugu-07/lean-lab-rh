# RH Loop Classification Under Protocol v2

Date: 2026-07-10

Source logs:

- `attempts/riemann_hypothesis_initial.md`
- `research/rh_loop_protocol_20260709.md`
- `HANDOFF.md`

Range rows below classify every loop in the range. Under v2, none of loops 1-130 changed G1, G2,
or G3 in `research/hard_gap_dag.md`; therefore none is classified as `HARD_GAP_REDUCED`.

| loops | result_class | hard_gap_delta | rationale |
| --- | --- | --- | --- |
| 1-3 | FORMALIZATION_ONLY | 0 | RH wrapper and trivial-zero separation interfaces. |
| 4-68 | FORMALIZATION_ONLY | 0 | Local xi/Li scaffold, center-value estimates, and numerical/analytic support for project-local statements. |
| 69-74 | FORMALIZATION_ONLY | 0 | Xi/completed-zeta and xi/nontrivial-zero bridges; useful interfaces but not one of the fixed hard gaps. |
| 75-85 | FORMALIZATION_ONLY | 0 | Bounded work closing local Li-candidate positivity and writing the Tier 1 note. |
| 86 | DEPENDENCY_GAP_IDENTIFIED | 0 | Li/Hadamard inventory found missing global product, zero-enumeration, and zero-sum bridge infrastructure. |
| 87 | DEPENDENCY_GAP_IDENTIFIED | 0 | Nyman-Beurling inventory found no ready criterion statement, but enough L2 infrastructure for scaffolding. |
| 88-106 | FORMALIZATION_ONLY | 0 | Project-local Nyman-Beurling kernel, span, closure, density, and concrete approximation infrastructure. |
| 107 | DEPENDENCY_GAP_IDENTIFIED | 0 | Classical criterion inventory recorded the mismatch between local predicates and published NB/BD criteria. |
| 108-125 | FORMALIZATION_ONLY | 0 | Restricted-parameter branch and route summary; conditional on restricted density and not a criterion bridge. |
| 126 | DEPENDENCY_GAP_IDENTIFIED | 0 | Natural-index inventory selected a Lean index shape and reciprocal map, but did not reduce M0/M1. |
| 127-130 | FORMALIZATION_ONLY | 0 | Positive-natural reciprocal map, finite-support transport, integral transport, and predicate packaging. |

## Consecutive-Loop Review

- The final run 127-130 has repeated `hard_gap_delta = 0`.
- The planned loop 131 is a one-step composition corollary and must be batched instead of run as
  a standalone loop.
- Before any new math loop, a clean-context audit must choose `CONTINUE`, `PIVOT`, `BATCH`, or
  `STOP` against the fixed DAG.

## Governed Batches After Loop 130

| batch | result_class | hard_gap_delta | rationale |
| --- | --- | --- | --- |
| M1-11 | DEPENDENCY_GAP_IDENTIFIED | 0 | Isolated the exact Titchmarsh analytic-log/Borel/Hadamard boundary and compiled the analytic logarithm branch. |
| M1-12 | HARD_GAP_REDUCED | remove reciprocal-zeta subedge | Compiled the exact RH reciprocal-zeta arbitrary-subpower theorem used by the Balazard-Saias route. |
