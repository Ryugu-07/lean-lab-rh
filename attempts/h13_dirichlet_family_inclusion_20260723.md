# H13 Dirichlet-Family Inclusion Attempt

Campaign: `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: inherited-summary recovery completed; H2 implementation, evidence, final
  ledger, public CI coordinates, historical atlas, and H13 source card were re-read before this
  selection.
- `global_goal`: active.

## Baseline

- `parent_commit`: `b13bc623e266990e9ba40802c6e1deb5ed87215a`.
- `parent_public_ci`: run `29959903737`, build job `89058172229`, passed in `2m14s`.
- `selected_node`: `H13-DIRICHLET-FAMILY-INCLUSION-01`.
- `preregistration`: `research/h13_dirichlet_family_inclusion_prereg_20260723.md`.
- `preregistration_commit`: pending.
- `preregistration_public_ci`: required before proof-source editing.

## Preregistered endpoint

Kernel-check the exact modulus-one inclusion of Riemann zeta in Mathlib's Dirichlet L-family,
then separate the valid one-way zeta-factor transfer from the invalid assumption that enlarging an
L-function target preserves an RH-equivalent zero set.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `H2_PUBLIC_CLOSURE` | H2 final-ledger commit `b13bc623e266990e9ba40802c6e1deb5ed87215a` passed run `29959903737`, job `89058172229`, in `2m14s`. | Return to historical breadth; actual bow exclusion, H2, and RH remain open. |
| 2 | `CROSS_FAMILY_COVERAGE` | H13 is the remaining source-aligned historical family without an independent theorem-producing attempt; H14 is supporting finite computation. | Select H13 before H14 and avoid returning to numerical-bound optimization. |
| 3 | `MATHLIB_OBJECT_AUDIT` | Mathlib commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` supplies analytic Dirichlet L-functions and proves the modulus-one member equals `riemannZeta`. | Use the real family object rather than a synthetic L-function class. |
| 4 | `TRANSFER_DESIGN` | Family-wide zero control implies RH only by specializing to the zeta member; a product containing zeta gives the same one-way implication, while an extra factor can add off-line zeros. | Preregister exact inclusion plus an explicit reverse-direction obstruction. |

## Assumption and gap accounting

- `assumption_frontier_before`: the project has exact zeta zero and critical-line predicates, and
  Mathlib has the modulus-one Dirichlet L-function identity; no H13 transfer theorem is registered.
- `hard_gap_before`: prove a generalized/automorphic/p-adic statement that controls every
  individual archimedean zeta zero without assuming a class theorem that already contains RH.
- `rh_frontier_before`: RH open.
- `candidate_obstruction`: family inclusion and zeta-factor products provide only a one-way
  reduction; additional factors can create new critical-strip zeros.
- `hard_gap_delta_target`: `0`; this audit is not expected to prove any generalized RH input.
- `route_map_delta_target`: `1`; H13 gains an exact theorem-producing transfer boundary.
- `obstruction_map_delta_target`: `1`; extra-factor reverse promotion is tested explicitly.
- `rh_frontier_delta_target`: `0` unless an unanticipated unconditional family theorem is found.
- `next_gate`: preregistration commit and public CI before Lean proof-source editing.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
