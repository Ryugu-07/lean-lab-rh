# H13 Dirichlet-Family Inclusion Attempt

Campaign: `FALSIFICATION-20260723-H13-DIRICHLET-FAMILY-INCLUSION-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `PUBLICLY_CLOSED / INDIVIDUAL_TRANSFER_OPEN`

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
- `preregistration_commit`: `e001e3afb37818918e42b08d76c18b6490062ac7`.
- `preregistration_public_ci`: run `29960700375`, build job `89060685988`, passed in `2m2s`.

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
| 5 | `PREREGISTRATION_GATE` | Commit `e001e3afb37818918e42b08d76c18b6490062ac7` passed public Lean Action run `29960700375`, build job `89060685988`, in `2m2s`. | Open proof-source editing with the fixed endpoint and claim boundary unchanged. |
| 6 | `LEAN_ZETA_EQUIVALENCE` | Lean proves that critical-strip zero control for `riemannZeta` is equivalent to Mathlib's RH, with nontrivial/strip conversion in both directions. | Fix the generic predicate against the project's exact RH definition. |
| 7 | `LEAN_DIRICHLET_INCLUSION` | The modulus-one Dirichlet L-function predicate is exactly RH, and the all-Dirichlet predicate implies RH by specialization. | Confirm that a class theorem containing the zeta member is not a shortcut around RH. |
| 8 | `LEAN_PRODUCT_TRANSFER` | Critical-strip zero control for `zeta*g` implies zeta zero control and hence RH for every function `g`. | Retain this as a valid one-way consumer for genuine factorizations. |
| 9 | `LEAN_EXTRA_FACTOR_FALSIFICATION` | The product with factor `s-1/4` has an exact strip zero at `1/4`, away from the critical line. | Reject reverse-equivalence promotion for unconstrained extra factors. |
| 10 | `INTEGRATION_AUDIT` | One proven and one open Target, eight exact TargetChecks, seven selected standard-only axiom prints, an empty production forbidden scan, and the full `8,748`-job build pass. | Publish the implementation and require independent public CI; generalized RH, H13, and RH remain open. |
| 11 | `IMPLEMENTATION_PUBLIC_CI` | Frozen implementation commit `ab45b1bd8ba5c8cdbe5fb2bd9cd87c222131bb91` passed public Lean Action run `29961388807`, build job `89062966415`, in `2m18s`. | Keep Lean proof source frozen; publish immutable implementation evidence and require that evidence commit's own public CI. |
| 12 | `EVIDENCE_PUBLIC_CI` | Immutable-evidence commit `cb19d46bd1b62eb15dbd2ff41efe5ddf820c4505` passed public Lean Action run `29961677975`, build job `89063888150`, in `2m17s`. | Stop the local transfer-logic audit at its registered endpoint; publish the final ledger and return the active RH Goal to historical-route omission search. |
| 13 | `FINAL_LEDGER_PUBLIC_CI` | Final-ledger commit `11822e34ad720b9715f7cc22d17e2ed066e51803` passed public Lean Action run `29961935426`, build job `89064730187`, in `2m17s`. | Mark the transfer-logic campaign publicly closed; retain generalized RH, actual individual-zeta transfer, H13, and RH as open. |

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
- `hard_gap_delta`: `0`; no generalized-RH input has been proved.
- `route_map_delta`: `1`; H13 now has an exact theorem-producing inclusion/transfer boundary.
- `obstruction_map_delta`: `1`; unconstrained extra-factor reverse promotion is kernel-refuted.
- `rh_frontier_delta`: `0`.
- `public_implementation_evidence`: frozen implementation commit
  `ab45b1bd8ba5c8cdbe5fb2bd9cd87c222131bb91` passed Lean Action run `29961388807`, build job
  `89062966415`, in `2m18s`.
- `public_closure_evidence`: immutable-evidence commit
  `cb19d46bd1b62eb15dbd2ff41efe5ddf820c4505` passed Lean Action run `29961677975`, build job
  `89063888150`, in `2m17s`.
- `public_final_ledger`: commit `11822e34ad720b9715f7cc22d17e2ed066e51803` passed Lean Action run
  `29961935426`, build job `89064730187`, in `2m17s`.
- `local_stop`: the fixed transfer-logic endpoint is compiled. Actual automorphic, family, or
  p-adic individual-zeta transfer remains open.
- `next_gate`: H14 finite-height promotion is preregistered separately.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
