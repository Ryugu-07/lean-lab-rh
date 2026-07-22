# H8 Jensen Eventual-Hyperbolicity Attempt

Campaign: `FALSIFICATION-20260723-H8-JENSEN-EVENTUAL-HYPERBOLICITY-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `EVIDENCE_CI_PASSED / FINAL_LEDGER_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: inherited-summary recovery occurred before H11 implementation closure;
  canonical records were re-read and H11 was completed before this route selection.
- `global_goal`: active.

## Baseline

- `parent_commit`: `3424cb661487a45e544eb4fa1ff4ad8bcd757455`.
- `parent_public_ci`: run `29949249815`, build job `89022493860`, passed in `1m33s`.
- `selected_node`: `H8-JENSEN-EVENTUAL-NOT-GLOBAL-01`.
- `preregistration`: `research/h8_jensen_eventual_hyperbolicity_prereg_20260723.md`.

## Preregistered endpoint

Formalize generic Jensen coefficient windows and kernel-check a single-defect sequence that passes
every prescribed finite initial wedge and is eventually hyperbolic for every fixed degree, yet has
an explicit degree-two nonreal-root window. This tests the exact quantifier gap left by the human
eventual-hyperbolicity theorems.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `H11_CLOSURE / ROUTE_SELECTION` | H11 final-ledger commit `3424cb661487a45e544eb4fa1ff4ad8bcd757455` passed run `29949249815`, job `89022493860`, in `1m33s`. H11-D/H11-E remain open. | Compare underexplored historical families rather than optimize H11 proportions. |
| 2 | `CROSS_FAMILY_COMPARISON` | H2 density shares the already compiled sparse-exception obstruction; H7 has three recent finite spectral campaigns and now needs arithmetic uniformity or an infinite limit. H8 has no theorem-producing project campaign. | Select H8 as a breadth correction with a bounded falsification endpoint. |
| 3 | `SOURCE_AUDIT` | Primary-source search found no post-2024 all-degree/all-shift mechanism. Duran 2024 adds Brenke-polynomial RH equivalences but does not close all-index real-rootedness. Griffin et al. explicitly retain the all-`d,n` requirement, while Farmer documents asymptotic universality and weak defect detection. | Audit the quantifier promotion directly rather than add another equivalent criterion. |
| 4 | `FALSIFICATION_DESIGN` | A single zero coefficient inserted into an otherwise all-one sequence is invisible to every earlier finite Jensen window and every sufficiently late fixed-degree window, but creates `1+X^2` at one shift. | Preregister the parameterized finite-wedge/eventual/nonreal-root model before proof-source editing. |
| 5 | `PREREGISTRATION_CI` | Commit `0275ab15b83a253b9a4eb9fcfa4a575943b89b33` passed public run `29949869070`, build job `89024569873`, in `1m54s`. | Open proof-source editing at the fixed endpoint. |
| 6 | `WINDOW_AND_EVENTUAL_MODEL` | Lean defines the exact Jensen coefficient window, proves locality, proves the all-one identity `(1+X)^d`, and proves both finite-wedge and post-defect equality for the one-defect sequence. | Use the root predicate to discharge all finite and eventual real-rootedness claims. |
| 7 | `EXPLICIT_NONREAL_ROOT` | Lean proves the defect window at degree two and shift `m` is `1+X^2`; direct evaluation at `I` proves it does not have only real roots. | Combine the witnesses into `exists_eventually_realRooted_not_all_realRooted`. |
| 8 | `PROJECT_INTEGRATION` | The module, two Targets, seven exact TargetChecks, and six selected axiom prints compile. Selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`. | Record definition alignment, then run forbidden scan, diff check, module build, and full build. |
| 9 | `FULL_LOCAL_BUILD` | The production forbidden scan is empty, `git diff --check` passes, the H8 module has no local warning, and the full `8,744`-job build passes. | Freeze the implementation in a scoped commit and require independent public CI. |
| 10 | `IMPLEMENTATION_PUBLIC_CI` | Frozen implementation commit `ca656cb6e24b5084b403d53e5a3763dc34b642be` passed public Lean Action run `29950744385`, build job `89027520728`, in `2m4s`. | Keep Lean proof source frozen; publish immutable implementation evidence and require that evidence commit's own public CI. |
| 11 | `EVIDENCE_PUBLIC_CI` | Immutable-evidence commit `c567b96b0315121c3df10c4088422121f8f866a9` passed public Lean Action run `29951025462`, build job `89028448900`, in `1m37s`. | Stop the local falsification campaign at its registered endpoint; publish the final ledger and return the active RH Goal to historical-route omission search. |

## Assumption and gap accounting

- `assumption_frontier_before`: fixed-degree eventual hyperbolicity is a proved human theorem for
  the xi Jensen sequence; all-degree/all-shift hyperbolicity remains RH-equivalent.
- `hard_gap_before`: no uniform mechanism controls all degrees and all exceptional shifts.
- `rh_frontier_before`: RH open.
- `current_result`: `FULL_SUCCESS_AT_REGISTERED_LOGICAL_ENDPOINT / GENERIC_PROMOTION_FALSIFIED`.
- `candidate_obstruction_model`: all-one sequence with one future zero coefficient.
- `hard_gap_delta`: `0`; actual-xi all-index hyperbolicity remains open.
- `rh_frontier_delta`: `0`.
- `route_infrastructure_delta`: `1`.
- `route_map_delta`: `1`; Duran 2024 is added as a new-equivalence source, and the source
  quantifier boundary now has a compiled generic countermodel.
- `definition_alignment`:
  `research/h8_jensen_eventual_hyperbolicity_definition_alignment_20260723.md`.
- `public_implementation_evidence`: frozen implementation commit
  `ca656cb6e24b5084b403d53e5a3763dc34b642be` passed Lean Action run `29950744385`, build job
  `89027520728`, in `2m4s`.
- `public_closure_evidence`: immutable-evidence commit
  `c567b96b0315121c3df10c4088422121f8f866a9` passed Lean Action run `29951025462`, build job
  `89028448900`, in `1m37s`.
- `local_stop`: the registered generic falsification endpoint is publicly closed. H8 actual-xi
  all-index hyperbolicity and RH remain open.
- `next_gate`: final-ledger commit and public CI, then fresh historical-route selection.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
