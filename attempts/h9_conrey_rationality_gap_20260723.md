# H9 Conrey Rationality-Gap Attempt

Campaign: `FALSIFICATION-20260723-H9-CONREY-RATIONALITY-GAP-01`

Mode: `FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_GREEN / EVIDENCE_BACKFILL_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: one inherited-summary recovery after local preregistration; canonical files
  were re-read before proceeding.
- `global_goal`: active.

## Baseline

- `parent_commit`: `02e8f746a1afacf87d74196883e909f0053a8618`.
- `parent_public_ci`: run `29937476151`, build job `88982651332`, passed in `2m9s`.
- `selected_node`: `H9-CONREY-RATIONALITY-FLAT-INTERVAL-01`.
- `preregistration`: `research/h9_conrey_rationality_gap_prereg_20260723.md`.
- `primary_source`: Acta Arithmetica 214 (2024), Proposition 1 and its later two-branch formula.
- `preregistration_commit`: `7e682226d4ac7965ba0f02265578d1c71dc0d9ad`.
- `preregistration_public_ci`: Lean Action run `29939270138`, build job `88988711235`, passed in
  `2m3s`.

## Preregistered endpoint

Prove the exact finite weighted-prefix identity, replace the printed rationality inference by the
correct flat-or-rational dichotomy, and kernel-check an irrational countermodel to the omitted
generic inference. Do not claim that an actual quadratic-character flat prefix exists unless Lean
certifies one.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | Compared H10 function-field transfer, H2 density, H11 statistics, and ranked D10 arithmetic/Speiser. H10's finite endpoint is complete; H2/H11 lack an exceptional-zero localizer; D10 is the highest-ranked untested door. | Select a theorem-producing audit of Conrey's exact finite proof step before the global character-sum inequality. |
| 2 | `SOURCE_AUDIT / FALSIFICATION_RECONNAISSANCE` | Read the peer-reviewed source through Theorem 6 and Proposition 1. The rationality proof omits `B_m=0`; the paper later writes the same flat branch but does not exclude it. Exact scans found no actual character counterexample below the recorded bounds. | Preregister the corrected dichotomy and generic irrational countermodel. Keep the published proposition open rather than labeling it refuted. |
| 3 | `COMPACTION_RECOVERY / USER_ROUTE_RULING` | Re-read the canonical governance and campaign records after an inherited summary. The user fixed the survey's purpose as a search for overlooked branches across the major historical routes before original-route work becomes the main allocation; conjecture proposal and testing remain open throughout. | Preserve H9 as the next value-ranked omission audit, publish its preregistration first, and keep cross-family coverage as the default successor rule. |
| 4 | `LEAN_IMPLEMENTATION` | Compiled the exact finite weighted-prefix identity, proved that zero first moment makes the prefix constant in its scale, proved the exhaustive flat-or-explicit-rational dichotomy, and checked a rational-parameter `sqrt(2)` countermodel. Five exact TargetChecks and five selected axiom prints pass; the full 8,741-job build passes. | Classify the generic rationality inference as formally falsified while keeping the actual quadratic-character Proposition 1 open. Publish the frozen implementation and require public CI. |
| 5 | `IMPLEMENTATION_CI` | Implementation commit `4c9939496e6a508c2f5e631ad3fa5ede9f5a69aa` passed Lean Action run `29940099631`, build job `88991480954`, in `1m56s`. | Freeze Lean proof source. Publish immutable implementation evidence and require its own public CI. |

## Compiled declarations

- `conreyWeightedPrefix_eq_mass_sub_moment_div`;
- `conreyWeightedPrefix_eq_mass_of_moment_eq_zero`;
- `conreyAffineFraction_eq_dichotomy`;
- `conreyAffineFraction_eq_rat_or_flat`;
- `conreyAffineRationalityInference_counterexample`.

Definition alignment is recorded in
`research/h9_conrey_rationality_definition_alignment_20260723.md`.

## Assumption and gap accounting

- `assumption_frontier_before`: unseparated zero numerator in the affine-fraction inference.
- `target_reduction`: rational branch plus an explicit flat-prefix obstruction.
- `hard_gap_before`: prove source positivity or obtain a character-sum/Speiser localizer excluding
  every off-line zeta zero.
- `rh_frontier_before`: RH open.
- `current_result`:
  `PROVED / SOURCE_GENERIC_INFERENCE_FALSIFIED / ACTUAL_CHARACTER_PROPOSITION_OPEN`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `source_proof_gap_delta`: `1`.
- `obstruction_map_delta`: `1`.
- `mechanical_gates`: production module, Targets entry, five exact TargetChecks, five selected
  standard-only axiom prints, forbidden scan, and `git diff --check` pass; full `lake build`
  passes with `8,741` jobs.
- `implementation_commit`: `4c9939496e6a508c2f5e631ad3fa5ede9f5a69aa`.
- `implementation_public_ci`: Lean Action run `29940099631`, build job `88991480954`, passed in
  `1m56s`.
- `proof_source_state`: frozen at the implementation commit.
- `next_gate`: immutable evidence commit and public CI.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
