# H7 Finite Weil Matrix and Parity Attempt

Campaign: `LITERATURE-20260722-H7-WEIL-FINITE-MATRIX-PARITY-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: one inherited compaction. Governance, HANDOFF, Targets, TargetChecks, the
  closed H7 alignment attempt and preregistration, DAG, portfolio, external ACTIVE ledger, and git
  state were reread before route selection.
- `global_goal`: active.

## Baseline

- `parent_commit`: `9ab3bf45101226f731b371a11ec06b149fa11a9a`.
- `baseline_public_ci`: run `29925232284`, build job `88940549581`, passed in `1m55s`.
- `selected_node`: `H7-WEIL-GROUNDSTATE-FINITE-MATRIX-01`.
- `preregistration`: `research/h7_weil_finite_matrix_parity_prereg_20260722.md`.

## Preregistered endpoint

Formalize the exact source divided-difference matrix and reflection parity split. Prove that
strict Rayleigh positivity on the even orthogonal complement of one normalized even eigenvector,
together with strict Rayleigh positivity on the whole odd block, makes that eigenvector the unique
global ground state. The theorem must expose an executable target for later exact or interval
certificates without assuming the source's unproved simple-even condition.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `RECOVERY / SOURCE_AND_CERTIFICATE_AUDIT` | Recovered the public H7 M0 frontier. Re-read the 2025 divided-difference, reflection, commutator, and even-simple definitions; audited the July 2026 matrix code, Arb inertia certificate, finite-height errata, and even-sector eigenflow. | Existing evidence neither proves nor falsifies simple-even. Select an exact finite matrix/parity checker as a separate literature campaign. |
| 2 | `PREREGISTRATION` | Fixed the source matrix, parity decomposition, strict two-block Rayleigh certificate, numerical-evidence boundary, and local stopping rule. No Lean proof source was edited. | Publish preregistration alone and require public CI before implementation. |

## Assumption and gap accounting

- `assumption_frontier_before`: source matrix structure is published, while simple-even is an
  explicit missing assumption and no project theorem checks it.
- `hard_gap_before`: uniform simple-even ground-state structure and the actual
  `xi_lambda -> k_lambda` comparison are open.
- `rh_frontier_before`: RH open.
- `current_result`: `PREREGISTERED_ONLY`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `next_gate`: preregistration commit and public CI.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
