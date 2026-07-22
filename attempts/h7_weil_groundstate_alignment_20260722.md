# H7 Finite-Prime Weil Ground-State Alignment Attempt

Campaign: `LITERATURE-20260722-H7-WEIL-GROUNDSTATE-ALIGN-01`

Mode: `LITERATURE`

Status: `IMPLEMENTATION_PUBLIC_CI_PASSED / EVIDENCE_COMMIT_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: one inherited compaction, recovered under the current governance protocol.
- `global_goal`: active.

## Baseline

- `parent_commit`: `051ace38c80aebcde083432297c9fa01e02539e4`.
- `baseline_public_ci`: run `29921844064`, build job `88929023824`, passed in `2m1s`.
- `selected_node`: `H7-WEIL-GROUNDSTATE-ALIGN-01`.
- `preregistration`: `research/h7_weil_groundstate_alignment_prereg_20260722.md`.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `RECOVERY / SOURCE_INVENTORY` | Re-read governance and the public survey frontier; audited source TeX for arXiv:2511.23257, 2511.22755, 2602.04022, 2605.20224, and 2607.02828 against the project compact Weil modules. | Preregister an itemized M0 campaign before any Lean proof-source edit. |
| 2 | `PREREGISTRATION_PUBLIC_CI` | Commit `0e1941d05c2f0a9faa166170e93a017f121fe9f6` passed run `29922818186`, build job `88932298080`, in `1m33s`. | Begin the itemized alignment and weighted-coordinate Lean bridge. |
| 3 | `M0_ALIGNMENT / LEAN_BRIDGE` | Completed all fourteen rows in `research/h7_weil_groundstate_alignment_20260722.md`. Lean compiles the weighted involution, autocorrelation, positive-sign transform, source negative-sign coordinate `s=1/2-i*z`, and both source pole moments. Exact witnesses and selected axiom prints pass. | Classify `MEANINGFUL_PARTIAL`: algebraic alignment succeeds, while the source Galerkin class cannot directly instantiate the project's globally smooth compact criterion. Close this campaign after full build/public CI; make finite matrix/parity formalization and spectral falsification a separate child. |
| 4 | `IMPLEMENTATION_PUBLIC_CI` | Implementation commit `0ed05ba49605c7de621f16193ff73dd63a7bbabb` passed run `29924570570`, build job `88938283725`, in `1m56s`. | Backfill immutable evidence without changing Lean source; require the evidence commit to pass its own public CI. |

## Initial correction and exact risk

- Connes 2026 already proves the `k_lambda` Fourier-transform limit to `Xi`; the open limit is
  the true ground state `xi_lambda` versus `k_lambda`, not `k_lambda` versus `Xi`.
- The July 2026 finite dictionary may close the finite coefficient-to-test part of M0, but it is
  explicitly one-way and does not prove continuum simple-even structure or the true-ground-state
  limit.
- The coordinate conjugacy `g(x)=exp(-x/2)*f(x+L/2)` now compiles in Lean. Source ordinate `z`
  maps to project parameter `s=1/2-i*z`; the initially implicit Fourier sign has been corrected
  and compiled.
- The project's named `compactWeilArithmeticQuadratic` is pole-free after two endpoint moments;
  the source finite matrix includes the pole block. Direct equality without this distinction is
  forbidden.

## Local outcome

- `classification`: `MEANINGFUL_PARTIAL / WEIGHTED_COORDINATE_ALIGNMENT_COMPILED /
  SOURCE_PROJECT_DOMAIN_GAP_EXPOSED`.
- `rh_frontier_delta=0`, `hard_gap_delta=0`, `route_infrastructure_delta=1`,
  `obstruction_map_delta=1`.
- `OBS-H7-WEIL-ALIGN-REGULARITY-01`: generic source trigonometric vectors extended by zero are not
  globally `C infinity`; smoothing changes the finite form and is not an equality repair.
- Eight exact TargetChecks and eight selected axiom prints pass locally; selected declarations use
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Full project build passed with `8,737` jobs. Implementation commit
  `0ed05ba49605c7de621f16193ff73dd63a7bbabb` passed public run `29924570570`, build job
  `88938283725`, in `1m56s`. Evidence backfill and final ledger remain.
- Proposed independent child after closure: formalize the exact source finite matrix and parity
  blocks, then run `FALSIFICATION` against simple/even ground-state uniformity before an infinite
  spectral proof attempt.
