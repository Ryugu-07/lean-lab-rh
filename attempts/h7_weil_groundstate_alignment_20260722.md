# H7 Finite-Prime Weil Ground-State Alignment Attempt

Campaign: `LITERATURE-20260722-H7-WEIL-GROUNDSTATE-ALIGN-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION_LOCAL / PUBLIC_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: none in this campaign.
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

## Initial correction and exact risk

- Connes 2026 already proves the `k_lambda` Fourier-transform limit to `Xi`; the open limit is
  the true ground state `xi_lambda` versus `k_lambda`, not `k_lambda` versus `Xi`.
- The July 2026 finite dictionary may close the finite coefficient-to-test part of M0, but it is
  explicitly one-way and does not prove continuum simple-even structure or the true-ground-state
  limit.
- The expected coordinate conjugacy is
  `g(x)=exp(-x/2)*f(x+L/2)`. It has not yet been compiled in Lean.
- The project's named `compactWeilArithmeticQuadratic` is pole-free after two endpoint moments;
  the source finite matrix includes the pole block. Direct equality without this distinction is
  forbidden.

## Next gate

Commit the preregistration and synchronized route ledgers, push to public `main`, and require green
Lean Action CI. Only then may the fourteen-row alignment record or any Lean bridge be written.

