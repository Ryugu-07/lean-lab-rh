# H7 Finite Herglotz Criterion Attempt

Campaign: `LITERATURE-20260722-H7-WEIL-HERGLOTZ-CRITERION-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: no compaction in this campaign so far; parent records include two recoveries.
- `global_goal`: active.

## Baseline

- `parent_commit`: `c5ba3ab66e9a61446da7ad43d3a1d3786efd220d`.
- `baseline_public_ci`: run `29930876406`, build job `88959943824`, passed in `1m45s`.
- `selected_node`: `H7-WEIL-GROUNDSTATE-HERGLOTZ-01`.
- `preregistration`: `research/h7_weil_herglotz_criterion_prereg_20260722.md`.

## Preregistered endpoint

Prove the exact finite rank-one Herglotz criterion on the reflection-odd sector: for a strictly
positive pole-free shifted form `P`, odd pole vector `S`, and odd resolvent vector `u` satisfying
`P*u=S`, strict positivity after the source update `P-2*S*S^T` is equivalent to
`2*(S dot u)<1`. Connect that iff to the compiled parity Rayleigh certificate without asserting
the arithmetic scalar bound.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION / SOURCE_AUDIT` | Compared the H7 true-ground-state limit, H1 runner-up, and four direct June 2026 Perron/Loewner/Herglotz sources. The scalar odd-sector criterion is the narrowest human frontier that directly consumes the public finite matrix/parity interface. | Select a separate finite Herglotz criterion campaign. Keep all S3 operator and arithmetic claims outside the premise set. |
| 2 | `PREREGISTRATION` | Fixed the completion-of-square identity, strict-positivity iff, certificate consumer, source sign, threshold, assumptions, and local stop. No Lean proof source was edited. | Publish preregistration alone and require public CI before implementation. |

## Assumption and gap accounting

- `assumption_frontier_before`: all-vector strict odd Rayleigh positivity.
- `target_reduction`: pole-free odd positivity plus one scalar resolvent inequality.
- `hard_gap_before`: prove that scalar inequality uniformly for the arithmetic matrices; prove the
  actual ground-state-to-`k_lambda` comparison.
- `rh_frontier_before`: RH open.
- `current_result`: `PREREGISTERED_ONLY`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `next_gate`: preregistration commit and public CI.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
