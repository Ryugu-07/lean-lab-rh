# H1 Short-Mollifier Variational Attempt

Campaign: `LITERATURE-20260722-H1-SHORT-MOLLIFIER-VARIATIONAL-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: no compaction in this campaign so far; parent records include one recovery.
- `global_goal`: active.

## Baseline

- `parent_commit`: `7e15cfb386e961f7437dfa25d39b6cab85d3946b`.
- `parent_public_ci`: run `29934044666`, build job `88970856616`, passed in `1m37s`.
- `selected_node`: `H1-SHORT-MOLLIFIER-VARIATIONAL-01`.
- `preregistration`: `research/h1_short_mollifier_variational_prereg_20260722.md`.
- `primary_source`: arXiv:2508.11108v1, equations `(58)`-`(63)`.

## Preregistered endpoint

Prove that the source parameter condition `c < 1/4` makes the general short-mollifier variational
functional strictly convex on fixed-endpoint paths. The proof must compile the exact weighted
Hardy identity, align source `K/c1` with the normalized energy, derive the exact energy gap from
the Euler-Lagrange equation, and conclude unique global minimality without hypergeometric or
numerical premises.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | Compared the closed H7 residual with H1 mollifiers, H2 density, H11 statistics, and H10 function-field transfer. H2/H11 still lack an exceptional-zero localizer and H10 lacks a number-field trace object. H1 contains a source-identified underused derivative-combination freedom and an exact continuum variational target. | Select H1 rather than continue H7 scalar optimization. Keep sparse-exception and arithmetic mean-value barriers explicit. |
| 2 | `SOURCE_AUDIT / PREREGISTRATION` | Read arXiv:2508.11108v1 equations `(12)`-`(31)` and `(58)`-`(63)`. The source gives the Euler-Lagrange solution under `c < 1/4`; the discriminating Lean endpoint is global-minimizer sufficiency via the weighted `1/4` Hardy threshold, not a decimal proportion. | Publish preregistration alone. Require public CI before any Lean proof-source edit. |

## Assumption and gap accounting

- `assumption_frontier_before`: Euler-Lagrange stationarity plus source endpoints.
- `target_reduction`: prove coercivity and the exact energy gap, thereby justifying unique global
  minimality over the represented path class.
- `hard_gap_before`: unconditional long/twisted mean values sufficient for proportion one and a
  quantitative exceptional-zero eliminator.
- `rh_frontier_before`: RH open.
- `current_result`: `PREREGISTERED_ONLY`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `next_gate`: preregistration commit and public CI.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
