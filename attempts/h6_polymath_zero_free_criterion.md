# H6 Polymath Zero-Free-Region Criterion Campaign

Campaign: `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`

Date: 2026-07-17

Status: `PREREGISTRATION_CI_PENDING`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: no

## Normalized Tuple

- `statement`: the complete Polymath three-region zero-free criterion, its exact
  `t0+y0^2/2` all-real endpoint, and the Table 1 second-row corollary at time `1/5`
- `assumptions`: only the three explicit source region predicates and positivity constraints on
  `t0`, `X`, and `y0`; standard Mathlib analysis and compiled source-normalized H6 infrastructure
- `strategy`: compact first-contact time, repeated-zero backward Hermite splitting,
  arbitrary-complex simple-zero force geometry, and general strip contraction
- `known_obstacle`: repeated-zero splitting is absent; the exported simple-zero implicit path is
  real-only; the force estimate must be lifted to arbitrary complex boundary zeros without a
  global zero enumeration
- `nearest_primary_source`: Polymath arXiv `1904.12438`, Proposition 3.3, Theorem 1.2, and Table 1;
  Platt--Trudgian arXiv `2004.09765`, Corollary 2
- `nearest_project_attempt`: H6-H2e supplies only the final strip contraction; the zero-dynamics
  campaign supplies simple real paths and the regularized force but explicitly leaves repeated
  zeros and global continuation open
- `new_attack_angle`: use a compact first-contact set and complete both source collision branches,
  rather than assume a global strip or continue only real simple zeros

## Loop Ledger

| Loop | Mode | Result | Decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION -> LITERATURE` | Compared H6-Q, strict-below-0.2, W2, M2, H1/H2 counts, and H10. Primary-source review identifies Polymath Proposition 3.3 as the first structural consumer of the newly compiled general strip theorem. It requires real new analysis: compact first contact, repeated-zero Hermite splitting, and complex simple-zero force geometry. | Preregister the complete criterion and exact table-row corollary; require public CI before proof edits. |

## Current Accounting

- `hard_gap_before`: the initial, final, and barrier region certificates, H6-E/G8, and RH open
- `hard_gap_after`: unchanged
- `hard_gap_delta`: 0
- `classification`: `PREREGISTERED_CI_PENDING`
- `next_gate`: public preregistration CI
- `persistent_goal`: active
