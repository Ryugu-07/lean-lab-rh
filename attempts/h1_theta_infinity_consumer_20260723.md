# H1 Theta-Infinity Consumer Attempt

Campaign: `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `5e36c53da657b4018f23339d4744562da07002ba`.
- `parent_public_ci`: run `29965855724`, build job `89077075898`, passed in `1m51s`.
- `selected_node`: `H1-FARMER-BETTIN-GONEK-THETA-INFINITY-01`.
- `preregistration`: `research/h1_theta_infinity_consumer_prereg_20260723.md`.
- `global_goal`: active.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `H7_PUBLIC_CLOSURE` | H7 final-ledger commit `5e36c53da657b4018f23339d4744562da07002ba` passed run `29965855724`, job `89077075898`, in `1m51s`. | Close only the generic H7 campaign; resume historical mechanism-level selection. |
| 2 | `PRIMARY_SOURCE_AUDIT` | Bettin--Gonek Theorem 1 shows a fixed long-mollifier exponent excludes every zero in `Re(s)>1/2+1/(2*theta)`; arbitrary `theta` implies RH. | Correct the route map: the full `theta=infinity` route is stronger than a bare proportion-one result. |
| 3 | `PROOF_SPINE_AUDIT` | Equations `(2.1)`--`(2.5)` turn one off-line zero into a residue lower bound and then into `T^(2*beta*theta) << T^(1+epsilon+theta)`. | Separate the exact final exponent consumer from the still-open Mellin/residue analytic bridge. |
| 4 | `QUANTIFIER_AUDIT` | The theorem states uniform integer-cutoff control, while the proof integrates over real cutoffs after extending `M_x`. The normalized polynomial is affine in `1/log x` between consecutive integers. | Require Lean to prove the interpolation and its convex squared-norm consequence; do not silently pass from integer to real cutoffs. |
| 5 | `PREREGISTRATION` | Exact source objects, interpolation, exponent boundary, fixed/all-theta consumers, claim limits, and stop rules are locked. | Publish preregistration and require public CI before proof-source edits. |

## Frontier accounting

- `hard_gap_before`: unconditional arbitrary-length mollified moment bounds and the full formal
  Mellin/residue transfer from such bounds to an individual-zero power obstruction.
- `rh_frontier_before`: RH open.
- `target_delta`: source definition alignment plus two consumer edges; no unconditional gap delta.
- `route_map_delta`: correct the false compression of `theta=infinity` into a proportion-one-only
  mechanism.
- `falsification_target`: one fixed positive `theta` permits a nonempty strip between the critical
  line and its quasi-RH boundary.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
