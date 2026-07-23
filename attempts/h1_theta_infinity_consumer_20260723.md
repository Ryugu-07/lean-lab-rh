# H1 Theta-Infinity Consumer Attempt

Campaign: `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

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
| 6 | `PREREGISTRATION_PUBLIC_CI` | Commit `1cb89557a3630778270da171ba59d87b1fa1f132` passed run `29966502725`, build job `89079059819`, in `1m56s`. | Open the fixed proof-source gate; implement interpolation before the zeta-specific consumers. |
| 7 | `SOURCE_OBJECT_ALIGNMENT` | Defined the exact logarithmic taper, real-cutoff Mobius mollifier, critical-line coordinate, mollified second moment, uniform fixed-theta moment bound, and theta-infinity conjecture. | Keep the conjecture and moment-to-power bridge as open propositions; no theorem may establish them by definition. |
| 8 | `REAL_CUTOFF_INTERPOLATION` | Lean proves the affine `1/log x` interpolation, endpoint coefficient vanishing, coefficient membership in `[0,1]`, pointwise complex norm-square convexity, continuity, interval integrability, and the source moment interpolation inequality. | The integer-to-real quantifier passage in the paper is valid; record no source gap here. |
| 9 | `POWER_AND_ZERO_CONSUMERS` | Lean proves the exact exponent boundary, fixed-theta zeta zero-free half-plane, all-theta RH consumer through functional-equation reflection, and a fixed-theta off-line boundary witness. | Correctly separate quasi-RH at one theta from RH at all theta. Keep the analytic moment-to-power bridge open. |
| 10 | `TARGET_AND_AXIOM_GATES` | Two proven and two open Targets, 12 exact TargetChecks, and 12 selected axiom prints compile. Every selected theorem uses only the standard three axioms. | Run the production scan, diff checks, full build, and public implementation CI. |
| 11 | `LOCAL_MECHANICAL_CLOSURE` | The production forbidden scan is empty, `git diff --check` passes, and the full `8,751`-job build succeeds. | Freeze the registered implementation endpoint and publish it for independent Lean Action CI. |
| 12 | `IMPLEMENTATION_PUBLIC_CI` | Frozen implementation commit `ed9fb11e3293e80a86561f30eb05073bfbf0b7ab` passed run `29967710426`, build job `89082709000`, in `2m3s`. | Keep Lean proof source frozen; publish immutable evidence and require its own public CI. |

## Frontier accounting

- `hard_gap_before`: unconditional arbitrary-length mollified moment bounds and the full formal
  Mellin/residue transfer from such bounds to an individual-zero power obstruction.
- `rh_frontier_before`: RH open.
- `target_delta`: source definition alignment plus two consumer edges; no unconditional gap delta.
- `route_map_delta`: correct the false compression of `theta=infinity` into a proportion-one-only
  mechanism.
- `falsification_target`: one fixed positive `theta` permits a nonempty strip between the critical
  line and its quasi-RH boundary.
- `local_result`: `FULL_SUCCESS_AT_CONSUMER_ENDPOINT` locally. The source objects,
  real-cutoff interpolation, moment convexity, exponent consumer, fixed-theta zero-free theorem,
  all-theta RH consumer, and fixed-theta witness pass the full `8,751`-job build.
- `hard_gap_after`: `H1-BETTIN-GONEK-MOMENT-TO-POWER-01` and
  `H1-FARMER-THETA-INFINITY-MOMENT-01` remain open and unavailable as premises.
- `definition_alignment`:
  `research/h1_theta_infinity_consumer_definition_alignment_20260723.md`.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
