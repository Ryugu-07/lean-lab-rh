# H6 Zero-Dynamics Proof Attempt

Campaign: `PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01`

Status: `ACTIVE`

## Target

- `mode`: `PROOF-ATTEMPT`
- `node_id`: H6-E / G8
- `exact_mathematical_statement`: prove every zero of the exact source-normalized `H_0` is real.
- `proposed_lean_statement`: `deBruijnNewmanAllZerosReal 0`.
- `relation_to_RH`: exact equivalent endpoint.
- `success_criterion`: compile the unconditional theorem and all mechanical/public gates.
- `falsification_criterion`: falsify a fixed force-law clause or record the first exact collision
  estimate that the attack cannot establish; no such failure falsifies RH.

## Prior state

- `assumption_frontier_before`: H6 source alignment, heat PDE, order-one Hadamard product, exact
  real-zero predicate, closedness, forward preservation, quantitative strip contraction, and
  `deBruijnNewmanAllZerosReal (1/2)` are public.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH are open.
- `known_obstacles`: real-rootedness can fail backward only through zero collision; the needed
  uniform theta-specific gap/collision estimate is open. Infinite zero forces require a proved
  summation convention and multiplicity handling.
- `nearest_primary_source`: Rodgers-Tao arXiv `1801.05914v5`, Theorem 4.1; Csordas-Smith-Varga
  (1994).
- `nearest_project_attempt`: H6-H2d reaches the exact positive witness but gives no backward
  collision exclusion; `OBS-H6-REVERSE-HEAT-LI-01` rules out a generic reverse-Li mechanism.
- `new_attack_angle`: derive an absolutely convergent divisor-indexed force law directly from the
  compiled genus-one product, then use actual theta-kernel information to attack collisions.

## Route-selection loop

- Re-read canonical V4.1 governance, HANDOFF, Targets, the hard-gap DAG, route cards, portfolio,
  and the publicly closed H6-H2d attempt after inherited-summary compaction.
- Ranked H1/H2 finite counts below direct open nodes because aggregate counts cannot remove one
  exceptional zero.
- Deferred H6-Q because its certified numerical stack is absent and it remains short of G8.
- Found no materially new W2 or M2 mechanism beyond the recorded prime-kernel and projection
  obstructions.
- Selected H6 zero dynamics because the heat PDE and Hadamard divisor are now both compiled, and
  their combination targets the exact backward-collision mechanism between `1/2` and `0`.
- Fixed first endpoint: summable regularized divisor force, simple-zero derivative ratio, and
  differentiable zero-path velocity. Fixed campaign endpoint remains `H_0` all-real zeros.
- `result`: preregistration prepared; public CI required before Lean proof edits.
- `hard_gap_delta`: 0.
- `route_infrastructure_delta`: 0.

## Attempt log

Public preregistration passed. Exact architecture and adversarial checks are in
`research/h6_zero_dynamics_force_prereg_20260717.md`.

### Implementation loop 1: regularized force and path velocity

- Removed the complete multiplicity fiber over `r` from the genus-one canonical product and
  proved genuine summability of the remaining regularized divisor terms.
- Proved that a simple zero has divisor-fiber cardinality one, split the global Hadamard product,
  and rewrote its removed factor as `(z-r)*(-exp(z/r)/r)`.
- Differentiated the exact factorization twice and proved
  `H_t''(r)/(2*H_t'(r)) = deBruijnNewmanRegularizedZeroForce t r`.
- Added joint continuity of the first and second source moments. The two continuous partial
  derivatives give a strict real Frechet derivative of `(t,z) |-> H_t(z)`.
- Applied that joint derivative and the backward heat equation to an arbitrary path differentiable
  at the selected time. Lean proves the exact source sign and factor
  `x'(t)=2*deBruijnNewmanRegularizedZeroForce t (x t)` at every simple path zero.
- The force interface is known mathematics and passes the fixed first-spine criterion. It does not
  construct zero paths, control repeated zeros, exclude collisions, or prove the time-zero target.
- `result`: first formalization spine locally complete; campaign remains active at architecture
  step 6 (construct and order local real simple-zero trajectories).
- `hard_gap_delta`: 0.
- `route_infrastructure_delta`: 1, verified by public implementation CI.

## Mechanical audit

- exact module compilation: `DeBruijnNewmanDynamics.lean` passes without diagnostics.
- `Targets.lean`: exact source-force target registered and compiles.
- `TargetChecks.lean` exact witness: five new exact witnesses compile.
- `AxiomsAudit.lean` and printed axioms: all five selected declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- forbidden token/declaration/resource scan: empty after a syntax-narrow declaration rescan.
- witness audit: summability, ratio, mixed chain rule, and path velocity statements witnessed.
- definition/source alignment: the divisor regularization, heat sign, and factor two match the
  preregistered Rodgers-Tao convention.
- `git diff --check`: passes.
- full `lake build`: passes with 8,691 jobs.
- public implementation CI: commit `ce65db1c0379a4accfef579c9e8c08995662dc19` passed Lean
  Action run `29534356022`, build job `87741989620`, in `2m36s`.

## Runtime record

- `model`: GPT-5 Codex (exact exposed runtime model identifier unavailable).
- `reasoning_effort`: not exposed.
- `budget`: no token budget.
- `compaction_state`: inherited summary detected; canonical recovery files re-read before route
  selection.
- `commit_and_CI`: preregistration commit `4405d60c2a33444f8ae43f2406631cc80faff356`;
  public Lean Action CI run `29532612360`, build job `87736257748`, passed in `2m29s`.
  Implementation commit `ce65db1c0379a4accfef579c9e8c08995662dc19` passed public run
  `29534356022`, build job `87741989620`, in `2m36s`.

## Result

- `result_class`: active direct proof attempt; known first spine formalized locally.
- `assumption_frontier_after`: exact summable divisor force, simple-zero derivative ratio, joint
  time-space Frechet derivative, and differentiable simple-zero path velocity.
- `hard_gap_after`: H6-E/G8, W2/G7, M2/G3, and RH remain open.
- `hard_gap_delta`: 0.
- `OBS_node`: none yet.
- `theorem_names`: `summable_deBruijnNewman_regularizedZeroForceTerm`,
  `deBruijnNewmanH_second_deriv_div_two_deriv_eq_regularizedZeroForce`,
  `hasDerivAt_deBruijnNewmanH_along`, `deBruijnNewman_simpleZeroPath_velocity`.
- `failure_or_obstacle`: the first spine succeeds; local trajectory construction and the first
  theta-specific collision inequality remain to be attempted, so no obstruction node is yet due.
- `route_selection_decision`: remain in the fixed H6-E campaign and proceed to local real
  simple-zero trajectories after public implementation CI.
