# H6 Zero-Dynamics Proof Attempt

Campaign: `PROOF-ATTEMPT-20260717-H6-ZERO-DYNAMICS-01`

Status: `PUBLIC_OBSTRUCTION_RECORDED`

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

### Implementation loop 2: local trajectories and pair-removed gap dynamics

- Applied Mathlib's product-domain real implicit-function theorem to the compiled joint strict
  Frechet derivative at an arbitrary simple real zero.
- Proved a locally unique differentiable complex zero path. Conjugation symmetry maps that path
  to a second nearby zero path, so local uniqueness forces zero imaginary part near the anchor.
- Constructed two such paths at distinct simple real zeros and proved that their real parts remain
  locally ordered.
- Generalized the velocity theorem from globally zero-valued paths to paths that are zero-valued
  eventually in the selected time neighbourhood; this is the exact interface needed by the local
  implicit function.
- Proved the exact complex-gap, real-gap, and squared-real-gap derivative laws.
- Removed both complete simple-zero divisor fibers from the force difference and proved the
  remaining term genuinely summable. Lean verifies
  `force(t,s)-force(t,r)=2/(s-r)+pairRemainder(t,r,s)`.
- Substitution into the squared-gap law gives the exact real anchored identity
  `(gap^2)'=8+4*gap*Re(pairRemainder)`. The constant `8` is the mutual pair interaction, not part
  of the remainder definition.
- This completes local trajectory construction and narrows the next attack to global continuation
  plus a theta-specific integrated estimate on the pair-removed remainder. A height-uniform
  positive absolute gap is not adopted as a target; shrinking mean zero spacing makes that the
  wrong global shape.
- `result`: loop 2 locally complete; campaign remains active and the next loop must attempt the
  theta-specific remainder estimate rather than another dynamics wrapper.
- `hard_gap_delta`: 0.
- `route_infrastructure_delta`: 1 at campaign level; no unconditional collision exclusion yet.

### Implementation loop 3 preregistration: adjacent-pair remainder sign

- `mode`: `PROOF-ATTEMPT` inside the active H6-E campaign.
- `fixed_statement`: at a time when every zero of `H_t` is real, let `r<s` be distinct simple
  real zeros with no real zero strictly between them. Prove that every term in the pair-removed
  remainder has nonpositive real part, hence
  `Re(pairRemainder(t,r,s)) <= 0` and `(gap^2)' <= 8` along the corresponding local paths.
- `proposed_lean_surfaces`: a source-divisor-index zero theorem, an exact adjacent-real-zero
  predicate, `deBruijnNewmanZeroPairForceRemainder_re_nonpos`, and a derivative upper-bound
  corollary of the public pair-remainder law.
- `success_criterion`: exact statements compile without new axioms; TargetChecks, selected axiom
  prints, forbidden scans, full build, and public CI pass.
- `relation_to_RH`: this is a collision-estimate component below H6-E/G8, not the unconditional
  time-zero theorem. It may be used only at already-good times and cannot assume the desired
  all-real property at time zero.
- `known_limitation`: integrating only `(gap^2)'<=8` backward yields a persistence interval scaled
  by the terminal squared gap. Since high-zero gaps shrink, this has no immediate height-uniform
  interval. The loop must test this limitation explicitly before selecting a successor statement.
- `adversarial_nonadjacent_test`: if an additional real zero lies strictly between `r` and `s`,
  its pair term is positive because the two denominators have opposite signs; adjacency is
  indispensable.
- `adversarial_lattice_test`: for a bi-infinite equally spaced real lattice, the other-zero
  remainder formally equals `-2/gap`, so it exactly cancels the mutual `8` contribution and the
  squared-gap derivative is zero. The sign theorem is therefore generic real-zero geometry, not
  theta-specific control.
- `multiplicity_test`: repeated divisor indices outside the selected fibers repeat a nonpositive
  term and preserve the sign; the selected simple fibers are still required for the exact mutual
  coefficient.
- `falsification_criterion`: a divisor index need not be an actual source zero, a remaining
  adjacent real term can be positive, or the complex-to-real `tsum` transport is invalid.
- `hard_gap_delta_expected`: 0 unless a genuinely uniform theta-specific continuation theorem is
  subsequently compiled.
- `route_infrastructure_delta_expected`: 1 at campaign level if the exact sign interface compiles.

### Implementation loop 3 result: sharp adjacent-gap bound and generic obstruction

- Proved that every multiplicity-bearing divisor index represents an actual source zero.
- Defined exact adjacency for real source zeros and proved every remaining pair-force term has
  nonpositive real part at an all-real time. Summability plus `Complex.re_tsum` gives
  `Re(pairRemainder(t,r,s)) <= 0`.
- Proved the adversarial converse boundary: a real zero strictly between the selected endpoints
  contributes positively. The adjacency hypothesis is therefore mathematically necessary.
- Combined the sign theorem with the public pair-removed law to compile the exact derivative and
  bound `(gap^2)'=8+4*gap*Re(pairRemainder) <= 8`.
- Integrated this bound over an interval of adjacent real simple-zero paths, obtaining
  `gap(a)^2 >= gap(b)^2-8*(b-a)`.
- Added `H6GapVelocityAudit.lean`, an exact quadratic family satisfying the same backward heat
  equation. Its terminal zeros are distinct and simple with gap `epsilon`, and they collide into
  a double zero after backward time `epsilon^2/8`.
- Lean proves that such a collision occurs inside every proposed positive uniform interval. Thus
  the generic adjacent-gap bound is sharp and cannot by itself give height-uniform continuation.
- `result`: local obstruction `OBS-H6-ADJACENT-GAP-EIGHT-01` recorded. This eliminates only the
  generic adjacent-gap branch; it does not falsify theta-specific continuation, H6-E, or RH.
- `hard_gap_delta`: 0.
- `route_infrastructure_delta`: 1 remains unchanged at campaign level.
- `successor_state`: `ROUTE_SELECTION`; any renewed H6-E attack must preregister a genuinely
  theta-specific estimate or a different repeated-zero mechanism.

## Mechanical audit

- exact module compilation: `DeBruijnNewmanDynamics.lean` and `H6GapVelocityAudit.lean` pass
  without diagnostics.
- `Targets.lean`: source-force, local-trajectory, and adjacent-gap sharpness targets compile.
- `TargetChecks.lean`: five first-spine, six loop-2, and seven loop-3 exact witnesses compile.
- `AxiomsAudit.lean` and printed axioms: all five first-spine, seven loop-2, and seven loop-3
  selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- forbidden token/declaration/resource scan: empty after a syntax-narrow declaration rescan.
- witness audit: summability, ratio, mixed chain rule, path velocity, local uniqueness/reality,
  local ordering, pair-force decomposition, adjacent sign, integrated gap bound, and sharp
  quadratic collision model witnessed.
- definition/source alignment: the divisor regularization, heat sign, and factor two match the
  preregistered Rodgers-Tao convention.
- `git diff --check`: passes.
- full `lake build`: loop 3 passes with 8,692 jobs; warnings replayed only from pre-existing files.
- public implementation CI: commit `ce65db1c0379a4accfef579c9e8c08995662dc19` passed Lean
  Action run `29534356022`, build job `87741989620`, in `2m36s`.
- public loop-2 implementation CI: commit `03ce2ac2ee68b7d9a6d48d56aed37ab40836c30d`
  passed Lean Action run `29536815968`, build job `87750004173`, in `1m54s`.
- public loop-2 evidence CI: commit `5debf07e9412255dd86a0ecf8f8c6c12993f1818` passed Lean
  Action run `29537039585`, build job `87750713877`, in `1m47s`.
- public loop-3 implementation and obstruction CI: commit
  `ce5b0c405f06078f549c6a27a477df04ccbcfb35` passed Lean Action run `29538670221`, build job
  `87755892757`, in `1m58s`.

## Runtime record

- `model`: GPT-5 Codex (exact exposed runtime model identifier unavailable).
- `reasoning_effort`: not exposed.
- `budget`: no token budget.
- `compaction_state`: inherited summary detected; canonical recovery files re-read before route
  selection.
- `commit_and_CI`: preregistration commit `4405d60c2a33444f8ae43f2406631cc80faff356`;
  public Lean Action CI run `29532612360`, build job `87736257748`, passed in `2m29s`.
  Implementation commit `ce65db1c0379a4accfef579c9e8c08995662dc19` passed public run
  `29534356022`, build job `87741989620`, in `2m36s`. Loop-2 implementation commit
  `03ce2ac2ee68b7d9a6d48d56aed37ab40836c30d` passed public run `29536815968`, build job
  `87750004173`, in `1m54s`; loop-2 evidence commit
  `5debf07e9412255dd86a0ecf8f8c6c12993f1818` passed run `29537039585`, build job
  `87750713877`, in `1m47s`. Loop-3 implementation commit
  `ce5b0c405f06078f549c6a27a477df04ccbcfb35` passed run `29538670221`, build job
  `87755892757`, in `1m58s`.

## Result

- `result_class`: public obstruction recorded. The direct H6-E endpoint remains open and the
  persistent RH Goal returns to route selection.
- `assumption_frontier_after`: exact summable divisor force, simple-zero derivative ratio, joint
  time-space Frechet derivative, locally unique real simple-zero paths, local ordering, and the
  exact pair-removed squared-gap law; at all-real times, adjacent pairs additionally satisfy the
  sharp integrated bound `gap(a)^2 >= gap(b)^2-8*(b-a)`.
- `hard_gap_after`: H6-E/G8, W2/G7, M2/G3, and RH remain open.
- `hard_gap_delta`: 0.
- `OBS_node`: `OBS-H6-ADJACENT-GAP-EIGHT-01`; generic adjacent-pair geometry supplies no positive
  height-uniform backward interval, as witnessed by the exact quadratic collision family.
- `theorem_names`: `summable_deBruijnNewman_regularizedZeroForceTerm`,
  `deBruijnNewmanH_second_deriv_div_two_deriv_eq_regularizedZeroForce`,
  `hasDerivAt_deBruijnNewmanH_along`, `deBruijnNewman_simpleZeroPath_velocity`,
  `exists_deBruijnNewman_localRealSimpleZeroPath`,
  `exists_deBruijnNewman_orderedLocalRealSimpleZeroPaths`,
  `deBruijnNewmanRegularizedZeroForce_sub_eq_two_div_add_pairRemainder`, and
  `hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq_pairRemainder`,
  `deBruijnNewmanZeroPairForceRemainder_re_nonpos`,
  `deBruijnNewman_adjacentSimpleZeroPath_realGapSq_lower_bound`, and
  `exists_h6GapAuditHeatPolynomial_collision_within`.
- `failure_or_obstacle`: the generic adjacent sign estimate succeeds but is sharp. It yields only
  terminal-gap-squared divided by eight of backward persistence, which degenerates with shrinking
  high-zero gaps. A theta-specific, height-aware estimate or a different collision invariant is
  still required.
- `route_selection_decision`: remain in the fixed H6-E campaign and attack the theta-specific
  pair-remainder estimate after loop-2 public implementation CI.
