# H6 Forward Real-Zero Preservation Campaign

Campaign: `CAMPAIGN-20260717-H6-FORWARD-PRESERVATION-01`

Mode: `LITERATURE`

Status: `LOCAL_IMPLEMENTATION_VERIFIED_PUBLIC_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: resumed after public closure of H6 threshold closedness; canonical
  governance, HANDOFF, Targets, TargetChecks, DAG, H1/H2/H6/H10 route cards, and the previous
  campaign log were reread from the repository
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`:
  `t <= tau -> deBruijnNewmanAllZerosReal t -> deBruijnNewmanAllZerosReal tau`.
- `proposed_Lean_statement`: `deBruijnNewmanAllZerosReal_mono` with arbitrary real `t,tau` and no
  additional hypotheses.
- `relation_to_RH`: H6-H2 threshold infrastructure. At `t=0` the predicate is RH-equivalent, but
  this implication does not establish its premise.
- `success_criterion`: the exact two-time theorem plus every witness, trust, build, and public CI
  gate in `research/h6_forward_preservation_prereg_20260717.md`.
- `falsification_criterion`: a source-order, shifted-factorization, heat-multiplier, sign, scaling,
  domination, or limit-persistence clause in the fixed architecture is false.
- `assumption_frontier_before`: exact source integral, entire backward heat evolution, all-real
  predicate, time-zero RH equivalence, nonvanishing, joint continuity, and threshold closedness are
  public.
- `hard_gap_before`: forward preservation, threshold nonemptiness/upper-ray structure, H6-E/G8,
  W2/G7, M2/G3, and RH are open.
- `known_obstacle`: mathlib has no Laguerre-Polya class, real-rootedness preserver, or Hurwitz
  theorem. The vendored generic Hadamard factorization can be used only after a new source
  order-one estimate, and it has no ready real-zero shifted-modulus corollary.
- `nearest_primary_source`: de Bruijn 1950; Rodgers-Tao arXiv `1801.05914`; Branden-Chasse arXiv
  `1402.2795`.
- `nearest_project_attempt`: H6 threshold closedness is publicly closed and supplies nonvanishing,
  joint continuity, and Jensen zero persistence, but no forward implication.
- `new_attack_angle`: reconstruct the universal-factor proof through the already vendored
  genus-one Hadamard API and source integral, then use iterated vertical-shift averages instead of
  introducing an unproved Laguerre-Polya abstraction.

## Route-selection loop

- Re-read the canonical V4.1 governance, current HANDOFF, Targets, exact TargetChecks, DAG, H6
  route card, and the previous H6 attempt log after compaction.
- Compared H1/H2 finite count wrappers, H10 continuation, direct M2/W2 re-entry, H6-Q, and the next
  H6-H2 dependency.
- Rejected H1-B/H2-B as hard-gap-neutral bookkeeping for this selection and H10 continuation as
  lacking a number-field-relevant consumer.
- Found no materially new unconditional M2/G3 or W2/G7 mechanism beyond recorded obstruction
  nodes.
- Confirmed from Rodgers-Tao that the exact source family is forward preserved, and from
  Branden-Chasse that de Bruijn's shifted Jensen theorem and `exp(-lambda*D^2)` strip contraction
  are the relevant source mechanism.
- Audited mathlib and the project for Laguerre-Polya, real-rootedness, hyperbolic polynomials,
  Hurwitz convergence, strip contraction, and heat-root preservation; none is packaged.
- Found reusable generic finite-order Hadamard factorization in the vendored
  `PrimeNumberTheoremAnd` tree and reusable Jensen persistence in the just-closed threshold module.
- Fixed the exact endpoint and seven-stage proof architecture before any Lean proof-source edit.
- `result`: campaign selected; public preregistration gate pending
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Current decision

- `public_preregistration`: commit `6e10d6eb74f038575e1d6ab4dcde92eb4e58b2ce`, Lean Action
  CI run `29520281656`, build job `87695371156`, passed in `1m51s`
- `route_selection_decision`: begin the fixed implementation and identify the first exact missing
  dependency without weakening the endpoint
- `campaign_status`: exact implementation verified locally; public implementation CI pending;
  persistent RH Goal remains active

## Implementation checkpoint: order one and vertical average

- `local_compile`: `rtk lake env lean LeanLab/Riemann/DeBruijnNewmanForward.lean` passes with no
  diagnostics under the default heartbeat limit.
- `source_decay`: exposed the existing double-exponential source majorant in
  `DeBruijnNewmanHeat.lean` and proved an order-one Hadamard growth bound for every real time.
- `factorization`: proved genus-one factorization and eliminated its linear exponential term using
  evenness and `deriv (deBruijnNewmanH t) 0 = 0`.
- `strict_product_comparison`: for `a>0` and `Im z>0`, proved the lower-shift canonical product has
  strictly smaller norm than the upper-shift product. The infinite-product proof fixes one strict
  factor and passes a uniform ratio `c<1` through finite products to the product limit; it also
  handles a vanishing lower factor.
- `compiled_intermediate`: `deBruijnNewman_verticalAverage_allZerosReal` proves that
  `(H_t(z+i*a)+H_t(z-i*a))/2` has only real zeros whenever `H_t` does and `a>=0`.
- `axiom_status`: not yet registered or audited; this is a local intermediate, not an endpoint
  progress claim.
- `next_dependency`: identify the vertical average with the source integral carrying multiplier
  `cosh(a*u)`, iterate it, and prove convergence to the exact forward heat multiplier.
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1

## Endpoint completion checkpoint

- `exact_endpoint`: `deBruijnNewmanAllZerosReal_mono` compiles with arbitrary real `t <= tau`,
  the existing all-complex-zero predicate, and no simplicity, spacing, bounded-time,
  nonnegative-time, or finite-degree hypothesis.
- `heat_limit`: finite iterated vertical averages carry multiplier
  `cosh(sqrt(2*(tau-t)/n)*u)^n`; a scalar-error majorant proves convergence to
  `exp((tau-t)*u^2)` and hence to the exact `H_tau` integral.
- `zero_persistence`: an assumed nonreal zero of the limit is isolated in a closed nonreal ball;
  Jensen persistence transfers a zero into sufficiently late all-real-zero approximants, giving
  the contradiction.
- `local_compile`: the new module, Targets, exact TargetCheck, and AxiomsAudit all pass under
  default resource limits; the full 8,689-job build succeeds.
- `axiom_status`: the four registered witnesses each print exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- `forbidden_scans`: proof placeholders, custom axioms/opaque/unsafe declarations, and resource
  relaxation scans are empty; `git diff --check` passes.
- `classification`: `KNOWN_THEOREM_FORMALIZED`.
- `hard_gap_delta`: 0.
- `route_infrastructure_delta`: 1.
- `remaining_frontier`: threshold nonemptiness and upper-time existence, H6-E/G8, W2/G7,
  M2/G3, and RH remain open.
- `next_gate`: commit and push the implementation, require public Lean Action CI, then backfill
  immutable run evidence before public campaign closure.
