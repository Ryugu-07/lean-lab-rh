# H6 Heat-Li All-Index Criterion Attempt

Campaign: `LITERATURE-20260717-H6-HEAT-LI-ALL-INDEX-01`

Mode: `LITERATURE`

Status: `IMPLEMENTATION_PUBLIC_CI_PASSED_EVIDENCE_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited continuation; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, H6 route card, Li criterion modules, and current public worktree were
  reread before selection
- `global_goal`: active

## Selection record

- `exact_target`: prove the full nonnegative-time heat-family Li iff and pointwise time-zero
  equality with the project Li candidates.
- `material_difference`: the previous campaign proved one finite coefficient by theta covariance;
  this campaign moves to the all-index zero criterion and does not attempt coefficient four.
- `nearest_attempt`: the public xi-specific Bombieri-Lagarias reverse criterion and H6-X route
  card; no previous heat-family all-index implementation exists in the repository.
- `assumption_frontier_before`: all H6 source definitions, order-one H theorem, zero-strip
  contraction, all-real half-time theorem, first-three heat Li values, and the xi-specific all-index
  criterion are compiled; the generic/heat all-index bridge is absent.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `finite_model_screen`: a reflected critical-line pair gives nonnegative paired coefficients; a
  reflected off-line pair at `rho=1/4+i` produces a negative coefficient in the first 100 indices.
  This screen is not a proof premise.

## Gate status

- preregistration commit, push, and public Lean Action CI: passed
- complete Lean endpoint without a hidden negative-time or strip hypothesis: passed locally
- exact registry, axiom, definition-alignment, forbidden-scan, and full-build gates: passed locally
- implementation public CI: passed
- evidence backfill commit and public CI: pending
- final public closure log update: pending

## Public implementation evidence

- implementation commit `16437075ed7ceb56becff79c77308d3e33bd1c65`
- public Lean Action CI run `29548736988`, build job `87786563205`, passed in `1m59s`

## Current result

- `result`: `KNOWN_CRITERION_HEAT_FAMILY_SPECIALIZATION_PUBLIC_IMPLEMENTATION`
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `proof_source_edits`: `LeanLab/Riemann/DeBruijnNewmanLiCriterion.lean`

## Loop record: complete all-index implementation

1. The preregistration commit
   `e8b611c4e3ab82df78925265c95e4c89ef6d1e29` passed public Lean Action CI run
   `29546924877`, job `87781127750`, before proof-source edits.
2. The derivative definition and time-zero pointwise equality compiled first, followed by the
   exact coordinate iff between real `H_t` zeros and critical-line heat-Xi zeros.
3. Affine input scaling, translation, and output scaling were proved to preserve entire order at
   most one. This yields heat-Xi divisor reciprocal-square summability for every real `t`, removing
   the anticipated need for a negative-time zero strip.
4. The Bombieri-Lagarias large-index argument was extracted to an abstract reflected divisor. Its
   reverse direction uses a finite orbit-radius superlevel, simultaneous phase recurrence, and a
   reciprocal-square tail bound; an off-line zero forces a negative coefficient.
5. The analytic bridge reconstructs the genus-one Hadamard factorization, locally uniform
   termwise differentiation at `s=1`, the compensated zero formula, reflection averaging, and
   functional-equation cancellation of the degree-at-most-one polynomial contribution.
6. Lean proves, for every real `t`,
   `deBruijnNewmanAllZerosReal t <-> forall n, 0 <= Re(heatLi(t,n))`, and for every `n` the exact
   equality `heatLi(0,n)=liCoefficientCandidate n`. The preregistered `t>=0` aggregate and the
   time-zero RH compatibility theorem also compile.

## Mechanical audit

- standalone new-module compile: diagnostic-free
- exact TargetChecks: diagnostic-free
- selected axiom prints: only `propext`, `Classical.choice`, and `Quot.sound`
- forbidden placeholder/declaration/resource scans: empty
- `git diff --check`: pass
- full build: `8696` jobs, success
- implementation public CI: run `29548736988`, build job `87786563205`, passed in `1m59s`
- immutable evidence closure: pending

## Assumption frontier

The campaign closes the criterion specialization only. At `t=0`, proving all coefficient real
parts nonnegative remains equivalent to RH. No unconditional sign beyond the already compiled
finite prefix is added, so RH, H6-E/G8, W2/G7, and M2/G3 remain open.
