# H6 Heat-Li Time Monotonicity

Campaign: `PROOF-ATTEMPT-20260717-H6-HEAT-LI-TIME-MONOTONICITY-01`

Mode: `PROOF-ATTEMPT`, with mandatory `FALSIFICATION` gate

Status: `IMPLEMENTATION_PUBLIC_CI_SUCCESS`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: fresh route selection after the publicly closed global-PF4 search; canonical
  governance, hard-gap DAG, H1/H2/H6 route cards, route portfolio, Targets, and relevant W2/M2
  obstruction records were reread
- `global_goal`: active

## Selection record

- `exact_target`: all-index actual-theta heat-Li coefficients tend to zero at negative infinite
  time and are monotone nondecreasing through time zero; derive RH
- `strength`: implies RH and may be strictly stronger
- `material_difference`: uses negative-time theta concentration and coefficient evolution, not
  later-time backward transfer, generic gap geometry, generic positive-kernel moments, or physical
  kernel total positivity
- `first_consistency_evidence`: the first coefficient derivative is governed by the already
  compiled ordered covariance `A*D-B*C>=0`
- `nearest_literature`: Loffler 2015 studies a related heat deformation; Sondow--Dumitrescu 2010
  studies a different spatial xi monotonicity; no exact all-index heat-Li time statement located
- `hard_gap_before`: H6-E/G8 and RH open

## Frozen rule

The conjecture is not a premise. Numerical work can only select a target. Campaign success is the
full compiled conjunction plus RH; campaign falsification is an exact Lean theorem about the
actual theta family. Fixed-index positivity, finite differences without full-kernel control, or a
generic finite-mixture model does not close the campaign.

## Public preregistration evidence

- Commit: `645b4570dfe25bd5bcdcda63168d64a34ba90e24`.
- Lean Action CI run: `29569013156`.
- Build job: `87848139812`, success in `1m28s`.

## Numerical gate implementation

- Tool: `research/tools/search_heat_li_time_monotonicity.py`.
- The actual-theta derivatives are generated from full theta-series quadrature moments.
- Li values use the generating substitution `s=1/(1-z)`.
- Time derivatives use the quotient series `(partial_t F)/F`; no finite time difference selects a
  sign.
- The positive two-atom cosh audit family is evaluated as a generic-control branch.
- Every output remains target-selection evidence only.

## Numerical gate result

- The preregistered 80-digit scan covered project indices `0..31` at 50 times in `[-16,0]` and
  found no negative actual-theta time derivative.
- Independent 120- and 180-digit scans increased both quadrature density and theta-series
  precision. The actual-theta minimum converged to project index `0`, time `-16`, derivative
  `0.000278054186180640755574984...`; no sampled sign changed.
- A 240-digit extension through project index `63` again found no negative derivative. At the
  higher indices the per-index minimum moved to time zero, so the observed sign is not explained
  by monotonic growth of the derivative in time.
- A separate 500-digit time-zero extension through project index `127` found no negative
  derivative. This extension exceeds the preregistered gate but remains numerical evidence only.
- The positive two-atom cosh control had robust negative derivatives, including project index `1`
  at time zero. Hence positivity, reflection symmetry, and finite positive hyperbolic moments do
  not provide the required sign mechanism.
- The first-index generating-series output was checked against `F'(1)/F(1)` and its direct quotient
  time derivative. At 80 digits, the maximum absolute residuals were below `3.3e-83` and
  `1.6e-84`, respectively. This is the numerical counterpart of the compiled `A,B,C,D` moment
  formula and covariance sign, not a proof premise.

## Lean results

New module: `LeanLab/Riemann/DeBruijnNewmanHeatLiMonotonicity.lean`.

- `DeBruijnNewmanHeatLiAtBotZero` and `DeBruijnNewmanHeatLiMonotoneToZero` freeze the exact
  all-index assumptions without asserting them.
- `forall_heatLiCoefficient_zero_re_nonneg_of_atBot_zero_and_monotone` proves that the two
  assumptions force every time-zero heat-Li coefficient to have nonnegative real part.
- `riemannHypothesis_of_heatLi_atBot_zero_and_monotone_assumptions` composes that result with the
  exact compiled all-index criterion and proves RH from precisely the registered assumptions.
- `deBruijnNewmanHeatXi_timeRatio_eq_logDeriv_evolution` proves, at every nonzero heat-Xi point,
  the function-level evolution
  `(partial_t F)/F = (1/4) * (deriv(logDeriv F) + (logDeriv F)^2)`.
- No theorem asserts the unproved limit or monotonicity conjecture.

## Proof mechanism A: generating-series evolution

The compiled function identity reduces coefficient evolution to the transformed coefficients of
`G''+(G')^2`, where `G` is the local logarithmic generating function after
`s=1/(1-z)`. The square term introduces signed cross-index convolutions. The existing first-index
covariance controls only its first specialization; the compiled positive-cosh obstruction and the
new numerical heat control rule out a proof using generic positive hyperbolic moments. The missing
dependency is a single actual-theta all-index coefficient representation with nonnegative
integrand or an equivalent theta-specific convolution inequality.

## Proof mechanism B: moving-zero evolution

The exact paired-zero formula is compiled separately at every time, but its divisor-index type
depends on that time. Existing dynamics provide local paths only for simple zeros, and their
velocity contains a regularized force whose pair-removed remainder has no global sign. There is no
compiled multiplicity-preserving global transport of the time-dependent divisor, no theorem
permitting differentiation of its `tsum`, and no collision-compatible domination uniform in the
Li index. Thus zero-side differentiation reaches the same missing theta-specific all-index sign
control through a materially different mechanism.

## Local result

- `result`: `NO_PROGRESS`
- `global_goal`: active
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `obstruction_map_delta`: 1 search/proof boundary
- `rh_status`: open

The numerical conjecture is neither proved nor falsified. Re-entry requires a concrete
actual-theta all-index integral/convolution identity or a global collision-compatible divisor
transport theorem, not additional finite-index sampling alone.

## Mechanical audit

- standalone `DeBruijnNewmanHeatLiMonotonicity.lean`: diagnostic-free
- exact `Targets.lean` and `TargetChecks.lean`: pass
- selected transitive axiom prints: exactly `propext`, `Classical.choice`, and `Quot.sound`
- forbidden proof/declaration/resource-relaxation scans: empty
- `git diff --check`: pass
- full build: 8,700 jobs, pass

## Public implementation evidence

- implementation commit: `fc2a32e8316f59370471597df9a8a26c02480bdd`
- Lean Action CI run: `29570628316`
- build job: `87853282509`, success in `2m2s`

Evidence backfill commit and its public CI are pending.
