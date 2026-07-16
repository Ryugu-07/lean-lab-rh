# H6 Reverse-Heat Li Transfer Falsification

Campaign: `AUDIT-20260717-H6-REVERSE-HEAT-LI-01`

Mode: `FALSIFICATION`

Status: `PUBLIC_IMPLEMENTATION_COMPLETE_EVIDENCE_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: continued after the publicly closed H10-B campaign; canonical files reread
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: the seven-clause polynomial heat-Xi countermodel in
  `research/h6_reverse_heat_li_falsification_prereg_20260717.md`.
- `relation_to_RH`: falsifies a generic backward-transfer mechanism adjacent to H6-X/H6-E; it does
  not address the actual theta-kernel family or falsify RH.
- `success_criterion`: exact polynomial PDE, reflection, entire-ness, real-time base-point
  nonvanishing, all critical-line zeros at time one, explicit off-line zero at time zero, and exact
  second Li values, followed by all mechanical and public CI gates.
- `falsification_criterion`: any registered clause is false for the fixed polynomial.
- `assumption_frontier_before`: the project has the exact H6 source heat equation and the exact Li
  criterion at time zero, but no valid reverse-time positivity transfer.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `known_obstacle`: backward heat flow does not preserve real-rootedness; the audit strengthens the
  warning by retaining reflection symmetry and nonvanishing at the Li base point.
- `nearest_primary_source`: Rodgers-Tao 2018, D. H. J. Polymath 2019, and Li 1997.
- `nearest_project_attempt`: H6-B and H6-H1 are publicly closed; H6-X remains a fixed-time
  criterion candidate and has no backward-time theorem.
- `new_attack_angle`: a rational degree-two heat family gives an exact, kernel-checkable Li-sign
  reversal without a base-point zero on the nonnegative real time interval.

## Selection and preregistration loop

- Reread current governance, HANDOFF, Targets, hard-gap DAG, route atlas, H1/H2/H6 cards, H10
  closure, and the exact M2 and W2 obstruction attempts.
- Compared direct W2/G7, direct M2/G3, H6-Q, generic H6 backward transfer, H1/H2 bridges, and new
  equivalence formalizations.
- Targeted primary-source search confirmed the canonical one-way heat-flow setting and found no
  source claim matching the generic backward Li transfer.
- Fixed the polynomial and both rational Li values before any Lean proof source edit.
- Preregistration commit `215ebcf661a421350d30920ec5aee43518d89559` passed public Lean Action CI run
  `29508598381`, build job `87655833650`, in `1m30s`.
- `result`: `PUBLIC_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Lean falsification loop

- Added `H6ReverseHeatLiAudit.lean` with the exact registered polynomial and the generalized
  second Li expression `2*logDeriv(f)(1)+(logDeriv(f))'(1)`.
- Proved complex differentiability in both variables and the exact heat equation
  `partial_t F=(1/4)*partial_s^2 F`; proved reflection by polynomial identity.
- Proved `F_t(1)!=0` for every real `t>=0`, retaining the base-point hypothesis throughout the
  time interval rather than exploiting a logarithmic-derivative pole.
- For an arbitrary complex zero of `F_1`, separated real and imaginary parts. The imaginary
  equation gives `(Re(s)-1/2)*Im(s)=0`; the real equation rules out `Im(s)=0`, forcing
  `Re(s)=1/2`. This is an all-zero theorem, not a finite root listing.
- Lean verifies `F_0(3/4)=0` and that `3/4` is off the critical line.
- Derived the logarithmic-derivative quotient and its derivative at `1`, obtaining the exact
  second Li values `-64/9` at time zero and `448/121` at time one.
- Registered one aggregate theorem containing every clause in Targets and TargetChecks.
- `result`: `BRANCH_FALSIFIED`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 1

## Mechanical audit

- preregistration diff check: passed before publication
- public preregistration commit and CI: passed at commit
  `215ebcf661a421350d30920ec5aee43518d89559`, run `29508598381`, job `87655833650`
- exact module compilation: diagnostic-free
- `Targets.lean`: exact obstruction target compiles as proven
- `TargetChecks.lean`: exact aggregate witness compiles
- `AxiomsAudit.lean`: all-zero theorem, both exact Li values, and aggregate theorem each use only
  `propext`, `Classical.choice`, and `Quot.sound`
- forbidden token/declaration/resource scan: empty
- witness audit: all time-one zeros are quantified; the time-zero off-line witness is exact
- definition alignment: the second Li expression matches the project's compiled
  `liCoefficientCandidate_one_eq_two_logDeriv_add_deriv_logDeriv` convention
- full `lake build`: passed locally, 8,686 jobs
- `git diff --check`: passed before implementation publication
- implementation public CI: passed at commit
  `819f3de472c43220895772788911a25e114cc7bd`, run `29509859982`, job `87660158241`, in `2m38s`
- immutable evidence backfill and public CI: pending

## Result

- `result_class`: `BRANCH_FALSIFIED`
- `assumption_frontier_after`: generic complex heat PDE, reflection, entire-ness, nonvanishing at
  the Li base point for all nonnegative real times, and later critical-line zeros do not imply
  earlier Li positivity
- `hard_gap_after`: H6-E/G8, W2/G7, M2/G3, and RH remain open
- `hard_gap_delta`: 0
- `OBS_node`: `OBS-H6-REVERSE-HEAT-LI-01`, locally compiled
- `theorem_names`: `h6AuditHeatXiQuadratic_heatEquation`,
  `h6AuditHeatXiQuadratic_one_allZerosOnCriticalLine`,
  `h6AuditHeatXiQuadratic_zero_offLine_witness`, `h6AuditSecondLiValue_zero`,
  `h6AuditSecondLiValue_one`, `h6AuditHeatXiQuadratic_falsifies_reverseLiTransfer`
- `failure_or_obstacle`: a successful reverse-time proof for the actual H6 family must use
  theta-kernel-specific estimates, infinite zero dynamics, or another premise absent from this
  countermodel; structural heat and Li data alone are insufficient
- `route_selection_decision`: publish and close the obstruction, then return to fresh value-ranked
  route selection; do not generalize the polynomial library
- `preregistration_commit_and_CI`: commit `215ebcf661a421350d30920ec5aee43518d89559`,
  run `29508598381`, job `87655833650`, passed in `1m30s`
- `implementation_commit_and_CI`: commit `819f3de472c43220895772788911a25e114cc7bd`,
  run `29509859982`, job `87660158241`, passed in `2m38s`
- `evidence_commit_and_CI`: pending
