# H6 Reverse-Heat Li Transfer Falsification

Campaign: `AUDIT-20260717-H6-REVERSE-HEAT-LI-01`

Mode: `FALSIFICATION`

Status: `LOCAL_PREREGISTERED_PUBLIC_CI_PENDING`

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
- `result`: `LOCAL_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Mechanical audit

- preregistration diff check: pending
- public preregistration commit and CI: pending
- exact module compilation: pending implementation
- `Targets.lean`: pending implementation
- `TargetChecks.lean`: pending implementation
- `AxiomsAudit.lean`: pending implementation
- forbidden token/declaration/resource scan: pending implementation
- full `lake build`: pending implementation

## Result

- `result_class`: pending
- `assumption_frontier_after`: pending
- `hard_gap_after`: pending
- `hard_gap_delta`: pending
- `OBS_node`: proposed `OBS-H6-REVERSE-HEAT-LI-01`
- `theorem_names`: pending
- `failure_or_obstacle`: pending
- `route_selection_decision`: H6 reverse-heat Li transfer falsification selected
- `commit_and_CI`: pending
