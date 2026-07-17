# H6 Third-Li Covariance Attempt

Campaign: `DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01`

Mode: `DISCOVERY`

Status: `PREREGISTERED_LOCAL`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited compacted summary; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, H6 source modules, and current route records reread from the clean
  public worktree
- `global_goal`: active

## Selection record

- `exact_target`: prove the exact theta-source covariance `B*C<=A*D`, the standard third heat-Li
  formula, its time-zero equality with `liCoefficientCandidate 2`, and strict positive real sign.
- `relation_to_RH`: one finite necessary Li condition; strictly below the all-index RH-equivalent
  criterion.
- `material_difference`: the failed positive-cosh branch used generic positivity only. This attack
  combines same-order covariance with the source-specific compiled time-zero bound `lambda1<1`.
- `nearest_attempt`: H6 first-two moment campaign and `OBS-H6-POSITIVE-COSH-LI3-01`.
- `nearest_sources`: Li 1997, Bombieri-Lagarias 1999, Polymath 2019, Coffey 2004, Maslanka 2004.
- `numerical_screen`: candidate selection only; approximate time-zero signs are positive through
  order three, and no sampled time in `[-100,100]` refuted the third sign.
- `assumption_frontier_before`: no theorem about the fourth theta moment, ordered covariance,
  third heat-Li formula, or `liCoefficientCandidate 2` sign is currently admitted.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.

## Pending gates

- preregistration diff check, commit, push, and public Lean Action CI
- exact Lean implementation without weakened endpoint
- Targets, TargetChecks, standard-only axiom audit, forbidden scans, full build
- implementation public CI and immutable evidence closure

## Current result

- `result`: `LOCAL_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0
- `proof_source_edits`: none
