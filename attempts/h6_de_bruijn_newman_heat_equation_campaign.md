# H6 de Bruijn-Newman Entire Heat Equation Campaign

Campaign: `CAMPAIGN-20260717-H6-HEAT-EQUATION-01`

Mode: `LITERATURE`

Status: `LOCAL_PREREGISTERED_PUBLIC_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: recovered from the completed H6-B campaign summary, then canonical files
  reread
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: for every real `t`, the source-defined `H_t` is entire in `z`,
  is differentiable in `t`, and satisfies `partial_t H_t = -partial_z^2 H_t` pointwise on `C`.
- `proposed_lean_statements`: `differentiable_deBruijnNewmanH`,
  `hasDerivAt_deBruijnNewmanH_time`, `deriv_deriv_deBruijnNewmanH`, and
  `deBruijnNewmanH_backward_heat_equation` in
  `research/h6_de_bruijn_newman_heat_equation_prereg_20260717.md`.
- `relation_to_RH`: H6 analytic infrastructure; it changes no unconditional RH frontier.
- `success_criterion`: all four clauses with full quantifiers, exact witnesses, standard-only
  axiom audit, full build, and public CI.
- `falsification_criterion`: a precise arbitrary-time domination or complex parameter-integral
  dependency gap; bounded-time, real-axis, continuity-only, or integrand-only results fail the
  endpoint.
- `assumption_frontier_before`: public compiled H6-B source normalization and H0-xi identity.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `known_obstacle`: neighborhood-uniform integrability of the `u^2`-weighted source kernel with
  arbitrary fixed quadratic and linear exponential weights.
- `nearest_primary_source`: D. H. J. Polymath, arXiv `1904.12438`; Rodgers-Tao, arXiv `1801.05914`.
- `nearest_project_attempt`: `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01`, publicly closed.
- `new_attack_angle`: reuse its explicit double-exponential series and mathlib's dominated
  parametric-integral theorem to prove the source PDE for the exact compiled family.

## Preregistration loop

- Reread canonical governance, HANDOFF, Targets, the hard-gap DAG, H1/H2/H6 route cards, the Batch
  A audit, route atlas, and recent attempts after compaction recovery.
- Checked the primary H6 sources: both quantify the displayed integral over every real `t`; the
  Polymath source identifies it as an entire heat-flow evolution.
- Compared H6-H with H6-X, direct H6-E/H6-Q, H1-B, H2-B, H10, W2/G7, and M2/G3. H6-H is the only
  candidate that both unlocks the next H6 statements and has a fixed current-library failure
  boundary.
- Local inventory found `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and the completed H6-B
  double-exponential kernel estimates. The missing reusable theorem is the arbitrary quadratic-
  weight majorant needed to combine them.
- No Lean proof source was edited during preregistration.
- `result`: `LOCAL_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Mechanical audit

- preregistration diff check: pending
- public preregistration commit and CI: pending
- exact module compilation: pending implementation
- `Targets.lean`: pending implementation
- `TargetChecks.lean` exact witness: pending implementation
- `AxiomsAudit.lean` and printed axioms: pending implementation
- forbidden token/declaration/resource scan: pending implementation
- witness audit: pending implementation
- definition/source alignment: inherited exact source definitions; derivative alignment fixed here
- full `lake build`: pending implementation

## Result

- `result_class`: pending
- `assumption_frontier_after`: pending
- `hard_gap_after`: pending
- `hard_gap_delta`: pending
- `OBS_node`: none yet
- `theorem_names`: none yet
- `failure_or_obstacle`: pending
- `route_selection_decision`: H6-H selected
- `commit_and_CI`: pending
