# H6 de Bruijn-Newman Entire Heat Equation Campaign

Campaign: `CAMPAIGN-20260717-H6-HEAT-EQUATION-01`

Mode: `LITERATURE`

Status: `LOCAL_IMPLEMENTATION_COMPLETE_PUBLIC_CI_PENDING`

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
- Preregistration commit `ee6d08a108255d336e3b1c46166a753da48c06df` passed public Lean Action CI
  run `29501372019`, build job `87630848802`, in `1m58s`.
- `result`: `PUBLIC_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Implementation loop

- Exposed the source term identity and the existing elementary double-exponential integrability
  and complex sine/cosine norm estimates without changing their statements.
- Proved `integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi`: for every `c>=0` and real
  `d`, `(1+u^2)*exp(c*u^2+d*u)*|Phi(u)|` is integrable on `(0,infinity)`. The proof separates a
  summable index majorant from the source double-exponential `u` decay.
- Defined the exact `u^2` source moment and proved integrability of the original, first spatial,
  and second spatial moment integrands for every real time and complex spatial parameter.
- Applied `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with explicit unit-ball majorants in
  both parameter spaces. This proves the real-time derivative, complex first derivative, entire
  spatial family, and complex second derivative without restricting `t` or `z`.
- Compiled the preregistered sign and quantifiers as
  `deBruijnNewmanH_backward_heat_equation (t : R) (z : C)`.
- The campaign proves no zero-location statement and does not define a Newman threshold.

## Mechanical audit

- preregistration diff check: passed before public preregistration
- public preregistration commit and CI: passed as commit
  `ee6d08a108255d336e3b1c46166a753da48c06df`, run `29501372019`, job `87630848802`
- exact module compilation: passed without diagnostics
- `Targets.lean`: passed; `H6.debruijn-newman.heat-evolution` is proven
- `TargetChecks.lean` exact witness: passed for the majorant, time derivative, entire family,
  second spatial derivative, and final PDE
- `AxiomsAudit.lean` and printed axioms: passed; all five new entries use only `propext`,
  `Classical.choice`, and `Quot.sound`
- forbidden token/declaration/resource scan: empty; an initial broad declaration scan matched the
  English word `constant,` in an old comment, and the declaration-shaped rescan was empty
- witness audit: exact full-quantifier endpoint compiled; no weakened wrapper is registered
- definition/source alignment: inherited exact source definitions; derivative alignment fixed here
- full `lake build`: passed locally, 8,684 jobs
- `git diff --check`: passed before this documentation backfill and will be rerun before publication

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `assumption_frontier_after`: the exact H6-B family is now an all-real-time entire heat evolution;
  later H6 work may use its compiled derivatives and PDE
- `hard_gap_after`: H6-H2 all-real-zero/threshold theory, H6-E/G8 (`Lambda <= 0`), W2/G7,
  M2/G3, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `OBS_node`: none; the preregistered arbitrary-weight domination obstacle is closed
- `theorem_names`: `integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi`,
  `hasDerivAt_deBruijnNewmanH_time`, `hasDerivAt_deBruijnNewmanH_spatial`,
  `differentiable_deBruijnNewmanH`, `deriv_deriv_deBruijnNewmanH`,
  `deBruijnNewmanH_backward_heat_equation`
- `failure_or_obstacle`: no parameter-integral dependency gap; the next H6 obstruction is global
  zero dynamics and threshold closedness, not differentiation of the source family
- `route_selection_decision`: H6-H1 complete; fresh value-ranked route selection required after
  public closure
- `preregistration_commit`: `ee6d08a108255d336e3b1c46166a753da48c06df`
- `preregistration_CI`: public Lean Action run `29501372019`, build job `87630848802`, passed in
  `1m58s`
- `implementation_commit`: pending
- `implementation_CI`: pending
- `commit_and_CI`: preregistration is public; implementation publication, independent CI, evidence
  backfill, and closure remain
