# H6 Positive-Cosh Third-Li Falsification

Campaign: `AUDIT-20260717-H6-POSITIVE-COSH-LI3-01`

Mode: `FALSIFICATION`

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited compacted summary; canonical governance, HANDOFF, Targets,
  route portfolio, hard-gap DAG, and H6 route card reread from the clean public worktree
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: the positive two-atom `cosh` transform and exact first-three Li
  sign pattern in `research/h6_positive_cosh_li3_falsification_prereg_20260717.md`.
- `relation_to_RH`: falsifies a generic all-order extrapolation from H6-Z; it does not concern the
  actual theta kernel and does not prove or falsify RH.
- `success_criterion`: exact entire/reflection/positive-coefficient/normalization clauses, exact
  standard Li differential values, first-two positivity and third negativity, followed by all
  mechanical and public CI gates.
- `falsification_criterion`: any registered clause is false for the fixed atoms and weights.
- `assumption_frontier_before`: H6-Z proves first-two positivity for the exact theta heat family
  using positive moments and weighted Cauchy--Schwarz; no all-index moment mechanism exists.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `known_obstacle`: all-index Li positivity at time zero is RH-equivalent; generic positive moment
  matrices need not control higher logarithmic cumulants.
- `nearest_primary_source`: Bombieri--Lagarias 1999, D. H. J. Polymath 2019, Sekatskii 2013.
- `nearest_project_attempt`: the publicly closed H6-Z first-two moment campaign and
  `OBS-H6-REVERSE-HEAT-LI-01`.
- `new_attack_angle`: retain an exact positive `cosh` representation, rather than only the heat
  PDE, and test the first unproved Li order with two rationally normalizable atoms.

## Selection and preregistration loop

- Compared direct H6-E continuation, H6-Q, a source-specific third Li inequality, W2/G7, and
  M2/G3 against the current obstruction map.
- Derived the exact third Li polynomial in the normalized moments and screened finite positive
  measures for boundary cases; numerical screening selected the model but is not a premise.
- Fixed `u=log 2`, `u=10*log 2`, normalized masses `1/8,7/8`, and the standard third Li
  differential expression before any Lean proof-source edit.
- Primary-source search located general Li criteria and the exact theta heat family, with no
  theorem asserting higher Li positivity from an arbitrary positive even transform.
- `result`: `LOCAL_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Pending gates

- immutable evidence backfill and its public CI

## Public preregistration gate

- Preregistration commit `316ece356aaf5a11f2ddd18ff91da7a9f2ac73e3` passed public Lean Action CI
  run `29542262029`, build job `87766756340`, from `2026-07-16T23:28:51Z` to `23:30:47Z`
  (`1m56s`) before proof-source edits.
- `result`: `PUBLIC_PREREGISTRATION_COMPLETE`

## Lean falsification loop

- Added the 501-line diagnostic-free module `H6PositiveCoshLiAudit.lean` with the exact registered
  atoms, normalized masses, and standard first-three Li differential expressions.
- Proved the normalized atom and the two-atom sum are complex differentiable everywhere and that
  the sum is reflection symmetric. Both unnormalized atom coefficients are strictly positive and
  the transform is exactly one at `s=1`.
- Derived the first three spatial derivatives and then the first two derivatives of `logDeriv`.
  The second logarithmic derivative is justified on an actual nonvanishing neighborhood of
  `s=1`; no quotient rule is asserted at zeros.
- Lean evaluates `sinh(log 2)`, `cosh(log 2)`, and the corresponding values at `10*log 2` exactly,
  obtaining the registered rational `beta`, `gamma`, and `delta` moment formulas.
- The first two Li signs are exact consequences of positivity and the two-atom variance. For the
  third sign, Lean uses `Real.log_two_gt_d9`, proves the exact quadratic bracket decreases beyond
  the certified lower endpoint, and derives a strict negative value. No decimal evaluation is a
  premise.
- The aggregate theorem carries entire-ness, reflection, coefficient positivity, normalization,
  all three exact formulas, and the complete real sign pattern.
- `result`: `BRANCH_FALSIFIED`
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 1

## Mechanical audit

- standalone module compilation: diagnostic-free
- exact `Targets.lean`: passed
- exact aggregate `TargetChecks.lean` witness: passed
- five selected transitive axiom prints: each exactly
  `[propext, Classical.choice, Quot.sound]`
- forbidden `sorry`/`admit`/`native_decide` scan: empty
- syntax-narrow `axiom`/`constant`/`opaque`/`unsafe` declaration scan: empty
- resource-relaxation scan: empty
- `git diff --check`: passed
- full `lake build`: passed, 8,694 jobs
- definition alignment: `Li1`, `Li2`, and `Li3` use the standard derivative convention fixed in
  the preregistration; the transform is not identified with the theta heat family

## Local result

- `result_class`: `BRANCH_FALSIFIED`
- `OBS_node`: `OBS-H6-POSITIVE-COSH-LI3-01`, locally compiled
- `theorem_names`: `h6PositiveCoshAudit_entire`, `h6PositiveCoshAudit_reflection`,
  `h6PositiveCoshAudit_coefficients_pos`, `h6PositiveCoshAuditLiOne_eq`,
  `h6PositiveCoshAuditLiTwo_eq`, `h6PositiveCoshAuditLiThree_eq`,
  `h6PositiveCoshAuditLiThree_re_neg`,
  `h6PositiveCoshAudit_falsifies_allOrder_positiveKernelLi`
- `assumption_frontier_after`: positivity of an arbitrary finite even `cosh` transform and its
  generic moment/Hankel inequalities do not force third Li nonnegativity
- `hard_gap_after`: quantitative information specific to `deBruijnNewmanPhi`, H6-E/G8, W2/G7,
  M2/G3, and RH remain open
- `failure_or_obstacle`: the H6-Z first-two Cauchy--Schwarz proof cannot be promoted to an
  all-index argument using positive-kernel or ordinary Hankel positivity alone
- `route_selection_decision`: after public closure, require a genuinely theta-specific
  inequality/cumulant control or return to independent value-ranked route selection
- `implementation_publication`: commit `5fdfc5c7437349735c57552a75838f16b4d63f5e` passed
  public Lean Action CI run `29543145545`, build job `87769424525`, from
  `2026-07-16T23:51:36Z` to `23:53:31Z` (`1m55s`)

## Public implementation gate

- Immutable implementation commit `5fdfc5c7437349735c57552a75838f16b4d63f5e` passed public
  Lean Action CI run `29543145545`, build job `87769424525`, from
  `2026-07-16T23:51:36Z` to `23:53:31Z` (`1m55s`).
- `result`: `PUBLIC_IMPLEMENTATION_VERIFIED`
- Only evidence backfill and its public CI remain before campaign closure.
