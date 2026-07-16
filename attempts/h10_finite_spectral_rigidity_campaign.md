# H10 Finite Power-Sum Spectral Rigidity Campaign

Campaign: `CAMPAIGN-20260717-H10-FINITE-SPECTRAL-RIGIDITY-01`

Mode: `LITERATURE`

Status: `PUBLIC_IMPLEMENTATION_COMPLETE_EVIDENCE_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: continued from the publicly closed H6-H1 campaign; canonical files reread
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: the two-clause finite aggregate power-sum radius/circle theorem
  in `research/h10_finite_spectral_rigidity_prereg_20260717.md`.
- `relation_to_RH`: exact final spectral mechanism in function-field RH; no number-field RH
  implication without a finite trace model or uniform infinite-tail control.
- `success_criterion`: both full-quantifier clauses, exact witnesses, standard-only axiom audit,
  full build, and public CI.
- `falsification_criterion`: a finite counterexample to the all-power aggregate bound, or a precise
  failure of simultaneous phase recurrence on the nonzero subtype.
- `assumption_frontier_before`: compiled finite simultaneous phase recurrence from the Li reverse
  campaign; no generic finite power-sum rigidity theorem.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.
- `known_obstacle`: converting simultaneous phase closeness into a uniform positive real-part
  lower bound while retaining zeros, duplicates, and arbitrary finite index types.
- `nearest_primary_source`: Bombieri, Bourbaki 430 (1973); Stepanov (1969).
- `nearest_project_attempt`: the Li reverse campaign uses phase alignment for a different infinite
  divisor/tail argument; it does not state the generic finite spectral theorem.
- `new_attack_angle`: isolate the exact function-field spectral step and reuse project phase
  recurrence to defeat arbitrary finite cancellation directly.

## Selection and preregistration loop

- Reread canonical governance, HANDOFF, Targets, hard-gap DAG, route atlas, H1/H2/H6 cards, and the
  latest H6 attempts after the rest turn.
- Compared the three open hard-gap routes, H6-H2/H6-X, H1-B/H2-B, and the required H10 census.
- Audited Stepanov's original special-case source, Bombieri's general Bourbaki presentation, and a
  modern statement-level reconstruction. The route card separates the point-count construction,
  lower-bound/Galois step, and final finite spectral rigidity.
- Local inventory found no equivalent theorem in project or pinned mathlib. Mathlib's curve-level
  Riemann-Roch/zeta/trace stack is not source-ready, while the project phase recurrence is directly
  sufficient for the selected spectral endpoint.
- No Lean proof source was edited during preregistration.
- Preregistration commit `af15b161049aedd65d46fd1f2af1f27e8dc69d44` passed public Lean Action CI
  run `29505635350`, build job `87645529929`, in `1m56s`.
- `result`: `PUBLIC_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Implementation loop

- Added `FinitePowerSumRigidity.lean` with the exact pre-registered finite power-sum definition
  and both endpoint theorems.
- Normalized every nonzero spectral value to the unit circle and reused
  `exists_even_gt_forall_circle_pow_dist_one_lt` to align all phases near `1` at one arbitrarily
  large power.
- Proved that phase closeness gives a strict `3/4` real-part lower bound after restoring each
  modulus. Every term then has nonnegative real part, including zero terms and the `n=0` case.
- If one modulus exceeds `R`, exponential growth makes its real contribution larger than
  `C*R^n`; the aggregate norm bound yields a contradiction. This handles duplicates and exact
  cancellation patterns such as `{a,-a}` without distinctness or positivity assumptions.
- Applied the radius theorem to both members of an arbitrary permutation pairing. The norm of the
  product is `q`, while both factors are at most `sqrt(q)`; Lean closes equality by real arithmetic.
- Integrated the exact declarations into Targets, TargetChecks, AxiomsAudit, and the project root.
- `result`: `LOCAL_IMPLEMENTATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 1
- `engineering_delta`: 1

## Mechanical audit

- preregistration diff check: passed before preregistration publication
- public preregistration commit and CI: passed at commit
  `af15b161049aedd65d46fd1f2af1f27e8dc69d44`, run `29505635350`, job `87645529929`
- exact module compilation: diagnostic-free
- `Targets.lean`: exact H10 target compiles
- `TargetChecks.lean`: both exact witnesses compile
- `AxiomsAudit.lean`: both selected transitive axiom prints are exactly `propext`,
  `Classical.choice`, and `Quot.sound`
- forbidden token/declaration/resource scan: empty
- witness and source-alignment audit: passed locally; finite spectral theorem is explicitly
  separated from the curve point-count theorem and number-field transfer
- full `lake build`: passed locally, 8,685 jobs
- implementation public CI: passed at commit
  `2fc3a7e8efff9636735dcdab0055957a7fdf911f`, run `29506928654`, job `87649987984`, in `1m51s`

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `assumption_frontier_after`: finite all-power aggregate bound plus reciprocal product pairing
  implies the exact critical circle; no curve point-count premise was constructed
- `hard_gap_after`: H6-E/G8, W2/G7, M2/G3, and RH remain open; H10's curve construction and
  number-field transfer gaps remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `OBS_node`: none; arbitrary finite cancellation is handled by simultaneous phase alignment
- `theorem_names`: `norm_le_of_forall_norm_finiteComplexPowerSum_le`,
  `norm_eq_sqrt_of_powerSum_bound_and_reciprocal`
- `failure_or_obstacle`: the Riemann zeta zero divisor is infinite and the route has no finite
  Frobenius trace model or uniform tail estimate that would let this finite theorem exclude an
  off-line zero
- `route_selection_decision`: H10-B locally complete; fresh route selection is required only
  after implementation and evidence commits pass public CI
- `preregistration_commit_and_CI`: commit `af15b161049aedd65d46fd1f2af1f27e8dc69d44`, run
  `29505635350`, job `87645529929`, passed in `1m56s`
- `implementation_commit`: `2fc3a7e8efff9636735dcdab0055957a7fdf911f`
- `implementation_CI`: public Lean Action run `29506928654`, build job `87649987984`, passed in
  `1m51s` (`2026-07-16T14:30:56Z` to `2026-07-16T14:32:47Z`)
- `evidence_commit_and_CI`: pending
