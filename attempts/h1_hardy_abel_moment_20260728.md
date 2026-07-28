# H1 Hardy Abel-Moment Amplification Attempt

Campaign: `LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01`

Status: `PREREGISTERED / PRODUCTION_LEAN_EDIT_BLOCKED_PENDING_PUBLIC_CI`

## Target

- `mode`: `LITERATURE`
- `node_id`: `H1-HARDY-ABEL-MOMENT-AMPLIFICATION-01`
- `exact_mathematical_statement`: Hardy's exact interior Abel even-moment law for project
  `hardyXi` implies a zero above every height and infinitely many actual project nontrivial
  zeros on the critical line.
- `proposed_lean_statement`: see
  `research/h1_hardy_abel_moment_prereg_20260728.md`.
- `relation_to_RH`: weaker known theorem and historical route bridge.
- `success_criterion`: full fixed endpoint, exact checks, standard-only axiom audit, full build,
  and all public CI gates.
- `falsification_criterion`: a normalization mismatch, a countermodel to the exact conditional
  implication, or a need for a stronger premise than Hardy's published interior integrability
  and Abel limit.

## Prior state

- `assumption_frontier_before`: project xi is entire, real/even/continuous on the critical line,
  has an exact nontrivial-zero dictionary, and equals eight times the source-normalized
  de Bruijn-Newman transform at heat time zero.
- `hard_gap_before`: Hardy's theta/Mellin transform and the argument producing unbounded
  critical-line zeros are absent from production Lean.
- `known_obstacles`: the source boundary integral at `alpha=pi/2` is not automatically a
  Lebesgue integral; the exact proof must retain the one-sided Abel limit. Interior moment
  integrability and the transform law remain analytic inputs.
- `nearest_primary_source`: Hardy 1914, pages 1012--1014, equations (1)--(6).
- `nearest_project_attempt`: publicly closed
  `LITERATURE-20260726-H1-HARDY-CRITICAL-LINE-SIGN-01`.
- `new_attack_angle`: use the original Abel moment family, not the later Hardy-`Z` proof; connect
  `Xi(2t)` exactly to the existing H6 transform and perform the high-moment contradiction before
  taking an unconditional boundary integral.

## Loop 1 preregistration

- Fresh H1/H2/H7/H9/H10/H12 comparison selected the original Hardy moment mechanism.
- Primary-source equations (1)--(6) were checked against corrected facsimile transcriptions.
- The source's `Xi(2t)` normalization matches `hardyXi (2*t)` and
  `8*deBruijnNewmanH 0 (4*t)`.
- The boundary-convergence issue is explicit: the fixed law is an interior integrability plus
  one-sided Abel-limit proposition.
- No production Lean source has been edited.
- Next gate: commit and push this docs-only preregistration, then require public Lean Action CI.

## Mechanical audit

- exact module compilation: pending public preregistration gate
- `Targets.lean`: pending
- `TargetChecks.lean` exact witness: pending
- `AxiomsAudit.lean` and printed axioms: pending
- forbidden token/declaration/resource scan: pending
- witness audit: pending
- definition/source alignment: preregistered in M0
- full `lake build`: pending after implementation

## Result

- `result_class`: `ACTIVE_LITERATURE_RECONSTRUCTION`
- `assumption_frontier_after`: unchanged at preregistration
- `hard_gap_after`: source Abel moment law remains open; its full contradiction consumer is fixed
- `hard_gap_delta`: 0 at preregistration
- `OBS_node`: none yet
- `theorem_names`: preregistered only
- `failure_or_obstacle`: none yet
- `route_selection_decision`: selected H1 original Abel moment route
- `model`: GPT-5 Codex
- `reasoning_effort`: high
- `budget`: no exposed per-loop or global token budget
- `compaction_state`: inherited compacted summary was revalidated against governance,
  `HANDOFF.md`, route files, production targets, source, git status, and external memory
- `commit_and_CI`: pending
