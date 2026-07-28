# H1 Hardy Abel-Moment Amplification Attempt

Campaign: `LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_PENDING`

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

## Loop 2 public preregistration gate

- Docs-only preregistration commit:
  `03a788e80e6ca0acfb82a41c8e3663bda3a9ef79`.
- Public Lean Action run `30334772898`, build job `90197213274`, passed in `1m38s`.
- The commit contains only the eight intended research and handoff documents; no production
  `LeanLab/` source was edited before the public gate passed.
- Production implementation is now open for the fixed endpoint. The first proof order is:
  exact H1/H6 scaling, source definitions, Abel-limit sign selection, positive-tail
  amplification, negative-tail amplification, unbounded zeros, and actual-zero infinitude.

## Loop 3 complete conditional amplification

- Added the 790-line no-sorry module
  `LeanLab/Riemann/HardyAbelMomentAmplification.lean`.
- Defined Hardy's exact interior integrand, moment, and one-sided Abel law without asserting
  boundary integrability.
- Compiled `hardyXi(2*t)=8*deBruijnNewmanH 0 (4*t)` exactly.
- The Abel limit selects a negative odd interior moment and a positive even interior moment.
- A compact initial interval has a bound `K*T^(2p)` uniform in both `alpha` and `p`.
- Under an eventual positive or negative tail, a fixed interval beyond `2T` gives the
  corresponding signed tail lower bound `C*(2T)^(2p)`, with `C>0` independent of `alpha,p`.
- Powers of 16 supply the required odd and even indices. The exact integral split then gives
  `|initial| < |tail| < |initial|` in each orientation.
- Continuity and tail nonvanishing force a constant sign, so both sign contradictions give a
  `hardyXi` zero above every real height.
- The project zero dictionary converts unbounded real zeros into an infinite set of actual
  critical-line nontrivial zeros.

## Loop 4 frozen implementation public gate

- Frozen implementation commit:
  `2d5b5e2e692e8622263142a1205971c611736a78`.
- Public Lean Action run `30336360223`, build job `90201998436`, passed in `2m17s`.
- The public commit contains the 790-line production module, registry entries, exact checks,
  axiom audit, and the loop logs listed in its 11-file manifest.
- Proof sources are frozen. The next commit is docs-only immutable evidence and must have an
  empty `LeanLab/` diff from the frozen implementation.

## Loop 5 immutable evidence public gate

- Docs-only immutable-evidence commit:
  `2d662d49ebb783d9f3e86a50e752191a12c69754`.
- Public Lean Action run `30336627329`, build job `90202820261`, passed in `1m35s`.
- `git diff --name-only 2d5b5e2e692e8622263142a1205971c611736a78
  2d662d49ebb783d9f3e86a50e752191a12c69754 -- LeanLab` is empty.
- Local stop: `FULL_FIXED_ENDPOINT_SUCCESS`.
- Final gate: publish this closure ledger and require public CI. After it passes, return to fresh
  cross-family `ROUTE_SELECTION`; do not silently continue into proving the Abel law.

## Mechanical audit

- exact module compilation: pass with `-DwarningAsError=true`
- `Targets.lean`: pass; one proven aggregate conditional endpoint
- `TargetChecks.lean` exact witness: pass; 11 exact witnesses
- `AxiomsAudit.lean` and printed axioms: pass; eight selected declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`
- forbidden token/declaration/resource scan: empty for the new module
- witness audit: pass, including both parities and actual-zero infinitude
- definition/source alignment: exact H1/H6 scaling and literal source denominator compiled
- full `lake build`: pass, `8777/8777`
- `git diff --check`: pass

## Result

- `result_class`: `HARDY_ABEL_MOMENT_AMPLIFICATION_FORMALIZED`
- `assumption_frontier_after`: the full high-moment contradiction, unbounded-zero consumer, and
  actual-zero infinitude are compiled conditional only on `HardyXiAbelMomentLaw`
- `hard_gap_after`: proving the law from Cahen-Mellin/theta inversion remains open
- `hard_gap_delta`: 0; the source analytic law has not been proved
- `OBS_node`: none yet
- `theorem_names`: `hardyXi_two_mul_eq_deBruijnNewmanH_zero_four_mul`,
  `exists_interior_hardyXiAbelMoment_odd_neg`,
  `exists_interior_hardyXiAbelMoment_even_pos`,
  `not_eventually_hardyXi_two_mul_pos`,
  `not_eventually_hardyXi_two_mul_neg`,
  `exists_hardyXi_zero_above_of_abelMomentLaw`,
  `infinite_criticalLineZeros_of_hardyXiAbelMomentLaw`,
  `hardyXiAbelMomentAmplification_endpoint`
- `failure_or_obstacle`: no contradiction-consumer obstacle; the remaining obstacle is the
  source Abel law itself
- `route_selection_decision`: freeze and publish the implementation, then publish immutable
  evidence before returning to cross-family route selection
- `model`: GPT-5 Codex
- `reasoning_effort`: high
- `budget`: no exposed per-loop or global token budget
- `compaction_state`: inherited compacted summary was revalidated against governance,
  `HANDOFF.md`, route files, production targets, source, git status, and external memory
- `commit_and_CI`: preregistration commit
  `03a788e80e6ca0acfb82a41c8e3663bda3a9ef79` passed public run `30334772898`,
  job `90197213274`; frozen implementation
  `2d5b5e2e692e8622263142a1205971c611736a78` passed public run `30336360223`,
  job `90201998436`; immutable evidence
  `2d662d49ebb783d9f3e86a50e752191a12c69754` passed public run `30336627329`,
  job `90202820261`; final-ledger CI pending
