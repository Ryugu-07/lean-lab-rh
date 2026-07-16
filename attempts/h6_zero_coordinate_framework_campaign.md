# H6 Zero-Coordinate Framework Campaign

Campaign: `CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01`

Mode: `LITERATURE`

Status: `PUBLIC_IMPLEMENTATION_COMPLETE_EVIDENCE_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: continued from the publicly closed H6 reverse-heat Li audit; canonical
  governance, HANDOFF, Targets, DAG, route cards, and recent attempts reread
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: the four-clause H6 zero-coordinate framework in
  `research/h6_zero_coordinate_framework_prereg_20260717.md`.
- `relation_to_RH`: exact H6 endpoint alignment; the final clause is RH-equivalent and does not
  prove either side unconditionally.
- `success_criterion`: exact coordinate, inverse-coordinate zero correspondence, strict strip,
  and all-real-zero RH equivalence, followed by every mechanical and public CI gate.
- `falsification_criterion`: any fixed clause fails under the compiled source normalization.
- `assumption_frontier_before`: exact source `H_0`-xi identity and all-real-time heat equation;
  no compiled all-real-zero coordinate framework.
- `hard_gap_before`: H6-H2, H6-E/G8, W2/G7, M2/G3, and RH open.
- `known_obstacle`: coordinate sign/factor alignment, strict boundary exclusion, and surjectivity
  from arbitrary nontrivial zeros must all be kernel-checked.
- `nearest_primary_source`: D. H. J. Polymath 2019 and Rodgers-Tao 2018.
- `nearest_project_attempt`: H6-B and H6-H1 are publicly closed; the H6 reverse-heat Li audit
  eliminates only a generic shortcut.
- `new_attack_angle`: expose the exact zero coordinate and RH endpoint before attempting global
  heat-flow zero dynamics or a Newman threshold.

## Selection and preregistration loop

- Reread the canonical protocol and all post-compaction authority files.
- Compared H1/H2 finite counts, direct M2/G3 and W2/G7 re-entry, H6-Q, H6-X, and H6-H2.
- Rechecked the exact Polymath/Rodgers-Tao normalization and the project's compiled xi-zero bridge.
- Fixed all four declarations and boundary tests before any Lean proof-source edit.
- Preregistration commit `8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e` passed public Lean Action CI
  run `29512089828`, build job `87667820977`, in `2m17s`.
- `result`: public preregistration complete; implementation active
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Lean implementation loop

- Added `DeBruijnNewmanZeros.lean` with the exact all-real-zero predicate and inverse source
  coordinate `-i*(2*s-1)`.
- Lean normalizes the coordinate's real and imaginary parts and proves
  `(1+i*z(s))/2=s` exactly.
- The nonzero factor `1/8` and the compiled xi-zero bridge yield both directions of the `H_0`
  zero/nontrivial-zero correspondence.
- Xi reflection plus the strict right critical-strip bound gives `0<Re(s)<1`; the exact coordinate
  then gives `-1<Im(z)<1` for every time-zero zero.
- The strip theorem kernel-checks both adversarial boundaries `H_0(i)!=0` and `H_0(-i)!=0`.
- Transporting `OnCriticalLine` through the coordinate in both directions proves the exact
  `RiemannHypothesis <-> deBruijnNewmanAllZerosReal 0` statement.
- Registered one aggregate theorem containing every endpoint clause.
- `result`: `KNOWN_THEOREM_FORMALIZED`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 1
- `engineering_delta`: 1

## Mechanical audit

- preregistration diff check: passed before staging
- public preregistration commit and CI: passed at commit
  `8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e`, run `29512089828`, job `87667820977`
- exact module compilation: diagnostic-free
- `Targets.lean`: exact H6 zero-coordinate target compiles as proven
- `TargetChecks.lean`: exact aggregate witness and both boundary witnesses compile
- `AxiomsAudit.lean`: all five selected theorem prints use only `propext`, `Classical.choice`, and
  `Quot.sound`
- forbidden token/declaration/resource scan: empty
- witness and definition alignment: exact source coordinate, inverse, strict strip, and all-complex
  zero quantifier compile; no multiplicity claim is made
- full `lake build`: passed locally, 8,687 jobs
- `git diff --check`: passed before documentation backfill
- implementation public CI: passed at commit
  `0283db6a11ef452a7241e17c535744677272a7d1`, run `29513380203`, job `87672181193`, in `1m59s`
- immutable evidence backfill and public CI: pending

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `assumption_frontier_after`: exact time-zero all-real-zero predicate, bijective zero coordinate,
  strict strip, and RH equivalence are compiled and available as premises
- `hard_gap_after`: H6-H2 forward preservation and threshold existence/closedness, H6-E/G8,
  W2/G7, M2/G3, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `OBS_node`: none
- `theorem_names`: `deBruijnNewmanH_zero_iff_isNontrivialZero`,
  `deBruijnNewmanH_zeroCoordinate_eq_zero_iff`, `deBruijnNewmanH_zero_im_mem_Ioo`,
  `deBruijnNewmanH_zero_I_ne_zero`, `deBruijnNewmanH_zero_neg_I_ne_zero`,
  `riemannHypothesis_iff_deBruijnNewmanAllZerosReal_zero`,
  `deBruijnNewman_zeroCoordinate_framework`
- `failure_or_obstacle`: no coordinate or boundary obstruction; the next H6 obstacle is the
  global de Bruijn zero-preservation/threshold theory
- `route_selection_decision`: publish implementation, require public CI, then backfill immutable
  evidence before closure
- `preregistration_commit_and_CI`: commit `8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e`,
  run `29512089828`, job `87667820977`, passed in `2m17s`
- `implementation_commit_and_CI`: commit `0283db6a11ef452a7241e17c535744677272a7d1`,
  run `29513380203`, job `87672181193`, passed in `1m59s`
- `evidence_commit_and_CI`: pending
