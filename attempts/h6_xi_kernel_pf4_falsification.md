# H6 Actual Xi-Kernel Global PF4 Falsification

Campaign: `FALSIFICATION-20260717-H6-XI-KERNEL-PF4-01`

Mode: `FALSIFICATION`

Status: `PUBLICLY_CLOSED`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited continuation; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, route atlas, and the publicly closed PF5 attempt were reread before
  route selection
- `global_goal`: active

## Selection record

- `exact_target`: find explicit rational strictly increasing `Fin 4` tuples with a negative
  determinant for the actual full even Xi kernel, then derive source-faithful `not PF4`
- `primary_source`: Michalowski 2026, arXiv:2602.20313, unreviewed preprint; global PF4 is stated
  there as an open problem
- `material_difference`: search non-Toeplitz configurations in the full seven-parameter space,
  whereas the source and prior project campaign establish only Toeplitz evidence at order four
- `nearest_attempt`: publicly closed actual Xi-kernel PF5 falsification campaign
- `assumption_frontier_before`: the actual full kernel, rational exponential enclosure layer,
  exact infinite-tail bounds, determinant perturbation method, strict TP2, and exact PF5 failure
  compile; no global PF4 theorem or counterexample is compiled
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open

## Frozen success rule

Only a compiled exact full-`tsum` negative `4x4` determinant plus ordered witnesses and the
quantified `not PF4` endpoint counts as success. A numerical candidate, a finite kernel prefix, a
negative rational-center determinant, or an abstract conditional theorem is insufficient.

If the bounded search finds no robust negative candidate, record all searched domains and the best
margin as `NO_PROGRESS`; this is not evidence that PF4 holds. If Lean fails on a selected witness,
record the first exact missing bound or normalization and keep all kernel-level claims unset.

## Preregistration audit

- Source definition, open-problem boundary, exact target, search space, success rule, failure rule,
  DAG relation, and stop boundary are frozen in
  `research/h6_xi_kernel_pf4_falsification_prereg_20260717.md`.
- No proof source has been edited for this campaign before the preregistration commit.
- Public preregistration commit: `b7b4ec77654095c93f3a0b980d42e7ad8784a1fe`.
- Lean Action CI run `29566305052`, build job `87839586304`, succeeded in `2m12s`.

## Numerical search record

- Reproducible search tool: `research/tools/search_xi_kernel_pf4.py`.
- Parameterization: `x_0=0`, three positive `x` gaps, free `y_0`, and three positive `y` gaps.
- Kernel evaluation: eight theta summands in double precision for broad selection; retained
  candidates are rounded to rational grids and reevaluated with 80-digit Decimal arithmetic and
  sixteen summands.
- The script and every output remain target-selection evidence only.

### Calibrated bounded-search stop suite

The initial `10,000`-sample calibration exposed ill-conditioned false negatives, so the search
metric was corrected before freezing the following terminal suite:

1. Central random domain: seed `20260717`, `1,000,000` samples, `y_0` in `[-0.35,0.35]`, six
   log-uniform gaps in `[0.01,0.25]`, condition threshold `10^12`.
2. Compact random domain: seed `20260718`, `5,000,000` samples, `y_0` in `[-0.3,0.3]`, six
   log-uniform gaps in `[0.02,0.2]`, condition threshold `10^12`.
3. Broad random domain: seed `20260719`, `5,000,000` samples, `y_0` in `[-1,1]`, six log-uniform
   gaps in `[0.005,0.5]`, condition threshold `10^12`.
4. Rational-lattice minor domain: all pairs of four-element subsets of a 12-point lattice, steps
   `0.01,0.02,0.03,0.04,0.05,0.06,0.08,0.1,0.12,0.15,0.2`, and offset fractions
   `0,0.1,0.2,0.3,0.4,0.5`; reevaluate the twelve least-conditioned double-negative candidates
   at 120-digit Decimal precision.

After these four suites, either freeze a rational negative witness for Lean or close this
campaign as `NO_PROGRESS`. Additional unregistered optimization is outside this campaign.

### Completed search results

- Calibration: `10,000` broad samples produced 96 double-negative values. Every retained value
  had condition number above `9.4e16`; rational-grid 80-digit Decimal reevaluation made each
  strictly increasing candidate positive. This caused the condition-aware metric correction.
- Central random domain: all `1,000,000` determinants were nonnegative in double precision;
  `robust_negative_double_count=0`. The retained rational-grid Decimal checks were positive.
- Compact random domain: all `5,000,000` determinants were nonnegative in double precision;
  `robust_negative_double_count=0`. The smallest retained row-scaled candidate had double
  determinant approximately `7.78749e-29`, still positive, and all rational-grid checks were
  positive.
- Broad random domain: `5,000,000` samples produced 79,489 double-negative values, but none had
  condition number below `10^12`. The twelve least-conditioned negatives ranged from
  `1.158e16` upward. Rounding each to denominators `1000`, `10000`, and `1000000` and reevaluating
  with 120-digit Decimal arithmetic produced 36 positive determinants.
- Rational-lattice minor domain: all `16,160,859` finite minors were scanned. There were 71,084
  double-negative values and zero negatives below the `10^12` condition threshold. The twelve
  least-conditioned negatives, beginning at condition number `1.150e16`, were reevaluated on the
  exact denominator-1000 lattice at 120 digits; all were positive. The first apparent value
  changed from approximately `-6.195e-47` to `+1.267e-56`.

The broad and lattice false negatives occur in matrices whose sign is below double-precision
conditioning resolution. Decimal reevaluation uses sixteen theta summands and is numerical
target-selection evidence, not a formal interval certificate.

## Closure classification

- `result`: `NO_PROGRESS`
- `reason`: the frozen bounded-search suite produced no robust rational negative determinant, so
  there is no admissible witness to send into the Lean full-`tsum` enclosure pipeline
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 0
- `obstruction_map_delta`: 0; `OBS-H6-XI-PF4-SEARCH-01` records a search boundary, not a
  mathematical counterexample
- `assumption_frontier_after`: unchanged
- `Lean theorem delta`: none; no proof-source, Targets, TargetChecks, or AxiomsAudit declaration
  was added

This campaign neither proves nor gives formal evidence for global PF4. It only reports that a
counterexample was not found in the registered domains. Global PF4, H6-E/G8, W2/G7, M2/G3, and RH
remain open. After closure CI, return the persistent Goal to value-ranked route selection.

## Local closure audit

- Both Python search tools parse under the host Python AST and their calibrated/full runs exit
  successfully.
- `git diff --check` passes.
- Placeholder scans for `sorry` and `admit` are empty across Lean sources.
- Scans for `native_decide`, custom `axiom`/`constant`/`opaque`/`unsafe` declarations, and
  `maxHeartbeats`/`maxRecDepth` relaxation are empty.
- The unchanged Targets, TargetChecks, and AxiomsAudit replay in the full build. No campaign
  declaration was added; existing selected audits retain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Root `lake build` succeeds for all 8,699 jobs.
- Closure commit: `503b83e35761e87b35fe7db3fb49feab8ea372de`.
- Lean Action CI run: `29567807097`.
- Build job: `87844319595`, success in `1m43s`.
- The local campaign is publicly closed as `NO_PROGRESS`. The persistent RH Goal remains active
  and returns to value-ranked route selection.
