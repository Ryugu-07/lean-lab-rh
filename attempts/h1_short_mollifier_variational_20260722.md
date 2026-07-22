# H1 Short-Mollifier Variational Attempt

Campaign: `LITERATURE-20260722-H1-SHORT-MOLLIFIER-VARIATIONAL-01`

Mode: `LITERATURE`

Status: `LOCAL_SUCCESS / IMPLEMENTATION_COMMIT_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: one inherited compaction recovery completed during implementation.
- `global_goal`: active.

## Baseline

- `parent_commit`: `7e15cfb386e961f7437dfa25d39b6cab85d3946b`.
- `parent_public_ci`: run `29934044666`, build job `88970856616`, passed in `1m37s`.
- `selected_node`: `H1-SHORT-MOLLIFIER-VARIATIONAL-01`.
- `preregistration`: `research/h1_short_mollifier_variational_prereg_20260722.md`.
- `primary_source`: arXiv:2508.11108v1, equations `(58)`-`(63)`.

## Preregistered endpoint

Prove that the source parameter condition `c < 1/4` makes the general short-mollifier variational
functional strictly convex on fixed-endpoint paths. The proof must compile the exact weighted
Hardy identity, align source `K/c1` with the normalized energy, derive the exact energy gap from
the Euler-Lagrange equation, and conclude unique global minimality without hypergeometric or
numerical premises.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | Compared the closed H7 residual with H1 mollifiers, H2 density, H11 statistics, and H10 function-field transfer. H2/H11 still lack an exceptional-zero localizer and H10 lacks a number-field trace object. H1 contains a source-identified underused derivative-combination freedom and an exact continuum variational target. | Select H1 rather than continue H7 scalar optimization. Keep sparse-exception and arithmetic mean-value barriers explicit. |
| 2 | `SOURCE_AUDIT / PREREGISTRATION` | Read arXiv:2508.11108v1 equations `(12)`-`(31)` and `(58)`-`(63)`. The source gives the Euler-Lagrange solution under `c < 1/4`; the discriminating Lean endpoint is global-minimizer sufficiency via the weighted `1/4` Hardy threshold, not a decimal proportion. | Publish preregistration alone. Require public CI before any Lean proof-source edit. |
| 3 | `LEAN IMPLEMENTATION` | Proved the exact weighted completion identity, the endpoint Hardy inequality, source normalization, and the Euler-Lagrange energy gap. The `1/4` threshold comes from `cosh^2-sinh^2=1` and integration by parts, not numerical optimization. | Continue to strict coercivity. Require a positive-length interval and a pointwise-distinct continuous path rather than inferring strict integral positivity from a bare point witness. |
| 4 | `STRICTNESS / MECHANICAL AUDIT` | Proved strict positivity for `c<1/4`, then both normalized and source-functional unique-global-minimizer certificates. The 374-line module, six exact TargetChecks, six standard-only axiom prints, forbidden scan, `git diff --check`, and full 8,740-job build pass. | Local success. Publish the implementation commit and require public CI; retain the long-mean-value and sparse-exception nodes as the actual H1 barriers. |

## Assumption and gap accounting

- `assumption_frontier_before`: Euler-Lagrange stationarity plus source endpoints.
- `target_reduction`: prove coercivity and the exact energy gap, thereby justifying unique global
  minimality over the represented path class.
- `hard_gap_before`: unconditional long/twisted mean values sufficient for proportion one and a
  quantitative exceptional-zero eliminator.
- `rh_frontier_before`: RH open.
- `current_result`: `PROVED / KNOWN_ANALYSIS_FORMALIZED / SOURCE_SUFFICIENCY_CERTIFIED`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `route_infrastructure_delta`: `1`.
- `source_sufficiency_audit_delta`: `1`.
- `theorem_spine`: `shortMollifierSourceEnergy_eq_mul_normalized`,
  `shortMollifierWeightedHardyIdentity`, `shortMollifierWeightedHardy_quarter_le`,
  `shortMollifierNormalizedEnergy_gap_of_eulerLagrange`,
  `shortMollifierWeightedVariation_pos`, and
  `shortMollifierSourceEnergy_unique_minimizer`.
- `compiler`: standalone production module, six exact TargetChecks, AxiomsAudit, and the full
  `8,740`-job build pass.
- `axioms`: all six selected declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- `remaining_obstacles`: `OBS-H1-LONG-MEAN-VALUE-01` and
  `OBS-H1-SPARSE-EXCEPTION-01`. The theorem does not prove the source mean-value asymptotic,
  proportion one, or exclusion of a finite/density-zero off-line orbit.
- `next_gate`: implementation commit and public CI, followed by immutable evidence backfill.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
