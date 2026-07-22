# H7 Finite Herglotz Criterion Attempt

Campaign: `LITERATURE-20260722-H7-WEIL-HERGLOTZ-CRITERION-01`

Mode: `LITERATURE`

Status: `LOCAL_ENDPOINT_PROVED / PUBLIC_IMPLEMENTATION_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: one inherited implementation recovery; all mandatory authority and frontier
  files plus the complete new source were re-read before compilation resumed.
- `global_goal`: active.

## Baseline

- `parent_commit`: `c5ba3ab66e9a61446da7ad43d3a1d3786efd220d`.
- `baseline_public_ci`: run `29930876406`, build job `88959943824`, passed in `1m45s`.
- `preregistration_commit`: `47d6adb4d8f25bf3d631cd449159a98eb1b94c20`.
- `preregistration_public_ci`: run `29931671154`, build job `88962703883`, passed in `1m55s`.
- `selected_node`: `H7-WEIL-GROUNDSTATE-HERGLOTZ-01`.
- `preregistration`: `research/h7_weil_herglotz_criterion_prereg_20260722.md`.

## Preregistered endpoint

Prove the exact finite rank-one Herglotz criterion on the reflection-odd sector: for a strictly
positive pole-free shifted form `P`, odd pole vector `S`, and odd resolvent vector `u` satisfying
`P*u=S`, strict positivity after the source update `P-2*S*S^T` is equivalent to
`2*(S dot u)<1`. Connect that iff to the compiled parity Rayleigh certificate without asserting
the arithmetic scalar bound.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION / SOURCE_AUDIT` | Compared the H7 true-ground-state limit, H1 runner-up, and four direct June 2026 Perron/Loewner/Herglotz sources. The scalar odd-sector criterion is the narrowest human frontier that directly consumes the public finite matrix/parity interface. | Select a separate finite Herglotz criterion campaign. Keep all S3 operator and arithmetic claims outside the premise set. |
| 2 | `PREREGISTRATION` | Fixed the completion-of-square identity, strict-positivity iff, certificate consumer, source sign, threshold, assumptions, and local stop. No Lean proof source was edited. | Publish preregistration alone and require public CI before implementation. |
| 3 | `LITERATURE / LEAN_IMPLEMENTATION` | Lean proves the exact completion-of-squares identity and both directions of the rank-one strict-positivity iff, then constructs the previous parity Rayleigh certificate and simple-even endpoint. The kernel proof exposes that oddness of `S` is unnecessary for the generic iff; oddness of `u` alone keeps the shifted test vector in the odd sector. | Record the weaker generic theorem while retaining `odd_S` in the source-aligned certificate. Do not infer the arithmetic scalar inequality. |
| 4 | `INDEPENDENT_LOCAL_AUDIT` | The 171-line module, Targets, six exact TargetChecks, six selected standard-only axiom prints, empty production forbidden scan, `git diff --check`, and the full 8,739-job build pass. | Classify as finite source infrastructure plus one checked assumption weakening, with no RH or hard-gap delta. Publish implementation and require public CI. |

## Compiled declarations

- `weilFiniteRankOneDeflation_mulVec`;
- `weilFiniteRankOneDeflectionQuadratic`;
- `weilFiniteOddRankOneStrict_iff_resolvent`;
- `WeilFiniteOddHerglotzCertificate.strict_odd`;
- `WeilFiniteOddHerglotzCertificate.parityRayleighCertificate`;
- `WeilFiniteOddHerglotzCertificate.evenSimpleGroundState`.

All six selected declarations print only `propext`, `Classical.choice`, and `Quot.sound`.

## Assumption and gap accounting

- `assumption_frontier_before`: all-vector strict odd Rayleigh positivity.
- `target_reduction`: pole-free odd positivity plus one scalar resolvent inequality.
- `hard_gap_before`: prove that scalar inequality uniformly for the arithmetic matrices; prove the
  actual ground-state-to-`k_lambda` comparison.
- `rh_frontier_before`: RH open.
- `current_result`: `PROVED / KNOWN_FINITE_LINEAR_ALGEBRA_FORMALIZED /
  SOURCE_ASSUMPTION_WEAKENED / FINITE_CERTIFICATE_CONSUMER`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `route_infrastructure_delta`: `1`.
- `obstruction_map_delta`: `1`.
- `source_assumption_weakening_delta`: `1` for deletion of `odd_S` from the generic iff only.
- `still_open`: prove or falsify the arithmetic scalar inequality uniformly in the actual Weil
  matrices; prove uniform simple-even structure and the true ground-state limit; prove RH.
- `next_gate`: implementation commit and public CI.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
