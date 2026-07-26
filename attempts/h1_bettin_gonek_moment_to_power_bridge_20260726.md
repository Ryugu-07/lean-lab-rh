# H1 Bettin--Gonek Moment-to-Power Bridge

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-BETTIN-GONEK-MOMENT-TO-POWER-BRIDGE-01`

Selected node: `H1-BETTIN-GONEK-MOMENT-TO-POWER-BRIDGE-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT`.
- `exact_mathematical_statement`: Bettin--Gonek Theorem 1: for every `theta>0`, the source
  uniform mollified moment bound through length `T^theta` implies the zero-free half-plane
  `Re(s)<=1/2+1/(2*theta)` for every nontrivial zero.
- `proposed_lean_statement`: prove `BettinGonekMomentToPowerBridge theta` for every positive
  `theta`, then discharge the bridge premise in the existing theta-infinity-to-RH consumer.
- `relation_to_RH`: known conditional bridge. Farmer's theta-infinity conjecture remains open.
- `success_criterion`: unconditional compilation of the full bridge and source RH corollary,
  followed by all mechanical and public evidence gates.
- `falsification_criterion`: a compiled exponent/normalization mismatch or an exact proof that
  the registered moment hypothesis cannot control one required source term.

## Prior state

- `assumption_frontier_before`: the actual Mellin identity, inverse Mellin kernel, convolution,
  contour residue, and exponent consumer compile.
- `hard_gap_before`: Cauchy--Schwarz, real-cutoff-to-integer moment assembly, positive zeta mass,
  and asymptotic bookkeeping have not been combined for the actual objects.
- `nearest_primary_source`: Bettin--Gonek, arXiv:1604.02740, Theorem 1 and equations
  `(2.1)`--`(2.5)`.
- `nearest_project_attempt`: the inverse-Mellin/convolution campaign publicly closed equation
  `(2.4)` but stopped before moment transfer.
- `new_attack_angle`: use a fixed low-height interval and positivity at `t=0`, avoiding the
  stronger global critical-line second-moment lower bound previously listed as necessary.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H1 moment transfer, H12 analytic Speiser counts, H2 actual-zeta bow exclusion, H10 transfer, and post-formula H7 positivity/density. | H1 is the only candidate whose missing source theorem now lies between actual compiled objects and admits a materially new attack. | Select the full Bettin--Gonek moment-to-power bridge. |
| `SOURCE_RECONSTRUCTION` | Re-read the primary TeX for Theorem 1 and equations `(2.1)`--`(2.5)`. | After squaring the residue inequality, the Cauchy factor cancels the extra `x`; the remaining real-cutoff moment contributes exactly one factor of `x`, producing exponent `1+epsilon+theta`. | Preserve this normalization exactly. |
| `OMISSION_AUDIT` | Specialized the source proof to `T1=0`. | A fixed compact interval with positive zeta mass suffices; the full asymptotic second moment is unnecessary for Theorem 1. | Register fixed-low-height Attack A and source fallback B. |
| `API_AUDIT` | Located exact residue, inverse-Mellin, real-cutoff interpolation, interval partition, finite Cauchy, positivity, and real-power APIs. | No target-equivalent premise is needed at the statement level. Joint real-cutoff/time Fubini can be avoided by partitioning into integer intervals before integrating in time. | Preregister the full endpoint and gate production edits on public CI. |
| `PUBLIC_PREREGISTRATION` | Published the fixed endpoint and attacks before production proof editing. | Commit `3df6ed836c550671a0e552a09bbba314fcab5c1c` passed Lean Action run `30188267224`, build job `89756704490`, in `1m31s`. | Open the production gate without changing the endpoint. |
| `ATTACK_A_FIXED_MASS` | Proved nonvanishing at `1/2`, positive zeta squared mass on `[0,1]`, a selected-zero residue lower bound uniform in `t`, and translation invariance of the inverse-Mellin majorant. | Every fixed analytic constant required by the compact-height attack is strictly positive or finite for the actual source objects. | Assemble the real-cutoff estimate. |
| `ATTACK_A_INTEGER_ASSEMBLY` | Handled `[1,2]` directly, partitioned `[1,X]` into unit intervals, reduced real cutoffs to neighboring integer mollifiers, and applied finite Cauchy. | The integrated source lower bound is controlled by the exact finite sum of Farmer integer moments on `[0,1]`. | Embed those moments into the assumed `[0,T]` moments. |
| `ATTACK_A_POWER_ASYMPTOTICS` | Used moment monotonicity, `X=floor(T^theta)`, floor comparison, logarithmic absorption, and real-power algebra. | Lean derives the registered exponent `T^(2*Re(rho)*theta) << T^(1+epsilon+theta)` for every nontrivial zero. | Close the aggregate bridge and RH consumer. |
| `ENDPOINT_CLOSURE` | Proved the full bridge for every positive `theta` and supplied it directly to the existing reflection/exponent consumer. | `bettinGonekMomentToPowerBridge_of_pos` and `farmerThetaInfinityConjecture_implies_riemannHypothesis_bettinGonek` compile. Attack A succeeds; fallback B is not needed. | Run registration, axiom, forbidden-token, and full-build gates. |
| `LOCAL_MECHANICAL_AUDIT` | Compiled the production module with warnings as errors, checked exact Targets and audits, scanned forbidden declarations/tokens and resource relaxations, and ran the complete project build. | All local gates pass; selected transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`; full build is `8763/8763`. | Freeze and publish the implementation. |

## Mechanical audit

- exact module compilation: `PASS_WARNING_AS_ERROR`.
- `Targets.lean`: `PASS_PROVEN_TARGET`.
- `TargetChecks.lean`: `PASS_EXACT_ENDPOINTS`.
- `AxiomsAudit.lean`: `PASS_STANDARD_ONLY`.
- forbidden scan: `PASS_EMPTY`.
- witness audit: `NOT_NUMERICAL`.
- definition/source alignment: `PASS`.
- full `lake build`: `PASS_8763_OF_8763`.

## Runtime record

- `model`: `GPT-5 Codex`.
- `reasoning_effort`: `high`.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: inherited compacted context was reloaded from governance, HANDOFF, active
  memory, route cards, attempts, Targets, and live repository state before selection.
- `global_goal`: active.

## Result

- `result_class`: `FULL_MOMENT_TO_POWER_SUCCESS_LOCAL`.
- `source_analytic_bridge_delta`: `1`.
- `known_theorem_formalization_delta`: `1`.
- `historical_route_coverage_delta`: `1`.
- `hard_gap_delta`: `0` for RH; Farmer's conjecture remains the open hard gap.
- `rh_frontier_delta`: `0`.
- `theorem_names`: `bettinGonekMomentToPowerBridge_of_pos`;
  `farmerThetaInfinityConjecture_implies_riemannHypothesis_bettinGonek`.
- `failure_or_obstacle`: none at the registered bridge; Attack A succeeded and fallback B was
  not needed.
- `route_selection_decision`: freeze and publish this implementation, then return to a fresh
  cross-family route comparison after public closure.
- `commit_and_CI`: preregistration commit
  `3df6ed836c550671a0e552a09bbba314fcab5c1c` passed public Lean Action run
  `30188267224`, build job `89756704490`, in `1m31s`; frozen implementation commit
  `d07fecd2f00748cf0dc2a4c19d15d89bb740a2e1` passed run `30189533073`, build job
  `89760104494`, in `2m31s`; docs-only immutable-evidence commit
  `6970f6b41ad5b1459504dab99a963482630a4b89` passed run `30189646824`, build job
  `89760437385`, in `2m2s`. Final-ledger CI pending.
