# H12 Levinson--Montgomery Paired-Mass Density

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-PAIRED-MASS-DENSITY-01`

Selected node: `H12-LM-PAIRED-MASS-DENSITY-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT`.
- `exact_mathematical_statement`: reconstruct Levinson--Montgomery equations `(2.2)`--`(2.3)`
  over the actual multiplicity-bearing xi zero divisor, prove negative paired mass localizes a
  left zero within half a height unit, and prove eventual negative mass at integer heights
  implies `N^-(T)>T/2` for all sufficiently large real `T`.
- `proposed_lean_statement`: define the actual paired zero mass and prove
  `levinsonMontgomery_real_paired_zero_sum_eq`,
  `exists_upperLeft_zero_abs_im_sub_lt_half_of_pairedMass_neg`, and
  `levinsonMontgomeryDenseBranch_of_pairedMassNegativeAtIntegers`.
- `relation_to_RH`: one analytic branch inside the known Speiser equivalence proof. It does not
  assume or prove the remaining Levinson--Montgomery count theorem or RH.
- `success_criterion`: full actual-zero, multiplicity-bearing dense branch plus all mechanical
  and public gates.
- `falsification_criterion`: exact pairing, summability, multiplicity, or boundary mismatch.

## Prior state

- `parent_closed`: H1 moment-to-power final-ledger commit
  `281ba918582707bcfed21920fb3616120d5cd292`, public run `30189742343`, build job
  `89760720303`, passed in `2m2s`.
- `nearest_attempt`: the 2026-07-23 H12 consumer campaign compiled the actual counts and
  conditional Speiser equivalence but stopped at
  `LevinsonMontgomeryLogCountBound` and `LevinsonMontgomeryCountDichotomy`.
- `new_attack_angle`: use the later H7/Li xi-divisor infrastructure to reconstruct the source
  real paired infinite sum and then complete the integer-neighborhood density argument.
- `nearest_primary_source`: Levinson--Montgomery 1974, Theorem 1, equations `(2.2)`--`(2.3)`.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H12 paired mass, H1 Farmer moments, H7 positivity/limits, H2/H11 sparse amplification, and H10 transfer. | H12 is the strongest unformalized known-source edge with a new cross-route input. | Select the paired-mass dense branch. |
| `SOURCE_RECONSTRUCTION` | Downloaded and rendered the original 1974 Acta paper and checked Theorem 1 plus equations `(2.1)`--`(2.4)`. | The dense alternative comes from a negative functional-equation-paired zero mass at each large integer, not from the `O(log T)` estimate. | Freeze equations `(2.2)`--`(2.3)` and the `T/2` count branch. |
| `PRIOR_ATTEMPT_AUDIT` | Re-read the earlier H12 consumer and current H7/Li zero-sum modules. | The first H12 attempt lacked the now-compiled compensated Hadamard sum, divisor permutations, reciprocal-square mass, and robust finite/infinite decomposition. | Re-enter H12 with the actual infinite paired mass. |
| `API_AUDIT` | Located the global xi divisor index, reflection and conjugation equivalences, zeta/xi multiplicity alignment, finite upper-left count, and Jensen/norm cutoffs. | The main risks are summability of the raw real pair and multiplicity-copy-to-weighted-count conversion; no target-equivalent premise is required. | Preregister Attack A and finite-cutoff fallback B. |
| `PREREGISTRATION_GATE` | Published the exact endpoint and both registered attacks before production proof edits. | Commit `8990be949f0160c593a55bf710714bdaeeef1768` passed run `30190223668`, job `89762046622`, in `1m34s`. | Open production editing. |
| `ATTACK_A_PAIRING` | Composed the multiplicity-preserving conjugation and functional-equation divisor permutations, then averaged each `rho,1-conj(rho)` reciprocal pair by `1/2`. | Off-line divisor copies recover the source coefficient two and critical-line copies recover coefficient one without subtype splitting. | Prove summability and the rational kernel identity. |
| `ATTACK_A_SUMMABILITY` | Rewrote the real reciprocal pair through two compensated Hadamard terms and bounded the real reciprocal constants by the compiled inverse-square divisor series. | The paired reciprocal term and explicit mass kernel are summable away from xi zeros. | Pass the pointwise identity through `tsum`. |
| `ATTACK_A_LOCALIZER` | Proved the exact rational identity and used negativity of the mass `tsum` to select a negative kernel term. | The negative numerator gives `|t-gamma|<1/2`; functional-equation reflection moves a right-half witness to the upper-left strip. | Amplify integer-height witnesses. |
| `ATTACK_A_DENSITY` | Selected one actual zero at each sufficiently large integer, proved injectivity from disjoint strict half-unit neighborhoods, and embedded the finite image into `speiserUpperLeftZetaZeroFinset T`. | Multiplicity is at least one on every selected value, and floor bookkeeping yields `T/2 < speiserUpperLeftZetaZeroCount T` eventually. | Register and freeze the full endpoint. |
| `ATTACK_B` | Finite symmetric cutoffs. | Not needed because direct paired summability compiled. | Retain only as historical fallback. |
| `PUBLIC_IMPLEMENTATION` | Published the frozen proof, Target, exact checks, and axiom audit. | Commit `0b5b6d5c44cddb680be721c54a6fc9d261e01ba5` passed run `30190754950`, job `89763478543`, in `2m6s`. | Publish immutable docs-only evidence. |
| `IMMUTABLE_EVIDENCE` | Published the complete attempts, source-alignment, route, DAG, and handoff evidence without touching proof source. | Commit `38071d8a6c085b74bd1f8d258cb6e83cec55d592` passed run `30190894736`, job `89763862993`, in `1m33s`. | Publish one final closure ledger. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: inherited compacted context was reloaded from governance, HANDOFF, active
  memory, Targets, the prior H12 attempt, the hard-gap DAG, live repository state, and the
  rendered primary source before selection.
- `global_goal`: active.

## Mechanical audit

- exact module compilation: `CLOSED`, 403 lines under warning-as-error.
- `Targets.lean`: `PROVEN`, node
  `H12.speiser.levinson-montgomery-paired-mass-density`.
- `TargetChecks.lean`: `CLOSED`, all three mandatory endpoints checked verbatim.
- `AxiomsAudit.lean`: `CLOSED`, five selected transitive prints use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- forbidden scan: `EMPTY`.
- witness audit: `CLOSED_ACTUAL_MULTIPLICITY_BEARING_XI_DIVISOR`.
- definition/source alignment: `CLOSED_GLOBAL_HALF_PAIR_EQUIVALENT_TO_SOURCE_SPLIT`.
- full `lake build`: `PASSED_8764_OF_8764`.

## Result

- `result_class`: `FULL_PAIRED_MASS_DENSITY_SUCCESS`.
- `hard_gap_delta`: `0` for RH.
- `rh_frontier_delta`: `0`.
- `source_analytic_bridge_delta`: `1`.
- `historical_route_coverage_delta`: `1`.
- `theorem_names`: `levinsonMontgomery_real_paired_zero_sum_eq`,
  `exists_upperLeft_zero_abs_im_sub_lt_half_of_pairedMass_neg`, and
  `levinsonMontgomeryDenseBranch_of_pairedMassNegativeAtIntegers`.
- `failure_or_obstacle`: the next source edge is eventual paired-mass negativity from equation
  `(2.1)`, explicit Gamma control, and the low-height certificate. The later indented contour and
  logarithmic count difference remain open.
- `route_selection_decision`: close only this fixed paired-mass density campaign after the
  evidence and final-ledger public gates, then return to value-ranked historical route selection.
- `commit_and_CI`: preregistration `8990be949f0160c593a55bf710714bdaeeef1768`,
  run `30190223668`, job `89762046622`, `1m34s`; frozen implementation
  `0b5b6d5c44cddb680be721c54a6fc9d261e01ba5`, run `30190754950`, job
  `89763478543`, `2m6s`; immutable evidence
  `38071d8a6c085b74bd1f8d258cb6e83cec55d592`, run `30190894736`, job
  `89763862993`, `1m33s`.
