# H12 Levinson--Montgomery Paired-Mass Density

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-PAIRED-MASS-DENSITY-01`

Selected node: `H12-LM-PAIRED-MASS-DENSITY-01`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT`.
- `exact_mathematical_statement`: reconstruct Levinson--Montgomery equations `(2.2)`--`(2.3)`
  over the actual multiplicity-bearing zeta zero divisor, prove negative paired mass localizes a
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

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: inherited compacted context was reloaded from governance, HANDOFF, active
  memory, Targets, the prior H12 attempt, the hard-gap DAG, live repository state, and the
  rendered primary source before selection.
- `global_goal`: active.

## Mechanical audit

- exact module compilation: `PENDING_PUBLIC_PREREGISTRATION`.
- `Targets.lean`: `CLOSED`.
- `TargetChecks.lean`: `CLOSED`.
- `AxiomsAudit.lean`: `CLOSED`.
- forbidden scan: `PENDING`.
- witness audit: `PENDING_ACTUAL_ZERO_DIVISOR`.
- definition/source alignment: `PREREGISTERED`.
- full `lake build`: `PENDING_PUBLIC_PREREGISTRATION`.

## Result

- `result_class`: `PENDING`.
- `hard_gap_delta`: pending.
- `rh_frontier_delta`: pending.
- `theorem_names`: pending.
- `failure_or_obstacle`: pending Attack A and fallback B.
- `route_selection_decision`: selected; production proof editing remains closed until public
  preregistration CI.
- `commit_and_CI`: pending docs-only preregistration commit.
