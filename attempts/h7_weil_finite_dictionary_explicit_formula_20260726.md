# H7 Finite Guinand--Weil Dictionary Explicit Formula

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Selected node: `H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`.
- `node_id`: `H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`.
- `exact_mathematical_statement`: Groskin Theorem 2.5 for the literal project dictionary:
  the cutoff-free finite arithmetic Weil quadratic equals the absolutely convergent,
  multiplicity-bearing sum of the induced test over all nontrivial zeta zeros.
- `proposed_lean_statement`: the fixed project-normalized arithmetic formula in
  `research/h7_weil_finite_dictionary_explicit_formula_prereg_20260726.md`, followed by exact
  zero, pole, prime, archimedean, and finite-source assembly corollaries.
- `relation_to_RH`: `bridge`. It identifies exact finite Weil test values but proves no sign.
- `success_criterion`: unconditional compilation of the full registered endpoint and all
  mechanical/public evidence gates.
- `falsification_criterion`: a compiled normalization mismatch, or an exact demonstration that
  the registered source regularity does not justify a claimed passage.

## Prior state

- `assumption_frontier_before`: no RH or source explicit-formula premise. The literal dictionary
  test is entire, even, of finite exponential type, inverse-square decaying on horizontal
  strips, and absolutely summable on the actual xi divisor.
- `hard_gap_before`: the arithmetic explicit formula is compiled only for globally `C^6`
  compact physical densities; the dictionary density is continuous and piecewise smooth.
- `known_obstacles`: top-edge decay, weak-regularity Gamma/prime limits, all-side convergence for
  smooth approximation, and exact source normalization.
- `nearest_primary_source`: Groskin, arXiv:2607.02828v1, Lemma 2.2 and Theorem 2.5.
- `nearest_project_attempt`: `WeilFiniteDictionarySourceCalculus.lean`,
  `WeilFiniteDictionaryAdmissibility.lean`,
  `WeilCompactLaplaceZeroCutoff.lean`, and
  `WeilCompactLaplaceArithmeticFormula.lean`.
- `new_attack_angle`: attack the full weak-regularity theorem first through the generic
  selected-height contour consumer; if its top edge is genuinely blocked, use source-faithful
  compact `C^6` approximation and prove convergence of every explicit-formula term.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H7 weak-regularity transport with H1 moments, H12 Speiser counts, H11 zero statistics, H2 bow localization, and H10 function-field transfer. | H7 is the largest exact source theorem for which most objects on both sides already compile. It is not a numerical-tail optimization. | Select the full finite dictionary explicit formula. |
| `SOURCE_ALIGNMENT` | Reread arXiv:2607.02828v1, especially Lemma 2.2 and Theorem 2.5, and separated the exact zero-sum dictionary from the later numerical tail-order theorem. | The source endpoint is an exact arithmetic explicit formula with multiplicity and finite prime support; it makes no RH claim. | Lock the literal source formula and its normalization. |
| `API_AUDIT` | Located the generic selected-height zero consumer, the `C^6` arithmetic formula, the dictionary zero-coordinate and summability theorems, and the prime source quadratic. | Differentiability, symmetry, and zero summability already match. The missing direct-contour hypothesis is top-horizontal vanishing. | Register direct contour and smooth approximation as the only two initial attacks. |
| `OBSTACLE_PRECHECK` | Compared the dictionary inverse-square strip decay with the selected-height `O(R^4)` xi logarithmic-derivative bound used by the smooth formula. | The existing estimates do not imply top-edge vanishing; a sharper source theorem or an approximation argument is required. | Do not weaken the endpoint or introduce the explicit formula as a premise. |
| `PREREGISTRATION` | Fixed the complete theorem, source corollaries, attack order, decision criteria, and claim boundary. | Production Lean editing remains closed pending public CI. | Publish this docs-only state and require public Lean Action CI. |

## Mechanical audit

- exact module compilation: `PENDING_PUBLIC_PREREGISTRATION`.
- `Targets.lean`: `CLOSED`.
- `TargetChecks.lean` exact witness: `CLOSED`.
- `AxiomsAudit.lean` and printed axioms: `CLOSED`.
- forbidden token/declaration/resource scan: `PENDING`.
- witness audit: `NOT_NUMERICAL`.
- definition/source alignment: `PREREGISTERED`.
- full `lake build`: `PENDING_PUBLIC_PREREGISTRATION`.

## Result

- `result_class`: `PENDING`.
- `assumption_frontier_after`: unchanged.
- `hard_gap_after`: pending.
- `hard_gap_delta`: pending.
- `OBS_node`: pending.
- `theorem_names`: pending.
- `failure_or_obstacle`: pending direct contour and smooth-approximation attempts.
- `route_selection_decision`: selected; production gate not yet open.
- `model`: `GPT-5 Codex`.
- `reasoning_effort`: `high`.
- `budget`: no numerical quota under V4.1; bounded by the fixed endpoint and local-stop criteria.
- `compaction_state`: inherited context was compacted before preregistration; authoritative state
  was reloaded from governance, HANDOFF, route cards, attempts, and exact Lean APIs.
- `commit_and_CI`: pending docs-only preregistration commit.
