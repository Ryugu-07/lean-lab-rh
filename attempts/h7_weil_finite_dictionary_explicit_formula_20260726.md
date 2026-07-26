# H7 Finite Guinand--Weil Dictionary Explicit Formula

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Selected node: `H7-WEIL-FINITE-DICTIONARY-EXPLICIT-FORMULA-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

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
| `PUBLIC_GATE` | Published preregistration commit `002a775afd9dbfa5d5d2006b531523b6a0e84414`. | Lean Action run `30185492253`, build job `89749281543`, passed. | Open only the fixed production endpoint. |
| `ATTACK_A_ZERO_COUNT` | Applied Mathlib Jensen to order-one `riemannXi` and converted the divisor finsum to a finite norm-ball count. | Lean proves a cofinal height with zero count `O(R^(5/4))`; a finite-set avoidance argument then supplies a long zero-free selected height. | Estimate the logarithmic derivative at that height rather than reuse the coarse generic `O(R^4)` selector. |
| `ATTACK_A_TOP_EDGE` | Combined the long zero-free height with the Hadamard logarithmic derivative expansion and the dictionary's uniform inverse-square strip decay. | The selected top integrand is `O(R^(-1/4))`, so `tendsto_dictionaryXiTopHorizontalIntegral` compiles. | Feed the sharper selector to the generic argument-principle consumer. |
| `ZERO_SIDE` | Reused the compiled divisor summability and selected-height contour theorem. | The right vertical xi integral converges to `pi` times the multiplicity-bearing dictionary zero `tsum`. | Identify the arithmetic decomposition term by term. |
| `PRIME_SIDE` | Proved weak Fourier inversion for the continuous compact dictionary density, justified the von-Mangoldt sum/integral exchange, and used compact support. | The prime integral converges to the exact finite `q in Icc 2 C` source sum and to the existing finite prime matrix quadratic. | Close pole and Gamma terms without imposing global `C^6`. |
| `POLE_SIDE` | Evaluated the pole-pair integral and passed the selected-height interval integral to the full line. | The pole term is exactly `2*g_u(i/2)` after division by `pi`; evenness supplies the sign convention. | Prove the real-place integral and source normalization. |
| `ARCHIMEDEAN_SIDE` | Established Gamma-logarithmic growth against the dictionary's inverse-square decay, then shifted the holomorphic Gamma integrand from `Re(s)=c` to `Re(s)=1/2` with vanishing horizontal sides. | The real-place term is independent of `c>1` and equals one half of the literal source integral `integral h_+(r) g_u(r) dr`. | Assemble the project and source-coordinate formulas. |
| `ASSEMBLY` | Combined the zero, pole, prime, and archimedean limits and divided by the exact `pi` normalization. | Both the mandatory weak-regularity formula and Groskin Theorem 2.5 source normalization compile for every finite real vector. | Register the theorem and run the full mechanical gate. |
| `REGISTRATION` | Added one proven H7 Target, exact mandatory/source/matrix TargetChecks, and six selected transitive axiom prints. | Every selected theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`. | Scan forbidden constructs and build the whole repository. |
| `MECHANICAL_AUDIT` | Compiled the 3,213-line module directly; scanned the implementation and interfaces; ran the full build. | New source is warning-free, the forbidden scan is empty, and `lake build` passes `8762/8762`. | Freeze the implementation and require public Lean Action CI. |
| `PUBLIC_IMPLEMENTATION` | Published frozen implementation commit `f0d76ee081c22381f6ffc208b024268b090fc35c`. | Lean Action run `30187598839`, build job `89754974406`, passed in `2m48s`. | Keep proof source frozen and publish immutable evidence. |

## Mechanical audit

- exact module compilation: `PASS`.
- `Targets.lean`: `PASS`.
- `TargetChecks.lean` exact witness: `PASS`.
- `AxiomsAudit.lean` and printed axioms: `PASS`; selected axioms are
  `propext`, `Classical.choice`, and `Quot.sound`.
- forbidden token/declaration/resource scan: `PASS / EMPTY`.
- witness audit: `NOT_NUMERICAL`.
- definition/source alignment: `PASS`.
- full `lake build`: `PASS / 8762/8762`.

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED / LOCAL_GREEN`.
- `assumption_frontier_after`: unchanged.
- `hard_gap_after`: the finite dictionary now has its exact arithmetic and zero-sum identity.
  Positivity, inverse/density, cutoff limits, H7, and RH remain open.
- `hard_gap_delta`: `0` for RH.
- `source_analytic_bridge_delta`: `1`.
- `historical_route_coverage_delta`: `1`.
- `rh_frontier_delta`: `0`.
- `OBS_node`: the coarse `O(R^4)` selected-height estimate is insufficient for this test, but it
  is bypassed by a compiled Jensen-derived sparse-height selector; it is not a remaining blocker.
- `theorem_names`: `tendsto_dictionaryXiTopHorizontalIntegral`,
  `weilFiniteDictionaryTest_arithmetic_explicit_formula`,
  `compactSymmetrizedXiArchimedeanIntegral_dictionary_eq_source`,
  `tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_neg_pi_mul_primeQuadratic`,
  `weilFiniteDictionary_source_arithmetic_explicit_formula`, and
  `weilFiniteDictionary_primeMatrix_archimedean_zeroSum`.
- `failure_or_obstacle`: Attack A succeeded. Attack B was not started because it was no longer
  necessary. No source normalization mismatch was found.
- `route_selection_decision`: freeze and publish the implementation; after closure return to
  fresh cross-route selection rather than automatically extending H7.
- `model`: `GPT-5 Codex`.
- `reasoning_effort`: `high`.
- `budget`: no numerical quota under V4.1; bounded by the fixed endpoint and local-stop criteria.
- `compaction_state`: inherited context was compacted before preregistration; authoritative state
  was reloaded from governance, HANDOFF, route cards, attempts, and exact Lean APIs.
- `commit_and_CI`: preregistration commit
  `002a775afd9dbfa5d5d2006b531523b6a0e84414` passed public Lean Action run
  `30185492253`, build job `89749281543`. Frozen implementation commit
  `f0d76ee081c22381f6ffc208b024268b090fc35c` passed run `30187598839`, build job
  `89754974406`, in `2m48s`; immutable-evidence CI is pending.
