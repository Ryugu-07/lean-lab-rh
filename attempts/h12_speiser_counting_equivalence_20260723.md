# H12 Speiser Counting-Equivalence Attempt

Campaign: `LITERATURE-20260723-H12-SPEISER-COUNTING-EQUIVALENCE-01`

Mode: `LITERATURE`

Status: `MEANINGFUL_PARTIAL / PUBLICLY_CLOSED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: inherited-summary recovery occurred in the preceding H9 campaign; canonical
  files were re-read before route selection.
- `global_goal`: active.

## Baseline

- `parent_commit`: `418a1b3e469a0a71e67ba39ac22eb0dd974d37f3`.
- `parent_public_ci`: run `29940746044`, build job `88993661951`, passed in `1m30s`.
- `selected_node`: `H12-SPEISER-LEVINSON-MONTGOMERY-COUNT-01`.
- `preregistration`: `research/h12_speiser_counting_equivalence_prereg_20260723.md`.
- `primary_sources`: Speiser 1935 and Levinson-Montgomery 1974.

## Preregistered endpoint

Compile the exact upper-left derivative-zero-free condition and prove it equivalent to
`Mathlib.RiemannHypothesis`, with multiplicity, open-strip boundaries, and indented-contour logic
aligned to the rigorous Levinson-Montgomery count proof. No source theorem may be inserted as an
unproved Lean premise.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | H9 reached its exact local stop. H11 has no real-part information, H10 lacks a number-field trace object, and H1/H2 lack a one-exception localizer. | Select H12 Speiser because its derivative-zero condition addresses exactly that cross-route gap. |
| 2 | `SOURCE_AUDIT` | EuDML fixes the journal record at 1935. The original level-curve proof has acknowledged rigor gaps; Levinson-Montgomery Theorem 1 gives a rigorous stronger count theorem and the Speiser corollary. | Use the 1974 count proof as the mathematical spine; retain the 1935 geometry only as historical motivation. |
| 3 | `LOGICAL_HINGE_AUDIT` | `N'_-(T)=N_-(T)+O(log T)` still permits finitely many exceptions. The decisive source statement is exact equality on an unbounded sequence of heights. | Make the exact natural-number count consumer an explicit Lean endpoint, then attack the analytic boundary theorem that supplies the sequence. |
| 4 | `PREREGISTRATION_CI` | Preregistration commit `178d86eaa7d02d8eb88421171bee8964c722fb0e` passed Lean Action run `29941747166`, build job `88997067033`, in `1m33s`. | Open the proof-source gate. |
| 5 | `DIVISOR_AND_FINITE_COUNTS` | Built the analytic `zeta'` divisor on `{1}ᶜ`, proved finite analytic order, support/zero correspondence, bounded-rectangle finiteness, and actual multiplicity-bearing zeta and derivative counts. | Use actual counts rather than an abstract natural-number surrogate. |
| 6 | `EXACT_COUNT_CONSUMER` | Lean proves that an unbounded exact-equality sequence transfers zero-freeness in either direction: zeta count zero forces derivative zero-freeness, and derivative count zero forces zeta zero-freeness. | Keep exact equality as the discrete last-exception localizer. |
| 7 | `REAL_AXIS_CROSS_ROUTE` | Existing H6 theorem `deBruijnNewmanH_mul_I_re_pos` and the exact `H_0`--xi coordinate prove that no nontrivial zeta zero lies on the real axis. | Discharge the positive-height/full-RH alignment internally instead of adding an external premise. |
| 8 | `SOURCE_LOGIC_CORRECTION` | The source does not provide an unconditional exact sequence. It provides an exact-or-eventually-`N_-(T)>T/2` dichotomy together with `O(log T)` count difference. | Define both source outputs separately; prove `O(log T)` implies the needed `o(T)` estimate and that the incompatible branch is eliminated under either zero-free condition. |
| 9 | `CONDITIONAL_EQUIVALENCE` | `riemannHypothesis_iff_speiserDerivativeZeroFree_of_levinsonMontgomeryTheoremOne` compiles from the literal logarithmic bound and count dichotomy. | Register it as a conditional source consumer, not as completion of Speiser's theorem. |
| 10 | `MECHANICAL_AUDIT` | Five exact TargetChecks pass; five selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden scan and `git diff --check` are clean; full `lake build` passes 8,742 jobs. | Stop locally at the first exact external analytic obstruction and require implementation CI. |
| 11 | `IMPLEMENTATION_CI` | Implementation commit `2a6290a27fd7675db409f884679d1a554c13b72d` passed Lean Action run `29943873685`, build job `89004249306`, in `2m6s`. | Freeze all Lean proof source. Publish immutable implementation evidence and require its own public CI. |
| 12 | `EVIDENCE_CI` | Evidence commit `eeca9f7fc910b323df7aaaec00f3258c92063483` passed Lean Action run `29944285692`, build job `89005620974`, in `1m33s`. | Record the local stop in the final ledger, require its public CI, then return the persistent RH Goal to fresh historical-route selection. |
| 13 | `FINAL_LEDGER_CI` | Final-ledger commit `100bc02d691b6a69cf2ca903f8a0aa9f6c99dca1` passed Lean Action run `29944572919`, build job `89006584781`, in `2m26s`. | Campaign publicly closed. Select H11 pair-correlation horizontal multiplicity after finding a post-atlas source correction. |

## Compiled declarations

- `analyticOnNhd_deriv_riemannZeta`
- `riemannZetaDerivDivisor_apply`
- `mem_support_riemannZetaDerivDivisor_iff`
- `finite_speiserUpperLeftZetaZeroSet`
- `finite_speiserUpperLeftDerivZeroSet`
- `speiserUpperLeftZetaZeroCount_pos_of_zero`
- `speiserUpperLeftDerivZeroCount_pos_of_zero`
- `criticalStripRealAxisZeroFree`
- `riemannHypothesis_iff_speiserZetaZeroFree`
- `levinsonMontgomeryCountDifferenceSublinear_of_logCountBound`
- `levinsonMontgomeryExactCountSequence_of_zetaCount_eq_zero`
- `levinsonMontgomeryExactCountSequence_of_derivCount_eq_zero`
- `riemannHypothesis_iff_speiserDerivativeZeroFree_of_levinsonMontgomeryTheoremOne`

## Assumption and gap accounting

- `assumption_frontier_before`: no project-local derivative-zero divisor or Speiser localizer.
- `hard_gap_before`: prove the source boundary sign and argument-principle count without assuming
  RH or derivative zero-freeness.
- `rh_frontier_before`: RH open.
- `current_result`: `PROVED / ROUTE_INFRASTRUCTURE / CONDITIONAL_SOURCE_CONSUMER`.
- `full_campaign_success`: `NO`; neither analytic source output is proved.
- `first_external_analytic_obstruction`: prove both `LevinsonMontgomeryLogCountBound` and
  `LevinsonMontgomeryCountDichotomy` for the actual counts. This requires a meromorphic
  indented-rectangle argument principle, functional-equation logarithmic-derivative zero sum,
  Gamma estimates, top-boundary selection, and low-height sign control.
- `api_inventory`: mathlib has analytic derivatives, locally finite divisors, Jensen's formula,
  and complex integration. The project has a specialized entire-xi rectangle argument principle
  derived from its Hadamard expansion. No generic meromorphic indented-rectangle argument
  principle or Levinson-Montgomery boundary theorem was found.
- `hard_gap_delta`: `0`; the source analytic theorem remains open.
- `rh_frontier_delta`: `0`.
- `route_infrastructure_delta`: `1`.
- `cross_route_reuse_delta`: `1` from H6 imaginary-axis positivity.
- `implementation_commit`: `2a6290a27fd7675db409f884679d1a554c13b72d`.
- `implementation_public_ci`: Lean Action run `29943873685`, build job `89004249306`, passed in
  `2m6s`.
- `proof_source_state`: frozen at the implementation commit.
- `evidence_commit`: `eeca9f7fc910b323df7aaaec00f3258c92063483`.
- `evidence_public_ci`: Lean Action run `29944285692`, build job `89005620974`, passed in `1m33s`.
- `local_stop`: reached at the conditional count consumer; H12-D and H12-E remain open and may be
  resumed when their analytic prerequisites outrank other historical-route audits.
- `final_ledger_commit`: `100bc02d691b6a69cf2ca903f8a0aa9f6c99dca1`.
- `final_ledger_public_ci`: Lean Action run `29944572919`, build job `89006584781`, passed in
  `2m26s`.
- `next_gate`: complete; successor campaign is H11 pair-correlation horizontal multiplicity.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
