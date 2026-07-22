# H12 Speiser Counting-Equivalence Attempt

Campaign: `LITERATURE-20260723-H12-SPEISER-COUNTING-EQUIVALENCE-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

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

## Assumption and gap accounting

- `assumption_frontier_before`: no project-local derivative-zero divisor or Speiser localizer.
- `hard_gap_before`: prove the source boundary sign and argument-principle count without assuming
  RH or derivative zero-freeness.
- `rh_frontier_before`: RH open.
- `current_result`: `PREREGISTERED_ONLY`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `next_gate`: preregistration commit and public CI.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
