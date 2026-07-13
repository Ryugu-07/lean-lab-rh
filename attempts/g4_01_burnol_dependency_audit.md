# G4-01 Burnol Dependency Audit

Date: 2026-07-13

- `loop_id`: `AUDIT-20260713-G4-01`
- `node_id`: `B1`
- `work_class`: `LITERATURE`
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `assumption_frontier_before`: Burnol's `d_N^2 >= C/log N` direction was only an external review
  suggestion; the continuous parameter space, inclusion direction, zero multiplicity, and proof
  dependencies had not been aligned with the project.
- `assumption_frontier_after`: Burnol's continuous `B_lambda` and the finite natural `V_N` are
  distinguished; the valid inclusion is `V_N <= B_(1/N)` and the source proof is fixed as F0-F5.
- `hard_gap_before`: broad planned G4 lower-bound theorem.
- `hard_gap_after`: G4 open with exact source-level frontier F0-F5.
- `hard_gap_delta`: dependency boundary identified; M2/G3 unchanged.
- `Lean_verification`: no Lean theorem was added in this literature loop.
- `theorem_names_added`: none.
- `nearest_known_literature`: Burnol, arXiv `math/0103058v2`; Baez-Duarte-Balazard-Landreau-Saias,
  Advances in Mathematics 149 (2000), DOI `10.1006/aima.1999.1861`.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `budget`: unbounded persistent-goal budget
- `compaction_state`: no compaction since the immediately preceding governance batch.
- `commit_SHA`: `a88bb53`

## Route Decision

The direct claim "the project already has Burnol's `D(lambda)`" was rejected. Its current closure
uses only reciprocal positive-natural parameters, while Burnol's primary distance uses every real
`theta` in `[lambda,1]`. The natural consequence survives because distance reverses the correct
subspace inclusion.

The next batch must implement all F0 definitions and transfer facts together. Those facts are
statement alignment and will be classified `FORMALIZATION_ONLY`; they are not a substitute for the
Burnol vectors or the finite-zero lower bound.
