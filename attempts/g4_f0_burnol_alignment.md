# G4-F0 Burnol Continuous/Natural Alignment

Date: 2026-07-13

- `batch_id`: `BATCH-20260713-G4-F0`
- `node_id`: `B1`
- `gap_id`: `G4/F0`
- `work_class`: `FORMALIZATION`
- `result_class`: `FORMALIZATION_ONLY`
- `assumption_frontier_before`: Burnol's continuous `B_lambda`, the project's finite natural
  `V_N`, and their distance relation were source-audited but absent from Lean.
- `assumption_frontier_after`: no mathematical assumption was added; Lean now checks the exact
  continuous/natural inclusion, reversed distance inequality, and right-sided parameter limit.
- `hard_gap_before`: F0 open; F1-F5 open; M2/G3 unchanged.
- `hard_gap_after`: F0 complete; F1 is the next source-level edge; F2-F5 and M2/G3 unchanged.
- `hard_gap_delta`: alignment edge F0 closed, with no claim of RH research progress.
- `theorem_names_added`:
  `burnolContinuousKernelL2_ofNatural`,
  `baezDuarteFiniteComplexKernelSpan_le_burnolKernelSpan`,
  `burnolDistance_inv_natCast_le_baezDuarteNaturalDistance`,
  `tendsto_natCast_inv_nhdsWithin_Ioi_zero`.
- `Lean_verification`: exact witnesses in `TargetChecks.lean`; full `lake build` succeeded with
  8609 jobs.
- `axiom_audit`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `sorry_admit_audit`: no `sorry`, `admit`, or `sorryAx` in Lean sources; no project `axiom` or
  `constant` declarations.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `budget`: unbounded persistent-goal budget
- `compaction_state`: automatic compaction occurred immediately before this implementation batch;
  execution resumed from the retained handoff summary without changing the preregistered target.
- `commit_SHA`: pending
- `public_CI`: pending

## Outcome

For every positive natural `N`, each reciprocal-natural kernel indexed by `n <= N` is literally a
member of Burnol's continuous family at cutoff `1/N`. Span monotonicity gives
`V_N <= B_(1/N)`, and `infDist` monotonicity gives `D(1/N) <= d_N`. The filter statement
`1/N -> 0+` records the parameter transport needed by the future liminf argument.

No Burnol lower bound, unitary model, zero vector, asymptotic pairing, or finite-zero liminf theorem
is proved here. The next batch must work on F1 as one source-level edge.
