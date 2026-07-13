# G4-F1-01 Unitary Model Audit

Date: 2026-07-13

- `batch_id`: `AUDIT-20260713-G4-F1-01`
- `node_id`: `B1`
- `gap_id`: `G4/F1`
- `work_class`: `LITERATURE_AND_DEPENDENCY_AUDIT`
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `assumption_frontier_before`: Burnol's statement that `D(lambda)` is the distance from `chi1`
  to `C_lambda` had not been expanded into its operator, sign, or dilation normalization.
- `assumption_frontier_after`: `T=(1-M)^-1`, multiplier `(s-1)/s`, identities
  `T chi=chi1` and `T rho(1/t)=-A`, and all dilation scalars are fixed; the missing explicit `A`
  proposition is isolated as F1a.
- `hard_gap_before`: G4/F1 open and undivided.
- `hard_gap_after`: G4/F1a and F1b open, with F1a selected next; F2-F5 and M2/G3 unchanged.
- `hard_gap_delta`: exact source dependency boundary identified; no theorem formalized.
- `Lean_verification`: no Lean theorem was added in this audit loop.
- `anti_tautology_check`: an image-defined `C_lambda` was rejected as insufficient for F2.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `budget`: unbounded persistent-goal budget
- `compaction_state`: no compaction since G4/F0 completed.
- `commit_SHA`: pending
- `public_CI`: pending

## Route Decision

Proceed through the explicit source function `A`, not through a generic image-space wrapper. The
next implementation batch must prove support, `L2` membership, and the Mellin formula together.
Only then may the spectral multiplier and distance equality be assembled as F1b.

