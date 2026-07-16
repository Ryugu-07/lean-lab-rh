# M2/G3 Automatic-Loop Stop Audit

Date: 2026-07-15

Current note: this is a historical local decision. V4.1 abolishes the numerical stop condition;
M2/G3 is open, and a materially new preregistered attack may re-enter it.

- `audit_id`: `AUDIT-20260715-M2-G3-03`
- `node_id`: `M2`
- `gap_id`: `G3`
- `work_class`: `AUDIT/LITERATURE`
- `status`: complete
- `hard_gap_before`: M2/G3 historically unselected (open under V4.1); M0, M1, D, and G4 complete.
- `assumption_frontier_before`: unconditional positive-natural target closure membership remains
  unproved and Lean-equivalent to RH.

## Loop 1: remaining-candidate and stop audit

- Rechecked the clean synchronized worktree, fixed M2/G3 frontier, prior Wong and Carvill audit
  results, and the v2 three-zero-delta stop condition.
- Iyer's residual-dynamics paper explicitly leaves residual covariance/weighted Hilbert residual
  decay as an open problem and identifies it with the known RH-equivalent approximation bridge.
- Alvarez Cruz-Alvarez Gutierrez prove a Colombeau criterion equivalence: the forward net bounds
  assume RH and the converse recovers RH.
- Bhattacharjee et al. explicitly disclaim an RH proof. Their rank-one collapse concerns
  `{x/k}` rather than the source-aligned `{1/(k*x)}` carrier, and their sawtooth replacement is a
  different family.
- The remaining dyadic project is explicitly conditional and numerical; it cannot satisfy G3's
  unconditional convergence requirement.
- No exact unconditional estimate survived admission, so no Lean target or source edit was
  created.
- `hard_gap_after`: M2/G3 was historically unselected (open under V4.1); M0, M1, D, and G4 remain complete.
- `hard_gap_delta`: zero.
- `assumption_frontier_after`: unconditional positive-natural target closure membership remains
  unproved and Lean-equivalent to RH.
- `Lean_verification`: not applicable; no mathematical proposition was admitted.
- `theorem_names_added`: none.
- `repository_verification`: `git diff --check` and the unchanged 8617-job project build pass.
- Governance commit `6bdbd1f9a459edb1b0baa7d3568b44605f0d4fc6` passed public Lean Action CI
  run `29384810340`, build job `87255750317`, in 1m24s.
- Final classification: `NO_PROGRESS`.
- Historical audit decision: `STOP` under v2 after three zero-delta loops with the same assumption
  frontier. This numerical trigger has no current force.
