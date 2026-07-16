# M2/G3 Ladder-Frequency Branch Audit

Date: 2026-07-15

- `audit_id`: `AUDIT-20260715-M2-G3-02`
- `node_id`: `M2`
- `gap_id`: `G3`
- `work_class`: `AUDIT/LITERATURE`
- `status`: complete
- `hard_gap_before`: M2/G3 historically unselected (open under V4.1); M0, M1, D, and G4 complete.
- `assumption_frontier_before`: unconditional positive-natural target closure membership remains
  unproved and Lean-equivalent to RH.

## Loop 1: recent-literature screening and source audit

- Re-audited the v2 protocol, clean synchronized worktree, fixed DAG, and the previously falsified
  Wong projection branch before selecting a new candidate.
- Screened recent NB/BD literature for an unconditional explicit approximant or structural
  estimate. Yang's 2026 Friedrichs-angle result does not advertise unconditional target closure;
  its RH-facing angle theorem is conditional on RH.
- Selected Carvill arXiv `2510.18132` because it claims unconditional arbitrary-order decay for a
  smoothed BN ladder and finite-section block compressibility.
- Pinned PDF SHA-256
  `c72c144f3d088032895be0903267757e1618065f034b70d814453cd8b758635f` and visually inspected
  the proof of Theorem 6.1 on pages 8-9.
- The proof converts oscillation frequency to Manhattan ladder distance by asserting
  `|(j'-j)log 2+(k'-k)log 3| >= min(log 2,log 3)*(|j-j'|+|k-k'|)`.
- Registered the first small cancellation test `(0,2)` versus `(3,0)` before any Lean source edit.
- Next obstruction: exact Lean verification of the strict reverse inequality without numerical
  evaluation.
- Provisional classification: `DEPENDENCY_GAP_IDENTIFIED`; M2/G3 was historically unselected (open under V4.1).

## Loop 2: exact ladder-frequency counterexample

- `M2LadderFrequencyAudit.lean` defines the source frequency using integer index differences and
  the source Manhattan distance using exact integer absolute values.
- Lean verifies for `(j,k)=(0,2)` and `(j',k')=(3,0)` that the distance is `5` and the frequency
  is `3*log(2)-2*log(3)`.
- Using only strict monotonicity of `Real.log`, Lean checks
  `3*log(2) < 2*log(3) < 4*log(2)`, from the exact integer comparisons `8<9<16`.
- It follows in Lean that
  `|3*log(2)-2*log(3)| < min(log(2),log(3))*5`, and therefore the displayed source lower bound is
  false at this admissible pair.
- This is the step that converts the integration-by-parts denominator `|lambda|^m` into decay in
  Manhattan distance. The claimed Theorem 6.1 distance envelope, row-tail summability, and
  finite-section estimate do not follow from the published proof.
- This audit does not assert that every possible decay theorem for the system is false. It rejects
  the source's current proof route and supplies no bridge from its smoothed family to unconditional
  target closure membership.
- Exact TargetChecks integration and transitive axiom audit pass. The endpoint depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- The 8617-job full build and `git diff --check` pass. Forbidden Lean token, declaration, and
  resource-relaxation scans are empty.
- Implementation commit `ff0f14f10e75d73424addb671b3da34f0c44c679` passed public Lean Action
  CI run `29384172003`, build job `87253877106`, in 2m34s.
- `hard_gap_after`: M2/G3 was historically unselected (open under V4.1); M0, M1, D, and G4 remain complete.
- `hard_gap_delta`: zero.
- `assumption_frontier_after`: unconditional membership of `baezDuarteComplexTargetL2` in
  `baezDuarteComplexKernelClosure` remains unproved and Lean-equivalent to RH.
- Final classification: `BRANCH_FALSIFIED`.
