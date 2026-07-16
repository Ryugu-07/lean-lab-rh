# Sparse Baez-Duarte Target Obstruction Campaign

Campaign: `CAMPAIGN-20260715-SPARSE-OBSTRUCTION-01`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget; campaign capped by Discovery Protocol V3
- `compaction_since_previous_campaign`: no

## Route Selection

- Entered `ROUTE_SELECTION` after publishing the exact sparse lower-frame campaign.
- Did not optimize the frame constant or add generic Gram wrappers.
- Admitted one precise target-coupling falsification mechanism based on a local orthogonal witness.
- The complete candidate and literature audit is in
  `research/m2_sparse_target_obstruction_prereg_20260715.md`.

## Exact Pre-Proof Data

- sparse base: `Q = 2^24`
- intervals: `(1/2,2/3]`, `(1/3,2/5]`, `(1/4,2/7]`
- coefficients: `118`, `-925`, `1176`
- tail-kernel moment: exactly zero
- base-kernel floor moment: exactly zero
- target moment: exactly `1/9`
- numerical premise: none

## Frontier Before Proof

- `hard_gap_before`: M2/G3 historically unselected (open under V4.1)
- `assumption_frontier_before`: unchanged
- `expected_result`: `BRANCH_ELIMINATED` or `NO_PROGRESS`
- `expected_hard_gap_delta`: zero
- `novelty`: `NOVELTY_UNCHECKED`

## Next Proof Attempt

One indivisible Lean batch may define the compactly supported witness, prove its exact three local
moments, lift it to complex `L2(0,infinity)`, prove orthogonality to every normalized sparse kernel,
and exclude the exact target from the sparse closed span. Partial integration helpers do not count
as separate research progress.

## Proof Attempt Result

- `result`: `BRANCH_ELIMINATED`
- `proof_file`: `LeanLab/Riemann/M2SparseObstruction.lean`
- `selected_candidate`: C1
- `candidate_statement_changed`: no
- `numerical_premise_used`: no
- `sorry_or_unchecked_declaration_used`: no

Lean verifies one explicit complex `L2` witness with pairing zero against every normalized sparse
kernel and pairing `1/9` against `baezDuarteComplexTargetL2`. Orthogonal-complement closure then
gives the exact theorem

```lean
baezDuarteComplexTargetL2 ∉ sparseGramKernelClosure
```

The pre-proof rejections are also Lean-checked: the one-cell identity is exact, and the selected
two-piece moment determinant is `1/600`, so neither screening conclusion remains informal.

## Progress Accounting

- `activity_result`: `LEAN_PROOF_ATTEMPT_COMPLETE`
- `research_progress`: exact sparse target-coupling branch eliminated
- `hard_gap_after`: M2/G3 was historically unselected (open under V4.1)
- `hard_gap_delta`: zero
- `assumption_frontier_after`: unchanged
- `novelty_after`: `NOVELTY_UNCHECKED`
- `next_state`: `ROUTE_SELECTION`

The preceding sparse lower-frame bound remains a valid auxiliary theorem, but it cannot be paired
with target membership for this family. Do not revisit the `(2^24)^j` family without a genuinely
different mathematical endpoint.

## Verification

- standalone Lean compilation and Lake module build: passed
- exact `TargetChecks.lean`: passed
- transitive axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- full `lake build`: passed with 8619 jobs
- forbidden placeholder, explicit declaration, `native_decide`, and resource-relaxation scans:
  empty
- `git diff --check`: passed
- implementation commit: `c2e6f086b30fc54b5e0ed6ab2782bf5ef9283a85`, pushed to public `main`
- Lean Action CI: run `29391437206`, build job `87275634635`, succeeded
