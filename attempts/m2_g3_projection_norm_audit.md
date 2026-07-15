# M2/G3 Projection-Norm Branch Audit

Date: 2026-07-15

- `audit_id`: `AUDIT-20260715-M2-G3-01`
- `node_id`: `M2`
- `gap_id`: `G3`
- `work_class`: `AUDIT/LITERATURE`
- `status`: complete
- `hard_gap_before`: M2/G3 parked; M0, M1, D, and G4 complete.
- `assumption_frontier_before`: unconditional positive-natural target closure membership remains
  unproved and Lean-equivalent to RH.

## Loop 1: fixed-DAG and literature audit

- Re-read the v2 loop protocol, review, current DAG, HANDOFF, and exact compiled Baez-Duarte
  criterion before selecting any target.
- Balazard-de Roton and Bettin-Conrey-Farmer provide only conditional upper bounds. The 2026
  Colombeau-Beurling paper supplies another RH equivalence, not an unconditional approximant.
- Cross-system search found no existing Lean NB/BD formalization and no Isabelle AFP NB/BD
  criterion entry; this does not by itself establish mathematical novelty.
- Inspected Wong arXiv `2310.03972v5` from pinned TeX source. Its strong-convergence argument uses
  `norm_infinity(P_n) <= norm_2(P_n) = 1` for Euclidean orthogonal projections.
- Selected exact audit test: a two-dimensional symmetric idempotent projection that increases the
  coordinate maximum norm from `1` to `6/5`.
- Next obstruction: compile all projection and norm facts in one Lean module, then decide only
  whether this proof branch is falsified.
- Provisional classification: `DEPENDENCY_GAP_IDENTIFIED`; M2/G3 remains parked.

## Loop 2: generic projection counterexample

- Lean verifies that `(1/5)*[[4,2],[2,1]]` is symmetric and idempotent.
- On the vector `(1,1)`, its coordinate maximum norm grows exactly from `1` to `6/5`.
- `exists_symmetric_idempotent_not_maxNorm_nonexpansive` therefore refutes the generic inference
  from Euclidean orthogonal projection to maximum-norm contraction.
- Exact TargetChecks integration and axiom audit pass; the final endpoint depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Stronger source-specific finding: evaluating the paper's own remainder matrix at `n=3` gives a
  Euclidean projection with candidate maximum-norm growth `10/7`; this extension was registered
  before its Lean source edit.
- Next obstruction: verify the exact `A_3`, Gram inverse, `P_3`, and test-vector calculation.
- Provisional classification: `BRANCH_FALSIFIED`; M2/G3 remains parked.

## Loop 3: source-specific `n = 3` counterexample

- Lean verifies the paper's exact first nontrivial remainder matrix
  `A_3 = [[1,1],[0,2],[1,0],[0,1],[1,2]]` and Gram matrix
  `A_3.transpose * A_3 = [[3,3],[3,10]]`.
- Lean verifies both products with the registered inverse
  `(1/21) * [[10,-3],[-3,3]]`, and then verifies that
  `P_3 = A_3 * (A_3.transpose * A_3)^(-1) * A_3.transpose` is symmetric and idempotent.
- The initial 25-coordinate idempotence expansion produced only syntactic high-index vector
  goals. Replacing it with matrix associativity plus the checked Gram inverse closed the proof
  without changing the endpoint or adding assumptions.
- For `x = (1,1,-1,1,1)`, Lean computes
  `P_3*x = (1/3,10/7,-8/21,5/7,22/21)`, hence
  `maxNorm(x)=1` and `maxNorm(P_3*x)=10/7`.
- `not_m2AuditWongPThree_maxNorm_nonexpansive` directly refutes the source's asserted
  maximum-norm contraction for its own special family, already at `n=3`.
- Exact TargetChecks integration and transitive axiom audit pass. The endpoint depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- The 8616-job full build and `git diff --check` pass. Forbidden Lean token, declaration, and
  resource-relaxation scans are empty.
- `hard_gap_after`: M2/G3 remains parked; M0, M1, D, and G4 remain complete.
- `hard_gap_delta`: zero. This rejects a proposed proof branch but does not prove unconditional
  closure membership.
- `assumption_frontier_after`: unconditional membership of `baezDuarteComplexTargetL2` in
  `baezDuarteComplexKernelClosure` remains unproved and Lean-equivalent to RH.
- Final classification: `BRANCH_FALSIFIED`.
