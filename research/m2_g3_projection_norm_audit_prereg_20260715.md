# M2/G3 Projection-Norm Branch Audit Pre-Registration

Date: 2026-07-15

Audit ID: `AUDIT-20260715-M2-G3-01`

## Fixed-Gap Entry

- `node_id`: `M2`
- `gap_id`: `G3`
- `work_class`: `AUDIT/LITERATURE`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete
- `hard_gap_before`: M2/G3 parked; M0, M1, D, and G4 complete.
- `assumption_frontier_before`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`.
- `expected_hard_gap_delta`: zero unless a cited unconditional proof branch survives exact
  verification. A checked counterexample may eliminate that branch but does not unpark M2/G3.

## Candidate Source

Kwok Kwan Wong, *Inequality and Nyman-Beurling-Baez-Duarte criteria*, arXiv
`2310.03972v5`. Inspected TeX source SHA-256:
`b0c482006baa8b1c7835b919805340d6fdb7d3a9d73c57edf66f424f070f03f8`.

The source claims RH and uses finite-dimensional Euclidean orthogonal projections `P_n` as
operators on `c_0` and `l-infinity`. At TeX lines 142-149 and 159-177 it invokes

```text
norm_infinity(P_n) <= norm_2(P_n) = 1
```

to obtain the uniform operator bound needed for strong convergence. This is not a valid generic
comparison of induced norms: Euclidean orthogonal projections need not be contractions for the
coordinate maximum norm.

## Exact Lean Audit Endpoint

Construct the real matrix

```text
P = (1/5) * [[4, 2], [2, 1]].
```

The audit must Lean-check all of the following in one module:

1. `P.transpose = P`;
2. `P * P = P`;
3. for `x = (1,1)`, the coordinate maximum norm of `x` is `1`;
4. the coordinate maximum norm of `P*x` is `6/5`;
5. therefore `not (forall x, maxNorm (P*x) <= maxNorm x)`.

Symmetry and idempotence identify `P` as a Euclidean orthogonal-projection matrix, while the last
three facts refute the generic maximum-norm contraction used in the source.

## Admission And Scope

- This is admitted because it tests a published unconditional RH-proof branch at a decisive
  theorem boundary; it is not a wrapper around project predicates.
- The audit does not claim that the special matrices `P_n` from the paper necessarily violate a
  uniform maximum-norm bound. It shows that orthogonal projection and Euclidean norm one do not
  supply that bound.
- Repair would require a separate proof of a uniform maximum-norm bound for the special `P_n`,
  together with well-defined common-domain extensions and the asserted compatibility on finitely
  supported vectors. None may be assumed.
- No new M2 successor node or conjectural Lean theorem may be created in this batch.
- No `sorry`, `admit`, project `axiom`, unchecked `constant`, `opaque` premise, `native_decide`, or
  resource-limit relaxation is permitted.

## Source-Specific Extension Registered Before Edit

The generic endpoint compiled during the audit, after which the source definition was evaluated
at its first nontrivial case `n=3`. Here `L_3=lcm(1,2,3)=6`, and TeX lines 65-70 give

```text
A_3 = [[1,1], [0,2], [1,0], [0,1], [1,2]].
```

Register the following stronger checks in the same indivisible audit batch:

```text
G_3 = A_3.transpose * A_3 = [[3,3],[3,10]],
G_3^(-1) = (1/21) * [[10,-3],[-3,3]],
P_3 = A_3 * G_3^(-1) * A_3.transpose.
```

Lean must verify both inverse products, symmetry and idempotence of `P_3`, and for
`x=(1,1,-1,1,1)` the exact coordinate maximum norms

```text
maxNorm(x)=1,    maxNorm(P_3*x)=10/7.
```

This directly tests the source's special projection family rather than merely refuting a generic
norm comparison. It is batched here because it uses the same branch, source claim, and fixed
endpoint; no new target is created.

## Literature Boundary

- Balazard and de Roton, arXiv `0812.1689`, improve the distance upper bound only under RH.
- Bettin, Conrey, and Farmer, arXiv `1211.5191`, obtain the conjectured optimal constant only under
  RH plus a mean bound for reciprocal zeta derivatives, implicitly requiring simple zeros.
- Alvarez Cruz and Alvarez Gutierrez, arXiv `2606.22562`, give new damped/Colombeau formulations
  that remain equivalences with RH, not unconditional convergence.
- GitHub code search on 2026-07-15 found no public Lean source containing `Nyman-Beurling`,
  `BaezDuarte`, or `fractionalPartKernel`; Isabelle AFP has zeta and PNT infrastructure but no
  Nyman-Beurling/Baez-Duarte criterion entry located by the audit.

## Result Rules

- `BRANCH_FALSIFIED`: the symmetric-idempotent counterexample and exact max-norm growth compile.
- `DEPENDENCY_GAP_IDENTIFIED`: the counterexample cannot be completed, but the special-matrix
  uniform-bound dependency is isolated without assuming it.
- `NO_PROGRESS`: only unrelated matrix identities compile.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; fixed DAG re-audited before admission

## Audit Result

Lean checks every registered generic and source-specific endpoint in
`LeanLab/Riemann/M2ProjectionNormAudit.lean`. For the source's exact `n=3` data it proves

```text
A_3.transpose * A_3 = [[3,3],[3,10]],
((1/21)*[[10,-3],[-3,3]]) * (A_3.transpose * A_3) = I,
(A_3.transpose * A_3) * ((1/21)*[[10,-3],[-3,3]]) = I,
P_3.transpose = P_3,
P_3 * P_3 = P_3,
P_3 * (1,1,-1,1,1) = (1/3,10/7,-8/21,5/7,22/21).
```

Consequently the input maximum norm is `1` while the output maximum norm is `10/7`. The source's
claimed bound `norm_infinity(P_n) <= norm_2(P_n) = 1` is therefore false for its own projection
family at `n=3`, not merely unsupported by the generic norm comparison.

- `result`: `BRANCH_FALSIFIED`
- `hard_gap_after`: M2/G3 remains parked; M0, M1, D, and G4 remain complete.
- `hard_gap_delta`: zero.
- `assumption_frontier_after`: no unconditional proof that
  `baezDuarteComplexTargetL2` belongs to `baezDuarteComplexKernelClosure`.
- `governance_decision`: do not reopen M2/G3 and do not create a successor edge from this source.
- `local_verification`: exact target checks, standard-only axiom audit, empty forbidden scans,
  `git diff --check`, and the 8616-job full build pass.
- `public_verification`: implementation commit
  `b4894f0cb9903b5fa14c766e30bdb10c3bdeaeb4` passed Lean Action CI run `29383306167`, build job
  `87251333374`, in 2m3s.

This result invalidates the audited proof route, not RH. A possible larger uniform bound for all
special `P_n` is not ruled out by the `n=3` example, but the source neither obtains such a bound
from Euclidean orthogonality nor supplies the additional common-domain and convergence argument
that a repair would require.
