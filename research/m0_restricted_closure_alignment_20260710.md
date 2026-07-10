# M0 Restricted Closure Alignment

Date: 2026-07-10

Batch ID: `BATCH-20260710-M0-02`

## Fixed-Gap Result

- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `assumption_frontier_before`: the project had only a one-way implication from restricted density
  to its local integral-tolerance predicate.
- `hard_gap_before`: the closure/tolerance relation was not exact, and the project-local restricted
  statement had not been checked against the coefficient constraint in the original criterion.

## Primary Sources

1. A. Beurling, *A Closure Problem Related to the Riemann Zeta-Function*, PNAS 41 (1955),
   312-314, <https://doi.org/10.1073/pnas.41.5.312>.
   Beurling's linear manifold consists of finite sums of `rho(theta / x)` with
   `0 < theta < 1` and the additional condition `sum c_k * theta_k = 0`.
2. M. Balazard and E. Saias, *The Nyman-Beurling Equivalent Form for the Riemann Hypothesis*,
   Expo. Math. 18 (2000), 131-138,
   <https://www.esi.ac.at/preprints/esi623.pdf>.
   Their unit-interval generators are the modified functions
   `rho(theta / t) - theta * rho(1 / t)`, which encode the same zero-moment condition.
3. L. Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
   Rend. Mat. Acc. Lincei 14 (2003), 5-11,
   <https://arxiv.org/abs/math/0202141>.
   Its strong theorem works in `L2(0,infinity)` with target `chi_(0,1]` and raw generators
   `rho(1 / (n*x))` for positive natural `n`.

## Lean-Checked Internal Alignment

The project now proves the exact local equivalence

```lean
unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure ↔
  nymanBeurlingRestrictedConcreteApprox
```

as `unitIntervalOneL2_mem_restrictedClosure_iff_concreteApprox`.

This closes the project-internal closure-versus-positive-tolerance mismatch. It does not turn that
closure into the published Beurling space, because the project span has no zero-moment condition.

## Lean-Checked Tail Identity

For a finite coefficient family supported in `0 < a` and `a <= 1`, Lean proves that for `1 < x`,

```text
sum c(a) * rho(a/x) = (sum c(a) * a) / x.
```

The theorem is `restricted_finsupp_sum_eq_moment_div_of_one_lt`. Lean also evaluates the entire
omitted tail:

```lean
integral over (1,infinity) of (sum c(a) * rho(a/x))^2
  = (sum c(a) * a)^2
```

as `restricted_finsupp_tail_error_eq_moment_sq`.

Therefore restricting the norm from `(0,infinity)` to `(0,1)` deletes exactly the squared
coefficient-parameter moment. In the original unit-interval criterion this quantity is forced to
zero; in the Baez-Duarte full-line criterion it is retained by the tail norm.

## Corrected Alignment Status

| Item | Status after this batch |
| --- | --- |
| Arbitrary signed-parameter predicate | Rejected in M0 audit 01; it is unconditional. |
| Project restricted closure vs project restricted tolerance | Equivalent in Lean. |
| Project restricted closure vs Beurling 1955 closure | Not aligned: the project omits `sum c_k * theta_k = 0` and uses raw rather than modified generators. |
| Project positive-natural local predicate vs Baez-Duarte theorem | Not aligned: the project omits the `(1,infinity)` tail, equivalently the squared reciprocal moment. |
| `< 1` vs `<= 1` endpoint | Still a minor formal convention, but no longer the leading mismatch. |
| Real vs complex coefficients | Project coefficients are real. The reduction from complex to real coefficients for real targets and generators is mathematically routine but not yet compiled in a shared full-line space. |
| Criterion-to-`Mathlib.RiemannHypothesis` | Open; M1 cannot start from the current local predicates. |

## Decision

- `assumption_frontier_after`: M0 must use either the moment-constrained unit-interval Beurling
  space or the full-line Baez-Duarte space. The current unconstrained restricted predicate is only
  local scaffolding.
- `hard_gap_after`: closure/tolerance representation is closed, while the exact missing
  moment/tail condition is now isolated and Lean-validated.
- `hard_gap_delta`: one internal mismatch closed and one previously hidden published-statement
  dependency identified. G1, M1, D, and RH remain unchanged.
- decision: `PIVOT`

The next M0 batch should formalize the published positive-natural finite-error shape by adding the
squared reciprocal moment to the existing `(0,1)` error. This is preferable to adding more local
span wrappers because the tail identity proves exactly why that term is required.
