# Tier 2 Nyman-Beurling restricted route summary

Date: 2026-07-10

Target: `T2.nyman.restricted.route.summary`

## Compiled Chain

The restricted branch now has a compiled project-local route:

```lean
nymanBeurlingRestrictedKernelDense
  → nymanBeurlingRestrictedConcreteApprox
  → nymanBeurlingConcreteApprox
```

The main endpoint is:

```lean
nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense
```

The second arrow was already available as:

```lean
nymanBeurlingConcreteApprox_of_restricted
```

Together these give a concrete approximation consequence of restricted kernel density, but only
inside the project-local formulation.

Batch `BATCH-20260710-M0-02` later strengthened the internal endpoint to the exact equivalence

```lean
unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure ↔
  nymanBeurlingRestrictedConcreteApprox.
```

## Internal Bridge Nodes

The branch was built from these compiled nodes:

- restricted span and closure scaffolding:
  `nymanBeurlingRestrictedKernelSpan`, `nymanBeurlingRestrictedKernelClosure`;
- restricted density predicate:
  `nymanBeurlingRestrictedKernelDense`;
- closure to finite sums:
  `exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`;
- norm form:
  `exists_restricted_finsupp_sum_norm_sub_lt_of_dense`;
- norm-square to selected representative integral:
  `norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self`;
- concrete representative bridge:
  `restricted_finsupp_sum_fractionalPartKernelL2_coeFn`,
  `unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn`,
  `norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete`;
- positive-tolerance concrete bound:
  `exists_restricted_finsupp_integral_lt_of_dense_tolerance`;
- subtype-to-real coefficient bridge:
  `exists_real_finsupp_of_restricted_finsupp`,
  `exists_real_finsupp_integral_lt_of_restricted`;
- packaged predicate:
  `nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense`.
- exact local closure/tolerance bridge:
  `unitIntervalOneL2_mem_restrictedClosure_iff_concreteApprox`.
- omitted-tail calculation:
  `restricted_finsupp_sum_eq_moment_div_of_one_lt`,
  `restricted_finsupp_tail_error_eq_moment_sq`.

## What This Does Not Prove

This route does not prove a classical Nyman-Beurling criterion, a Baez-Duarte strong criterion, or
an implication to `RiemannHypothesis`.

The current endpoint is a project-local concrete integral-tolerance predicate on `L²(0,1)` with
finite real-indexed coefficients whose support is contained in `0 < a ∧ a ≤ 1`.

It omits Beurling's condition `sum c_k * a_k = 0`. Consequently its restricted closure is not the
published Beurling closure. It also omits the Baez-Duarte `(1,∞)` tail, whose squared norm is exactly
the square of that coefficient-parameter moment.

## Remaining Classical Gaps

The earlier inventory
`research/tier2_nyman_classical_criterion_inventory_20260710.md` listed the broad gaps. After the
restricted branch, the remaining gaps are sharper:

- Moment/tail gap:
  Beurling's unit-interval criterion imposes `sum c_k * a_k = 0`; Baez-Duarte's full-line norm
  retains the equivalent squared tail penalty. The project predicate has neither.
- Natural-parameter indexing:
  Loops 126-130 later compiled the reciprocal positive-natural indexing and finite-sum transport,
  so indexing itself is no longer the leading gap.
- Domain/target gap:
  The local route works over `volume.restrict (Set.Ioo 0 1)` and approximates the constant-one
  representative. Baez-Duarte's usual shape is expressed on `L²(0,∞)` with an indicator target.
- Criterion-to-RH gap:
  There is still no compiled bridge from any Nyman-Beurling or Baez-Duarte criterion to
  `RiemannHypothesis`.

## Corrected V2 Next Step

Remain on fixed node M0. Formalize the positive-natural published finite-error shape by adding the
squared reciprocal coefficient moment to the existing `(0,1)` error. Do not add another local
transport target and do not use the unconstrained restricted predicate in M1.

Batch `BATCH-20260710-M0-03` completed this step as
`nymanBeurlingBaezDuarteFullLineConcreteApprox`. The remaining M0 task is whole-space `Lp` closure
packaging and endpoint/coefficient-field alignment.

Batches `BATCH-20260710-M0-04` and `BATCH-20260710-M0-05` subsequently completed the whole-space,
endpoint, and coefficient-field alignment. M0 is complete; see
`research/m0_completion_audit_20260710.md`.
