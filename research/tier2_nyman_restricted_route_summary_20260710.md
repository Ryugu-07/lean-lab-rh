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

## What This Does Not Prove

This route does not prove a classical Nyman-Beurling criterion, a Baez-Duarte strong criterion, or
an implication to `RiemannHypothesis`.

The current endpoint is a project-local concrete integral-tolerance predicate on `L²(0,1)` with
finite real-indexed coefficients whose support is contained in `0 < a ∧ a ≤ 1`.

## Remaining Classical Gaps

The earlier inventory
`research/tier2_nyman_classical_criterion_inventory_20260710.md` listed the broad gaps. After the
restricted branch, the remaining gaps are sharper:

- Natural-parameter gap:
  Baez-Duarte's strengthening uses natural parameters. The local predicate still allows arbitrary
  real parameters in `(0, 1]`.
- Index map gap:
  A likely bridge sends positive natural indices to restricted real parameters, for example
  `n ↦ ((n : ℝ)⁻¹)` or an equivalent reciprocal convention. The exact Lean statement has not been
  selected.
- Domain/target gap:
  The local route works over `volume.restrict (Set.Ioo 0 1)` and approximates the constant-one
  representative. Baez-Duarte's usual shape is expressed on `L²(0,∞)` with an indicator target.
- Criterion-to-RH gap:
  There is still no compiled bridge from any Nyman-Beurling or Baez-Duarte criterion to
  `RiemannHypothesis`.

## Recommended Next Target

Next target:

```lean
T2.nyman.baez.duarte.natural.index.inventory
```

Question:

Which Lean indexing shape should represent Baez-Duarte natural parameters, and what exact bridge
is needed from that shape to `nymanBeurlingRestrictedConcreteApprox`?

Expected output:

- a bounded inventory of candidate Lean index types, such as `ℕ+`, `{n : ℕ // 0 < n}`, or a
  positivity-constrained `ℕ`;
- a decision about the reciprocal map into `(0, 1]`;
- a small next formal target, likely a `Finsupp.embDomain` or finite-sum reindexing lemma from
  natural-indexed coefficients into real-indexed restricted coefficients.
