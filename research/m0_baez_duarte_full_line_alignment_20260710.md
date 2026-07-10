# M0 Baez-Duarte Full-Line Alignment

Date: 2026-07-10

Batch ID: `BATCH-20260710-M0-03`

## Fixed-Gap Entry

- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- `result_class`: `FORMALIZATION_ONLY`
- `assumption_frontier_before`: the positive-natural reciprocal indexing was compiled, but the
  only packaged predicate measured error on `(0,1)` and omitted the published full-line tail.
- `hard_gap_before`: the Baez-Duarte parameter family was aligned while its `L2` domain and target
  function were not.

## Published Statement Shape

Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
Rend. Mat. Acc. Lincei 14 (2003), 5-11,
<https://arxiv.org/abs/math/0202141>, works in

```text
H = L2(0,infinity),
chi = indicator of (0,1],
rho_n(x) = fract(1/(n*x)),  n positive natural.
```

For a finite real coefficient family, the squared error splits, up to null endpoints, into:

```text
integral over (0,1) of (1 - sum c_n rho_n(x))^2
+ integral over (1,infinity) of (sum c_n rho_n(x))^2.
```

## Lean Normal Form

The project now defines:

- `baezDuarteReciprocalMoment`;
- `baezDuarteUnitIntervalError`;
- `baezDuarteSplitFullLineError`;
- `nymanBeurlingBaezDuarteFullLineConcreteApprox`.

Lean proves:

```lean
baezDuarteSplitFullLineError c =
  baezDuarteUnitIntervalError c + baezDuarteReciprocalMoment c ^ 2
```

as `baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq`. The tail calculation is the
separate theorem `baezDuarte_finsupp_tail_error_eq_reciprocalMoment_sq`, so the moment term is not
inserted by definition.

The packaged predicate has the exact normalized form

```lean
forall delta > 0, exists finite c,
  unitIntervalError c + reciprocalMoment c ^ 2 < delta.
```

This is compiled as `nymanBeurlingBaezDuarteFullLineConcreteApprox_iff`.

## Relation To The Old Local Predicate

Lean proves only the safe direction

```lean
nymanBeurlingBaezDuarteFullLineConcreteApprox ->
  nymanBeurlingBaezDuarteConcreteApprox
```

as `nymanBeurlingBaezDuarteConcreteApprox_of_fullLine`, by dropping the nonnegative tail. The
reverse implication is not available and must not be assumed.

## Alignment Status

| Item | Status |
| --- | --- |
| Positive-natural parameters | Aligned by `baezDuartePositiveNatIndex` and `n -> 1/n`. |
| Target function | Aligned in split form: one on `(0,1)`, zero on `(1,infinity)`. |
| Full `L2(0,infinity)` finite error | Aligned in split integral form and normalized in Lean. |
| Endpoint `(0,1]` vs open split intervals | Closed in Batch 04 by `baezDuarteWholeLineError_eq_split`. |
| Real vs complex coefficients | Real finite-error form is compiled; a full-line complex-to-real closure bridge remains. |
| Full-line closure membership vs positive-tolerance predicate | Closed in Batch 04 by `baezDuarteTargetL2_mem_closure_iff_fullLineConcreteApprox`. |
| Equivalence with `Mathlib.RiemannHypothesis` | Open M1/G1 work. |

## Result

- `assumption_frontier_after`: M0 now has a source-faithful positive-natural finite-error predicate;
  the older local predicate is retained only as a weak consequence.
- `hard_gap_after`: natural parameters, target values, and finite full-line error are aligned in
  split form. Whole-space `Lp` closure packaging, endpoint/field bridges, and the RH equivalence
  remain open.
- `hard_gap_delta`: the previously missing tail was restored in the formal statement, but no
  published criterion theorem or RH implication was proved.
- decision: `CONTINUE` on M0, next with full-line `L2` closure packaging rather than another local
  coefficient transport.

Batch `BATCH-20260710-M0-04` subsequently completed the full-line `L2` packaging, endpoint bridge,
and closure/tolerance equivalence; see
`research/m0_baez_duarte_l2_closure_alignment_20260710.md`. The coefficient-field convention is the
remaining M0 audit item.

Batch `BATCH-20260710-M0-05` subsequently proved the real and complex closure formulations
equivalent and closed M0; see `research/m0_completion_audit_20260710.md`.
