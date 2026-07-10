# M0 Baez-Duarte L2 Closure Alignment

Date: 2026-07-10

Batch ID: `BATCH-20260710-M0-04`

## Classification

- `node_id`: `M0`
- `work_class`: `FORMALIZATION`
- `result_class`: `FORMALIZATION_ONLY`
- RH progress: none

## Source Shape

Baez-Duarte's strengthened criterion uses the Hilbert space `L2(0,infinity)`, target
`chi_(0,1]`, and the positive-natural family `rho(1/(n*x))`. Batch 03 represented its finite error
as the sum of the target-one error on `(0,1)` and the target-zero error on `(1,infinity)`.

This batch packages that shape in the actual mathlib space

```text
Lp Real 2 (volume.restrict (Set.Ioi 0))
```

instead of using a direct sum or leaving the two integrals disconnected from a Hilbert-space
closure.

## Lean Outputs

The following definitions package the published domain, target, generators, span, and closure:

- `positiveHalfLineL2`
- `baezDuarteTargetFunction`
- `baezDuarteTargetL2`
- `baezDuarteKernelL2`
- `baezDuarteKernelSpan`
- `baezDuarteKernelClosure`

The main integrability theorem is `fractionalPartKernel_memLp_two_positiveHalfLine`. It splits
`(0,infinity)` into `(0,1]` and `(1,infinity)`. The kernel is bounded on the first part. On the
second part, `0 < a <= 1` gives `rho(a/x) = a/x`, whose square is a constant multiple of
`x^(-2)`.

The whole-space norm is connected to the split error by:

```text
norm_sub_baezDuarte_sum_sq_eq_wholeLineError
baezDuarteWholeLineError_eq_split
```

The second theorem uses `(0,infinity) = (0,1] union (1,infinity)` and
`integral_Ioc_eq_integral_Ioo` to show that the target endpoint at `1` does not change the volume
integral.

The batch endpoint is the compiled equivalence:

```text
baezDuarteTargetL2_mem_closure_iff_fullLineConcreteApprox :
  baezDuarteTargetL2 ∈ baezDuarteKernelClosure ↔
    nymanBeurlingBaezDuarteFullLineConcreteApprox
```

Thus the Batch 03 positive-tolerance predicate is exactly the real whole-space closure-membership
statement, not merely an analogous split formula.

## Alignment Status

| Item | Status after Batch 04 |
| --- | --- |
| Positive-natural parameters | Aligned. |
| Actual `L2(0,infinity)` domain | Aligned in mathlib `Lp`. |
| Target `chi_(0,1]` | Packaged as `baezDuarteTargetL2`. |
| Positive-natural kernels | Packaged as `baezDuarteKernelL2`. |
| Full-line finite error | Equal in Lean to `baezDuarteSplitFullLineError`. |
| Endpoint `(0,1]` vs `(0,1)` | Closed by a null-endpoint integral identity. |
| Closure membership vs positive tolerance | Exactly equivalent in Lean. |
| Real vs complex coefficient convention | Still requires a source audit or a real-part bridge. |
| Equivalence with `Mathlib.RiemannHypothesis` | Open M1/G1 work. |

## Result

- `assumption_frontier_before`: the source-faithful finite error existed only as split integrals.
- `assumption_frontier_after`: the target and generators are honest elements of real
  `L2(0,infinity)`, and closure membership is exactly the split positive-tolerance predicate.
- `hard_gap_before`: M0 whole-space packaging, endpoint alignment, and coefficient-field
  comparison remained.
- `hard_gap_after`: M0 whole-space packaging and endpoint alignment are closed; only the
  coefficient-field/source-convention audit remains before an M0 completion decision. M1/G1, D,
  and RH are unchanged.
- `hard_gap_delta`: two M0 representation mismatches closed; no published criterion-to-RH theorem
  was proved.
- decision: `CONTINUE` M0 with a bounded coefficient-field audit, then decide whether M0 can close
  and M1 can begin.
