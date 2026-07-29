# H2 Classical Detector Inverse Mellin Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-01`

Node: `H2-CLASSICAL-DETECTOR-INVERSE-MELLIN-LINE-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL_PUBLIC_CI_REQUIRED`

## Parent and available producer

- `parent_closure`: H7 Connes projection-defect closure receipt
  `11e020fcfe8d2d616a0d42a061f638152fc73636`, public run `30412357592`, build job
  `90451181471`, passed in `1m55s`.
- `available_module`: `LeanLab/Riemann/ClassicalZeroDetectorMellin.lean`.
- `available_result`: the exact coefficient gap, actual zeta-product L-series, exponentially
  smoothed head-tail split, complete forward Mellin transform, canceled zero residue, retained
  translated-zeta residue, and cardinality-audited finite detector all compile.
- `first_open_prop`: `ClassicalDetectorInverseMellinLine`.

## Source statement

For every natural cutoff `M`, complex parameter `z`, positive smoothing scale `Y`, and positive
vertical line `c` satisfying

```text
1 - Re(z) < c,
```

prove

```text
classicalDetectorSmoothedSeries M Y z
  = (1/(2*pi)) * integral_t
      classicalDetectorMellinContourFactor M z Y (c+t*i).
```

This is exactly the existing definition `ClassicalDetectorInverseMellinLine`. No hypothesis may
be dropped, weakened, or strengthened silently.

## Fixed implementation

After preregistration public CI, create
`LeanLab/Riemann/ClassicalZeroDetectorInverseMellin.lean`.

The proof must use the actual production definitions. It may import Mathlib's Mellin inversion
and existing project Gamma estimates, but it may not introduce an assumed inversion theorem or
an abstract contour interface equivalent to the target.

## Full-success criteria

`FULL_SUCCESS` requires all of the following:

1. Prove `Complex.VerticalIntegrable Complex.Gamma c` for every real `c>0`, or an exactly
   equivalent theorem visibly sufficient for the subsequent inversion.
2. Specialize `mellinInv_mellin_eq` to `x -> exp(-x)` and prove the exact `1/(2*pi)`
   vertical-line formula for every positive evaluation point and every `c>0`.
3. Prove absolute integrability of every detector line integrand under `0<Y`, `0<c`, and
   `1-Re(z)<c`.
4. Justify the infinite coefficient sum and vertical-integral exchange from the actual absolute
   L-series bound on `Re(z)+c>1`.
5. Rewrite the resulting summed kernel through
   `LSeries_classicalDetectorCoefficient_eq` and the actual contour factor.
6. Prove

   ```text
   theorem classicalDetectorInverseMellinLine :
     ClassicalDetectorInverseMellinLine
   ```

   without any additional premise.
7. Register one proven Target `H2.classical-detector.inverse-mellin-line`, exact TargetChecks,
   selected axiom prints, and the root import.

## Partial, falsification, and blocked criteria

`MEANINGFUL_PARTIAL` requires items 1 and 2 plus a compiled theorem reducing the final detector
identity to one named sum-integral exchange or integrability statement.

`FALSIFIED_STATEMENT` requires a compiled counterexample satisfying all four exact domain
hypotheses of `ClassicalDetectorInverseMellinLine`.

`BLOCKED_API` requires the Gamma vertical-integrability proof and single-kernel inversion to
compile, together with the exact unavailable Bochner-integral or tsum interface. Library friction
alone is not mathematical falsification.

## Negative controls and claim boundary

- `c>0` is the Mellin convergence line and avoids the Gamma pole boundary; no `c=0` theorem is
  claimed.
- `Re(z)+c>1` is the absolute Dirichlet-series region used for sum-integral exchange. The
  campaign does not claim the formula is false after analytic continuation outside that region.
- `Y>0` is required for the real logarithm and complex-power normalization.
- The line parameter is real `t`; the source normalization is `1/(2*pi)`, not
  `1/(2*pi*i)`, because `dw=i*dt`.
- A vertical inverse identity is not a contour shift.
- No horizontal-edge decay, off-line-zero detector inequality, density estimate, H2 theorem,
  or RH theorem may be inferred.

## Audit gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. warning-as-error compile of the new module and registration files;
4. exact TargetChecks and selected standard-only axiom prints;
5. empty forbidden/resource scans;
6. `git diff --check` and full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop this local campaign and rerank all
historical routes.
