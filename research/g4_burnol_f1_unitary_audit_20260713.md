# G4-F1 Burnol Unitary Distance Model Audit

Date: 2026-07-13

Batch ID: `AUDIT-20260713-G4-F1-01`

Result: `DEPENDENCY_GAP_IDENTIFIED`

## Primary Source

Jean-Francois Burnol, *A lower bound in an approximation problem involving the zeros of the
Riemann zeta function*, arXiv `math/0103058v2`, source SHA-256
`8cedd01b32a9dfd1cf5635dd446c97690ce1f4084e4da1daed9fa92c2bcffec7`.

The relevant source locations are:

- lines 169-175: `K`, `chi`, and the original `B_lambda`;
- lines 294-303: Mellin-Plancherel and normalized dilation `D_theta`;
- lines 309-323: the Hardy averaging operator `M`, the unitary `1-M`, and its multiplier;
- lines 343-357: the phase construction and its compatibility with dilations;
- lines 367-386: the explicit function `A`, multiplier `Z`, `C_lambda`, `chi1`, and the distance
  identification.

## Exact Identity And Signs

Write

```text
f(t) = rho(1/t),
M f(t) = t^-1 * integral_(0,t] f(u) du,
T = (1-M)^-1.
```

On `Re(s)=1/2`, the multiplier of `T` is

```text
m(s) = (s-1)/s,
```

and `|m(s)|=1`. The already compiled Mellin formulas give

```text
Mellin(chi)(s) = 1/s,
Mellin(f)(s) = -zeta(s)/s.
```

Consequently,

```text
Mellin(T chi)(s) = (s-1)/s^2 = Mellin(chi1)(s),
Mellin(T f)(s) = -(s-1) zeta(s)/s^2 = -Mellin(A)(s).
```

Thus the correct source-facing identities are `T chi = chi1` and `T f = -A`. The minus sign is
essential in the pointwise theorem but immaterial to the complex span.

## Normalization Matrix

| object | source convention | project convention | exact relation |
| --- | --- | --- | --- |
| target | `chi = 1_(0,1]` | `baezDuarteComplexTargetL2` | equal a.e. |
| base kernel | `f(t)=rho(1/t)` | `burnolContinuousKernelL2` at `theta=1` | equal a.e. |
| dilation | `D_theta f(t)=theta^(-1/2)f(t/theta)` | kernel `rho(theta/t)` | `rho(theta/t)=sqrt(theta) D_theta f(t)` |
| transformed kernel | `D_theta A` | prospective `A(t/theta)` | `A(t/theta)=sqrt(theta) D_theta A(t)` |
| transformed target | `chi1=(1+log t)chi` | absent | must be added explicitly |
| original span | finite complex span of `rho(theta/t)` | `burnolKernelSpan` | already aligned |
| model span | finite complex span of `D_theta A` | absent | scalar-equivalent to span of `A(t/theta)` |

Because `T` commutes with `D_theta`, it maps each project kernel to `-A(t/theta)`. Hence it maps
`B_lambda` onto `C_lambda`, and `Metric.infDist_image` gives the exact distance equality.

## Available Lean Dependencies

The pinned toolchain already supplies:

- `baezDuarteFourierMellinL2_target_eq` and `fourier_baezDuarteTargetWeightedLog` for `chi`;
- `hasMellin_fractionalPartKernel_one` and `mellin_criticalLine_eq_fourier` for the base kernel;
- `MeasureTheory.memLp_top_of_bound`, `MeasureTheory.Lp.coeFn_lpSMul`, and the Holder instance for
  pointwise multiplication `L-infinity x L2 -> L2`;
- `Metric.infDist_image` for distance preservation under an isometry;
- `Submodule.map_span` for the span image;
- `Measurable.nat_floor` for the explicit floor formula;
- `Stirling.log_stirlingSeq_formula`, `Stirling.log_stirlingSeq'_antitone`, and its global bounds;
- `Real.one_sub_inv_le_log_of_pos` for the lower bound on the term
  `floor(1/t) * log(floor(1/t)*t)`.

There is no ready-made `LinearIsometryEquiv` for multiplication by a variable unit-modulus
function and no packaged Hardy averaging operator on this `L2` space. The multiplier equivalence
must be constructed locally, but that construction is not the source-level bottleneck.

## Fixed F1 Split

### F1a: Burnol's explicit `A` proposition

This is the next admitted implementation batch. It must add, together:

```text
burnolA : Real -> Real
burnolA_eq_zero_of_one_lt
burnolA_memLp_two_positiveHalfLine
burnolComplexAL2
hasMellin_burnolA
```

The central theorem must identify the source formula nondefinitionally:

```text
HasMellin (fun t => (burnolA t : Complex)) s
  ((s-1) * riemannZeta s / s^2)
```

on a source-valid strip containing `Re(s)=1/2`. The `L2` proof should use the exact Stirling
decomposition after setting `n=floor(1/t)`:

```text
A(t) = n*log(n*t) + (1/2)*log(2*n) + log(stirlingSeq n).
```

Floor inequalities and `one_sub_inv_le_log_of_pos` bound the first term; the pinned Stirling bounds
control the last term. This gives `|A(t)| <= C + C*|log t|` on `(0,1]`, sufficient for `L2`.

### F1b: multiplier and distance assembly

Only after F1a compiles, one batch may construct:

```text
burnolHardyInverseMultiplier
burnolHardyInverseL2 : positiveHalfLineComplexL2 ~=isometry= positiveHalfLineComplexL2
burnolChiOneL2
burnolModelKernelSpan
burnolHardyInverseL2_target
burnolHardyInverseL2_kernel
burnolHardyInverseL2_map_kernelSpan
burnolDistance_eq_modelDistance
```

The frequency variable must use the project's normalization
`s=1/2+(2*pi*xi)I`. The inverse multiplier is the complex conjugate. F1b must use the explicit
F1a `A`; defining `A` or `C_lambda` solely as an isometric image is forbidden.

## Frontier Change

- `assumption_frontier_before`: F1 was a one-line source claim with no recovered operator, sign,
  scaling, or Lean dependency boundary.
- `assumption_frontier_after`: the exact multiplier, signs, dilation scalars, explicit `A` burden,
  and Lean construction path are fixed; no premise was added.
- `hard_gap_before`: F1 open and undivided.
- `hard_gap_after`: F1a and F1b open with F1a selected next; F2-F5, M2, and G3 unchanged.
- `hard_gap_delta`: source dependency boundary identified; no Lean theorem and no RH progress.

