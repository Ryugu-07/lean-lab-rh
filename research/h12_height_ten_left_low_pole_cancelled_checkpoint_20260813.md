# H12 Height-Ten Left Low Pole-Cancelled Checkpoint

Date: 2026-08-13

Campaign: `PROOF-ATTEMPT-20260813-H12-HEIGHT-TEN-LEFT-LOW-POLE-CANCELLED-01`

Parent: `PROOF-ATTEMPT-20260803-H12-HEIGHT-TEN-LEFT-LOW-MIDDLE-PHASE-01`

Status: `FULL_SUCCESS / LOW_INTERVAL_CLOSED / ENCLOSING_CAMPAIGN_ACTIVE /
GLOBAL_GOAL_ACTIVE`

## Source alignment

The historical Levinson--Montgomery boundary argument needs the rotated logarithmic derivative
to avoid the principal slit ray. On the low part of the left imaginary-axis edge, strict positive
real part of the unrotated quotient supplies that exclusion. This checkpoint proves that
source-facing sign on the frozen interval `[0,1/4]`; it does not replace a continuum statement by
a sampled grid or an unquantified continuity neighborhood.

## Compiled result

The new module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftLowPoleCancelled.lean` proves

```lean
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_oneQuarter
    {y : Real} (hy0 : 0 <= y) (hy1 : y <= 1 / 4) :
    0 < (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re
```

For positive height, the proof replaces the separately singular reflected value and derivative
by the pole removal `F(w)=(w-1)zeta(w)`. Lean checks the exact cancellation identity

```text
zeta'(iy)/zeta(iy)
  = -F'(1-iy)/F(1-iy)
    - 1/(iy-1) + log(pi)
    - (digamma(1+iy/2) + digamma(3/2-iy/2))/2.
```

At cutoff `N=1`, the pole-removed finite centers collapse exactly to

```text
F_center(1-iy)  = (1-y^2/12) - (7y/12)i,
F'_center(1-iy) = 7/12 - (y/6)i.
```

Exact rational bounds then prove:

- the pole-cancelled phase center has real part greater than `2/5`;
- the complete value, derivative, and archimedean transport error is at most `1/8`;
- the finite value norm is at least `99/100`, so the quotient denominator margin is strict.

The endpoint `y=0` uses the existing exact theorem. For `0<y<=1/4`, the pole-cancelled evaluator
proves the strict sign. The module also compiles a reduction theorem showing that a future
producer on `[1/4,6]` closes the complete frozen low interval `[0,6]`.

## Rejected and repaired mechanisms

The available direct Hardy--Littlewood eta derivative error theorem requires `0<r<Re(s)` and
cannot be instantiated on the imaginary axis. Pure qualitative continuity was not selected
because it supplies no explicit rational join point for the remaining finite cover.

During implementation, a direct global denominator-product inequality did not close by exact
nonlinear arithmetic. It was decomposed into six explicit rational component bounds, preserving
the same mathematical margin under default resources.

The raw product center has a totalized-division artifact at `y=0`: its syntactic value there is
not the analytic limiting value. The proof therefore separates the already known exact endpoint
from the positive-height evaluator. This is an implementation-level representation issue, not a
gap in the actual interval theorem.

## Exact remaining producer

The remaining clause is now

```lean
forall y : Real, 1 / 4 <= y -> y <= 6 ->
  0 < (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re
```

Closing this clause would join the present theorem to the already compiled middle phase theorem
on `[6,13/2]`. It would still not close the other boundary producers, the complete height-ten
certificate, H12, or RH. The enclosing campaign and global Goal remain active.

## Local verification

- production module warning-as-error compilation: passed;
- aggregate Targets warning-as-error check: passed;
- exact TargetChecks warning-as-error check: passed;
- selected AxiomsAudit declarations: only `propext`, `Classical.choice`, and `Quot.sound`;
- production forbidden-token scan and `git diff --check`: clean;
- full local build: `8842/8842` jobs passed;
- public implementation, immutable evidence, and closure receipt: pending.
