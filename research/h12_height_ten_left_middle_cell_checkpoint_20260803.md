# H12 Height-Ten Left Middle Cell Checkpoint

Date: 2026-08-03

Campaign: `PROOF-ATTEMPT-20260803-H12-HEIGHT-TEN-LEFT-LOW-MIDDLE-PHASE-01`

Parent: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Status: `MEANINGFUL_PARTIAL / MIDDLE_INTERVAL_CLOSED / CAMPAIGN_ACTIVE /
GLOBAL_GOAL_ACTIVE`

## Source alignment

The historical Levinson--Montgomery boundary argument requires the rotated logarithmic
derivative to avoid the principal slit ray. On the left imaginary-axis edge this can be supplied
by a sign of either component of the unrotated quotient. The preregistered phase handoff fixes
negative imaginary part on `[6,13/2]`; this checkpoint proves exactly that source-facing
producer. It does not replace the source statement by a sampled grid or a conditional numerical
oracle.

## Compiled result

The new 1702-line module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftMiddleCell.lean` proves

```lean
theorem speiserZetaDerivRatio_leftVertical_im_neg_six_thirteenHalves
    {y : Real} (hy0 : 6 <= y) (hy1 : y <= 13 / 2) :
    (speiserZetaDerivRatio ((y : Complex) * Complex.I)).im < 0
```

One rational cell centered at `25/4` and cutoff `N=4` covers the complete frozen interval. The
proof keeps the finite complex phase, rather than bounding only norms:

- the rounded finite value center differs from the exact Euler--Maclaurin value center by at
  most `1/50000`;
- the rounded finite derivative center differs by at most `1/25000`;
- componentwise Bernstein certificates imply the finite quotient imaginary part is below
  `-3/25`;
- an exact paired-argument decomposition and rational arctangent gap prove the shifted
  archimedean imaginary part is below `-3/50`;
- the combined phase center is below `-9/50`, while the complete actual-function phase error is
  at most `3/25`;
- the exact value norm is at least `437/500`, so every quotient denominator margin is strict.

Consequently the actual logarithmic derivative has negative imaginary part throughout the
positive-width interval, not merely at finitely many points.

## Failed certificate and repair

A direct degree-20 Bernstein certificate for the combined quotient-numerator inequality was
mathematically positive coefficient by coefficient, but its normalization exceeded Lean's
default heartbeat limit. The attempt was removed without adding `maxHeartbeats` or any other
resource relaxation. Lower-degree component certificates compile under default resources and
prove a slightly weaker margin that is still sufficient. This is a repaired implementation
obstacle, not evidence against the phase mechanism.

## Exact remaining producer

The preregistered low clause remains open:

```lean
forall y : Real, 0 < y -> y <= 6 ->
  0 < (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re
```

The value at `y=0` is already proved exactly. The obstacle is uniform transport immediately
above zero: the reflected point approaches the zeta pole, so separate value and derivative
balls conceal cancellation. The next decision is between a pole-cancelled reflected evaluator
and a direct local expansion for the analytic quotient at zero, followed by ordinary rational
cells away from zero.

This checkpoint meets the preregistered `meaningful_partial` criterion because one entire frozen
phase interval is closed. It does not prove the complete left edge, the height-ten certificate,
H12, or RH. The campaign and global Goal remain active.

## Local verification

- production module compilation under default resources: passed;
- aggregate Targets warning-as-error check: passed;
- exact TargetChecks warning-as-error check: passed;
- selected AxiomsAudit declarations: only `propext`, `Classical.choice`, and `Quot.sound`;
- focused forbidden-token scan and `git diff --check`: clean;
- full local build: `8841/8841` jobs passed;
- public implementation commit `a4ded06a39519fa1c37d0e97aef8e60a32eb33fb`: Lean Action run
  `30819281694`, build job `91704779376`, passed in `3m51s`;
- immutable evidence and closure receipt: pending.
