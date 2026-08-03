# H12 Height-Ten Left Low/Middle Phase Backend Checkpoint

Date: 2026-08-03

Campaign: `PROOF-ATTEMPT-20260803-H12-HEIGHT-TEN-LEFT-LOW-MIDDLE-PHASE-01`

Parent: `HEIGHT-TEN-COMPLETE-BOUNDARY-01`

Status: `BACKEND_CHECKPOINT / BELOW_MEANINGFUL_PARTIAL / CAMPAIGN_ACTIVE /
GLOBAL_GOAL_ACTIVE`

## Compiled result

The production module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftLowMiddlePhase.lean` compiles the
following kernel-checked backend.

1. The full complex logarithmic-derivative reflection identity on the positive imaginary axis.
2. A generic quotient ball obtained from independent value and derivative balls.
3. A twice-shifted complex digamma--Stirling center with an explicit norm error.
4. A full complex ball for the actual quotient `zeta'(iy)/zeta(iy)` around a finite reflected
   second-corrected Euler--Maclaurin center.
5. Consumers turning a positive center real margin or negative center imaginary margin into the
   corresponding actual strict phase sign.
6. The exact endpoint theorem `Re(zeta'(0)/zeta(0))>0`, obtained directly from the compiled real
   bottom edge, plus a theorem reducing `[0,6]` to the positive-height interval.
7. A conditional join which composes the two frozen interval signs with the already closed
   `[13/2,7]` and `[7,10]` segments.

## Exact open producer

Neither frozen positive-width interval is closed. The remaining declarations are still:

```lean
forall y : Real, 0 < y -> y <= 6 ->
  0 < (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re

forall y : Real, 6 <= y -> y <= 13 / 2 ->
  (speiserZetaDerivRatio ((y : Complex) * Complex.I)).im < 0
```

The reflected point `1-I*y` approaches the zeta pole as `y` approaches zero. Therefore the
zero endpoint is not a routine cell of the reflected evaluator: its singular terms must cancel
before interval transport, or the endpoint must be removed exactly as done here. The next
producer is a proof-generating rational cell certificate on the positive-height intervals,
with fixed-center complex-power enclosures and explicit variation radii. Navigation decimals
are not premises.

This checkpoint is below the preregistered `meaningful_partial` threshold because neither whole
phase interval has compiled. It closes no positive-width boundary zone, no complete left edge,
no height-ten certificate, no H12 theorem, and no RH theorem. The campaign remains active.

## Verification

- focused production compilation with `-DwarningAsError=true`: passed;
- exact `TargetChecks`: passed;
- selected `AxiomsAudit`: only `propext`, `Classical.choice`, and `Quot.sound`;
- focused forbidden-token scan of the production module: clean;
- full local build: `8840/8840` jobs passed.

## Next decision

Continue with the finite rational subcover. First derive a reusable cell theorem that compares
the actual quotient at variable `y` with one fixed rational center, separating finite-power
rounding, Euler--Maclaurin remainder, archimedean remainder, and cell variation. If the first
checked cell cannot retain a strict margin, record that exact lost margin and stop only this
local mechanism before reranking the historical-route graph.

