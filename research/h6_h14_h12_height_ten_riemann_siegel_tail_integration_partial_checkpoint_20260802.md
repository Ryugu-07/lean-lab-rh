# H6 x H14 x H12 height-ten Riemann--Siegel tail integration partial checkpoint

Date: 2026-08-02

## Status

`HEIGHT-TEN-ENDPOINT-TAIL-INTEGRATION-01` remains active. Two of its three literal actual-integral
outputs compile; the positive far tail is still open.

## Compiled outputs

- `integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeTail_le` proves the actual
  height `10` endpoint-integrand norm integral on `Ioi (1/2)` is at most `19/2000`.
- `integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveNearTail_le` proves the actual
  height `13/2` endpoint-integrand norm integral on `Ioc (1/2) 1` is at most `27/200`.
- The positive principal angle is recentered exactly and receives separate compiled phase
  polynomial bounds on `[1/2,1]` and `[1,2]`.
- A general convex trapezoid integral theorem and nine exact rational node envelopes prove the
  near-tail exponential integral without numerical quadrature.

The two actual pieces total `289/2000`. The preregistered total tail budget is `3/20=300/2000`,
so the remaining positive tail on `Ioi 1` must compile at `<=11/2000`.

## Verification

- Production module passes direct warning-as-error compilation.
- `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` pass warning-as-error.
- Both selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, and `unsafe` scans are empty.
- Full build passes `8834/8834`.

## Strict boundary

This checkpoint does not prove the positive far tail, combined tail `<=3/20`, endpoint mass
`<=3/5`, literal Riemann--Siegel remainder margin, interval zeta nonvanishing, any complete
height-ten boundary certificate, H12, or RH. The global Goal remains active.

## Next exact producer

On `[1,2]`, combine the compiled middle phase polynomial with a convex exponential envelope and
eight exact trapezoids. On `Ioi 2`, prove a constant-angle lower bound and direct exponential tail.
Their actual-integrand bounds must total at most `11/2000`.
