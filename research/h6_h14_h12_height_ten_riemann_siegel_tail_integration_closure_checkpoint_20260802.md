# Height-ten Riemann--Siegel tail-integration closure checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-ENDPOINT-TAIL-INTEGRATION-01`

Status: `LOCAL_SUCCESS / PUBLIC_EVIDENCE_PENDING / GLOBAL_GOAL_ACTIVE`

## Compiled actual-integral outputs

- The negative endpoint tail on `Ioi (1/2)` is at most `19/2000`.
- The positive endpoint near tail on `Ioc (1/2) 1` is at most `27/200`.
- The positive middle tail on `Ioc 1 2` is at most `21/4000`.
- The positive far-far tail on `Ioi 2` is at most `1/4000`.
- Therefore the positive tail on `Ioi 1` is at most `11/2000`, and all three preregistered tail
  groups total at most `3/20`.

The middle interval uses a uniform `49/50` distance-power bound, the retained phase polynomial
`q1`, convexity of `exp(q1)`, eight exact trapezoids, and a 32-step rational quadratic exponential
envelope. The unbounded interval uses a proof of `6/5<=-arg` across both source-line quadrants,
an `exp(-9*v/2)` actual-integrand envelope, and the exact certificate `1000<=exp(9)`.

## Downstream closure

Exact set-integral decompositions prove

```text
heightTenRiemannSiegelNegativeEndpointMass 1 <= 219/2000,
heightTenRiemannSiegelPositiveEndpointMass 1 <= 981/2000.
```

Their sum proves `HeightTenRiemannSiegelOneEndpointMassBound`. Together with the already compiled
prefactor phase margin, Lean proves the literal `HeightTenRiemannSiegelOneRemainderMargin`, actual
`riemannZeta (1/2+iy) != 0`, and strict negativity of the actual Speiser quotient real part for
`13/2<=y<=10`.

## Verification

- The production module, Targets, TargetChecks, and AxiomsAudit pass warning-as-error.
- Selected final declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused forbidden scans and `git diff --check` are clean.
- Full local build passes `8834/8834`.

## Strict boundary and next producer

This closes the endpoint-mass producer and the right-high critical-line zone only. The right
low/middle zones, entire left vertical, compact-middle top interval, rotated-slit boundary,
literal height-ten certificate, H12, and RH remain open.

The next exact producer returns to the existing complete-boundary preregistration: construct a
proof-producing actual quotient interval evaluator for the remaining vertical and top zones.
The endpoint constants are closed and are not candidates for further optimization. Historical
omission search remains the governing purpose of this replay; original conjectures, falsification,
and direct RH attacks remain open.
