# Height-ten Riemann--Siegel endpoint-mass structural checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Mode: `PROOF-ATTEMPT / LITERATURE / HISTORICAL-OMISSION-SEARCH`

Status: `MEANINGFUL_PARTIAL / ENDPOINT_MASS_OPEN / GLOBAL_GOAL_ACTIVE`

## Route-policy ruling

Historical replay is an omission search, not a bibliography. A source-backed card does not count
as an attempted route. The replay must expose a decisive source inference, its last verified
theorem, its first exact open producer, failed probes, and its surviving frontier. Original
conjectures, falsification, and direct RH attacks remain open throughout. This checkpoint applies
that policy to the fixed Riemann--Siegel source contour rather than optimizing an unrelated upper-
bound constant.

## Compiled structural results

The new module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelEndpointMass.lean` proves:

1. `2*u^4/3 <= sinh(u)^2-sin(u)^2`, using the nonnegative tail of the exact
   `cosh(2u)+cos(2u)` power series;
2. exact quartic growth for the norm square of the source sine denominator;
3. rational lower and upper bounds on `pi*sqrt(2)/2`;
4. a compact reciprocal-denominator polynomial envelope for `abs(v)<=1/2`;
5. an exponential reciprocal-denominator envelope for `abs(v)>=1/2`;
6. exact arctangent formulas for the principal argument on both source half-lines;
7. cubic compact argument and total phase/Gaussian bounds;
8. rational distance-power bounds on both compact halves;
9. an exact norm factorization for the actual cutoff-one line integrand;
10. explicit pointwise compact envelopes for the actual endpoint integrands at heights `10` and
    `13/2`.

The polynomial positivity steps are kernel-checked Bernstein expansions on `2*v in [0,1]`; no
floating-point sampling or external Boolean certificate is a premise.

## Rejected candidate

Navigation initially proposed

```text
1/sqrt(1+x) <= 1-(29/100)x  for 0<=x<=21/20.
```

This statement is false near `x=21/20` and failed before admission. The corrected theorem uses
`x<=51/50`. Lean also proves that the actual compact contour quartic parameter lies in this
smaller interval. The failed wider statement is recorded as an obstacle, not silently reused.

## Exact remaining producer

`HeightTenRiemannSiegelOneEndpointMassBound` remains unproved. The next two mathematical steps are:

1. replace the two compact exponentials by proof-producing rational polynomial envelopes and
   integrate the resulting polynomials exactly;
2. combine exact Gaussian decay, retained argument decay, and the compiled sinh denominator tail
   on the remaining half-lines.

Only after these pieces give total mass at most `3/5` may the existing remainder-margin,
critical-line nonvanishing, and right-high Speiser consumers be invoked.

## Local audit

- new module passes standalone `-DwarningAsError=true`;
- `Targets`, exact `TargetChecks`, aggregate project entry, and `AxiomsAudit` compile;
- five selected axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`;
- focused `sorry`/`admit`/`native_decide`/custom-axiom/`opaque`/`unsafe`/resource scans are empty;
- `git diff --check` is clean;
- full local build passes `8832/8832`.

## Strict limit

This checkpoint does not prove either individual endpoint integral, their total `<=3/5`, the
literal Riemann--Siegel remainder margin, interval zeta nonvanishing, an unconditional vertical
boundary zone, the complete height-ten certificate, H12, or RH. The parent campaign and global RH
Goal remain active.

## Public implementation

Frozen implementation commit `5cc6e43fad122b1bf40c1ff614183183ff4ccf53` passed Lean Action
run `30721026723`, build job `91424754896`, in `2m59s`. The five Lean production blobs are
recorded in the immutable-evidence document and must remain unchanged in its docs-only commit.
