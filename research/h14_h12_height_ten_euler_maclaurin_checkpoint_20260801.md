# H14 x H12 Height-Ten Euler--Maclaurin Checkpoint

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Status: `MEANINGFUL_PARTIAL_IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Why this bound was formalized

This is not open-ended optimization of a numerical constant. The previous reflected eta evaluator
needed navigation near one million terms because its Cauchy derivative bound loses an exponent.
Johansson's Euler--Maclaurin route is a historical evaluation method directly named in the source
survey. One integration by parts changes the actual value and derivative remainder scale from
roughly `N^(-sigma)` to `N^(-sigma-1)`. Navigation then moves the first viable cutoff to `N=30`,
which is small enough for a Lean-generated rational certificate.

## Compiled mathematical result

`LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurin.lean` proves without `sorry`:

1. the centered fractional-part tail equals a half endpoint correction plus a quadratic periodic
   tail;
2. the quadratic periodic primitive has absolute value at most `1/8`;
3. actual `riemannZeta` equals the one-correction finite Euler--Maclaurin center plus its explicit
   quadratic remainder;
4. dominated parameter differentiation gives the exact derivative remainder;
5. explicit value and derivative norm balls have order `N^(-Re(s)-1)`; and
6. finite reflected Euler--Maclaurin margins imply actual zeta nonvanishing, derivative
   nonvanishing, and strict Speiser negativity on the left point.

`LeanLab/Riemann/LevinsonMontgomeryTranscendentalInterval.lean` proves:

1. a rational odd-atanh enclosure for `log(a/b)`;
2. a complex exponential Taylor enclosure with a rational norm majorant;
3. stability when the exponent is itself known only within a certified ball;
4. a positive-real complex-power enclosure combining the log and exponential layers; and
5. closed rational smoke certificates for `log 2` and a height-ten-scale complex exponential.

## Navigation, not premises

A standard-library complex calculation sampled `sigma` from `0` to `1/2` at spacing `0.001`.
With the new rigorous analytic radii, `N=20` had a negative sampled cross margin near the critical
endpoint. At `N=30`, the sampled minimum cross margin was about `0.0867`, the zeta norm margin
stayed above `1.38`, and the reflected archimedean upper stayed below `-0.445`. None of these
floating-point values occurs in a theorem statement or proof.

## Remaining producers

1. Generate and kernel-check rational log/complex-power certificates for the 30 finite terms.
2. Aggregate rational centers for the Euler--Maclaurin value and derivative.
3. Prove explicit variation bounds and a finite rational cover of `0 <= sigma <= 1/2`.
4. Prove the actual multiplicity-bearing zeta/zeta-derivative count equality below height ten.
5. Compose the two producers into `LevinsonMontgomeryHeightTenCertificate`.

The historical-route survey remains the default selection discipline. Direct attacks on RH or an
unresolved dependency, and proposal plus falsification of new conjectures, remain open at every
stage. No complete height-ten certificate, CountDichotomy, Speiser equivalence, H12, or RH is
claimed here.

## Local audit

- Both new modules compile with `-DwarningAsError=true`.
- `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` compile with the same setting.
- Eleven selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder and resource-option scans are empty in the production sources; the declaration scan
  has no hit in any changed Lean file.
- `git diff --check` passes.
- Full `lake build` passes `8822/8822` jobs.

## Public implementation

- Commit `f55f2efce7ae21e6fc0f78d677fecbb6606b526c` passed Lean Action run
  `30661192482`, build job `91257563206`, in `2m24s`.
- The two implementation modules, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and
  `LeanLab.lean` are frozen by Git blob in
  `research/h14_h12_height_ten_euler_maclaurin_evidence_20260801.md`.
- Documentation-only evidence commit `1e33d4a762301785e329bf6477a8152134efa734` passed Lean
  Action run `30661486385`, build job `91258507742`, in `1m35s`; all six frozen Lean blobs remain
  unchanged.
