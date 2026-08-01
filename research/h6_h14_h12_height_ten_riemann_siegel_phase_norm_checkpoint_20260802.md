# Height-ten Riemann--Siegel phase-norm checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-PHASE-NORM-01`

Mode: `PROOF-ATTEMPT / LITERATURE / HISTORICAL-OMISSION-SEARCH`

## Result

This loop closes the exact prefactor phase producer and the endpoint-domination reduction. It
does not close the fixed endpoint-mass producer, the literal Riemann--Siegel remainder margin, or
the interval nonvanishing consumer.

- `closed_edge_35`: Lean proves
  `norm(w^(-s))=norm(w)^(-1/2)*exp(y*arg w)` on the source line and proves the required argument
  signs on the two half-lines. The negative half is dominated by `y=10`; the positive half is
  dominated by `y=13/2`.
- `reduced_edge_36`: the complete raw integral is bounded by two fixed endpoint half-line masses.
  The exact remaining proposition is
  `HeightTenRiemannSiegelOneEndpointMassBound`, namely that their sum is at most `3/5`.
- `closed_edge_37`: a rectangular Stieltjes majorant gives
  `norm L(s/2)<=1/16` on the whole interval. The shifted main Stirling phase is strictly between
  `-3/8` and `1/8`; the actual Gamma factor is identified exactly as `exp L`, not treated as an
  approximation premise. Lean then proves
  `heightTenRiemannSiegelOnePrefactorPhaseMargin`.
- `conditional_edge_38`: the existing exact factorization composes the endpoint-mass proposition
  with the now unconditional prefactor phase theorem to
  `HeightTenRiemannSiegelOneRemainderMargin`. Actual zeta nonvanishing and the right-high Speiser
  sign still depend on the unproved endpoint-mass proposition.

## Mathematical content

For `s=1/2+iy`, write the actual prefactor as

```text
-c(y) * exp(E(y) + L(s/2)),  c(y)>0.
```

The proof derives this identity from the project's actual Gamma function and the exact Stieltjes
scaled-Gamma theorem. It proves monotonicity of the explicit shifted phase

```text
pi + y/4*log(1/16+y^2/4) - y/2*log(pi) - y/2 - arctan(2y)/4
```

and checks its two endpoints with rational logarithm, arctangent, and pi certificates. Adding the
Stieltjes imaginary error gives total shifted phase of absolute value less than `7/16`.
Mathlib's inequality `1-x^2/2<=cos x` then yields the strict `9/10` real-to-norm margin.

The useful omission finding is that low-height Gamma phase is not an obstruction: the source
prefactor has certified room after the exact Stieltjes correction. The live obstruction is now
entirely in the absolute mass of the phase-aware source contour at two fixed endpoint heights.

## Audit

- production modules:
  `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelPhaseNorm.lean` and
  `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelPhaseMargin.lean`;
- both new modules pass standalone warning-as-error compilation;
- registered `Targets`, exact `TargetChecks`, project entry, and `AxiomsAudit` compile;
- six selected axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`;
- focused `sorry`/`admit`/`native_decide`/custom-axiom/`opaque`/`unsafe`/resource scans are clean;
- `git diff --check` is clean;
- full local build passes `8831/8831`.

## Public implementation

Frozen implementation commit `6191095ff2bf8da3634059e36b46c55dd9a1183f` passed Lean Action
run `30718017024`, build job `91416905387`, in `3m30s`. Six production blobs are frozen in the
docs-only immutable-evidence record; that record still requires its own public CI and post-CI
identity check.

## Next exact producer

Prove `HeightTenRiemannSiegelOneEndpointMassBound`. The preferred attack should exploit the exact
denominator growth already exposed on the source line, then split each fixed endpoint integral
into proof-producing compact and tail pieces only as needed. The goal is the source-scale total
mass `<=3/5`, not optimization of the individual navigation values or best constants.

Historical-route replay remains omission search: this campaign asks whether the classical exact
contour contains a closure that was hidden by a coarse norm step. Independent conjecture
proposal, falsification, and direct RH attacks remain open at every stage.

## Strict limit

No unconditional Riemann--Siegel remainder margin, new zeta zero-free interval, vertical boundary
zone, complete height-ten certificate, H12, or RH theorem is claimed. The parent campaign and the
global RH Goal remain active.
