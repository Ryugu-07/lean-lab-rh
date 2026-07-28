# H12 Levinson--Montgomery Left-Half-Plane Winding Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01`

Node: `H12-LM-LEFT-HALF-PLANE-WINDING-01`

Classification: `FULL_SUCCESS_LOCAL / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Compiled result

The new module
`LeanLab/Riemann/LevinsonMontgomeryLeftHalfPlaneWinding.lean` compiles the exact
Levinson--Montgomery topological inference:

```text
strict left-half-plane differentiable path + interval integrability
  -> principal-log endpoint formula for integral g'/g
  -> zero logarithmic winding when the path is closed.
```

It also defines the actual source ratio
`speiserZetaDerivRatio = deriv riemannZeta / riemannZeta`, proves its complex and horizontal
derivative identities, and compiles
`intervalIntegral_speiserZetaDerivRatio_horizontal`. Under
`SpeiserStrictNegativeHorizontal t`, that theorem identifies

```text
integral from 0 to 1/2 of
  logDeriv(deriv riemannZeta)(sigma+t*I) - logDeriv(riemannZeta)(sigma+t*I)
```

with the principal-log difference of the two endpoint values of `-(zeta'/zeta)`.

The registered aggregate target is
`H12.speiser.left-half-plane-winding`, implemented by
`levinsonMontgomeryLeftHalfPlaneWinding_endpoint`.

## Definition boundary exposed

The actual horizontal derivative theorem needs `0 < t` explicitly. This is not cosmetic:
Mathlib's `riemannZeta` is totalized, so a nonzero value alone does not prove that the point is
away from `s = 1`, while the analytic derivative facts used here require `s != 1`.

This boundary was retained in `SpeiserStrictNegativeHorizontal`; no inference from totalized
nonvanishing to analyticity was introduced.

## Mechanical audit

- standalone warning-as-error compile: passed
- module build: passed
- `Targets.lean`: warning-as-error passed
- `TargetChecks.lean`: seven exact checks passed
- `AxiomsAudit.lean`: seven selected declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
- forbidden scans: no `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`, new
  `axiom/constant`, or relaxed resource/trace option
- `git diff --check`: passed
- full build: `8789/8789` passed

## Claim boundary

This result does not produce a height at which the actual ratio is strictly left-pointing. It
does not assemble the finite critical-zero indentations into a global contour, prove the
argument principle for the zeta and zeta-derivative divisors, control the Jensen top edge, or
derive either Levinson--Montgomery count bound.

Therefore Speiser equivalence, derivative-zero exclusion, H12, and RH remain open.
`rh_frontier_delta=0`.

## Successor graph

The exact remaining historical chain is:

```text
actual strict-negative horizontal height
  + finite oriented indentation assembly
  + multiplicity-aware argument principle
  + Jensen top variation
  -> Levinson--Montgomery count comparison
  -> Speiser criterion.
```

The first two analytic/topological successors remain
`H12-LM-INDENTED-ARGUMENT-PRINCIPLE-01` and
`H12-LM-JENSEN-TOP-VARIATION-01`. Route selection after public closure must compare them
against the other historical families rather than continuing H12 automatically.
