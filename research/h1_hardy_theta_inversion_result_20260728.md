# H1 Hardy Theta-Inversion Result

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H1-HARDY-THETA-INVERSION-01`

Classification: `MEANINGFUL_MELLIN_INVERSION_PARTIAL /
SOURCE_NORMALIZATION_CORRECTION`

## Compiled result

`LeanLab/Riemann/HardyThetaInversion.lean` proves the actual completed critical-line Mellin
transform vertically integrable, applies positive-real Mellin inversion, independently inverts
the two elementary pole terms, and derives Hardy's exact 1914 equation (1) for every positive
real `x`.

The aggregate certificate is `hardyThetaInversion_endpoint`. The literal source theorem is
`hardyCahenMellinInversion`.

## Normalization correction

Mathlib's `WeakFEPair.f_modif` does not equal
`Theta(pi*x)-1-x^(-1/2)` pointwise. It subtracts `1` above one and `x^(-1/2)` below one, with a
chosen zero value at one. The compiled `hardyPoleKernel` has Mellin transform

```text
1/s + 1/(1/2-s),
```

which becomes `2/(1/4+4t^2)` on `s=1/4+it`. Subtracting the two inverse transforms restores the
literal source equation. Dominated continuity proves the final formula at `x=1`.

## First open theorem

Attack C first requires exponential-weight integrability

```text
Integrable (exp(a*|t|) * norm(Xi(2t))/(1/4+4t^2))
```

for every `0<=a<pi/2`. The current uniform xi bound supplies only rational decay. This theorem
must be proved before claiming strip analyticity or Hardy equation (2).

## Mechanical audit

- production module: 803 lines;
- standalone and warning-as-error compiles: pass;
- Targets and exact TargetChecks: pass;
- selected axiom prints: only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden/custom-declaration/resource-relaxation scans: empty;
- `git diff --check`: pass;
- full build: `8781/8781`;
- frozen implementation: `8b687aa46d67a049680a7cf964ce8e982f325afa`;
- public implementation CI: run `30378958429`, job `90341715211`, passed in `2m29s`;
- immutable evidence: docs-only commit
  `189ac653a5e3b04bc49f639d80d9e8dd0614f515`, run `30379288299`, job
  `90342851859`, passed in `1m48s`;
- proof freeze: the `LeanLab/` diff from the frozen implementation to immutable evidence is
  empty.

## Claim boundary

No complex-strip identity, boundary Abel limit, all-order moment law, unconditional Hardy
infinitude theorem, positive proportion, H1, or RH is proved. The global RH Goal remains active.
This campaign stops locally at its preregistered meaningful-partial boundary; the next action is
fresh cross-family route selection rather than numerical or constant optimization.
