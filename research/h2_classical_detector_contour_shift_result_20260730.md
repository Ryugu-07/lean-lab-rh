# H2 Classical Detector Contour-Shift Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Node: `H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Classification: `FULL_SUCCESS / KNOWN_CONTOUR_SHIFT_FORMALIZED`

Public state: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_CI_PENDING`

## Result

The preregistered endpoint compiles without placeholders as
`classicalDetectorContourShift_endpoint` in
`LeanLab/Riemann/ClassicalZeroDetectorContourShift.lean`.

For an actual nontrivial zeta zero `rho` with `1/2 < Re(rho)` and `Y>0`, Lean proves

```text
classicalDetectorMellinLineIntegral M rho Y 2
  =
    Y^(1-rho) * Gamma(1-rho) * classicalDetectorMollifier M 1
    + classicalDetectorMellinLineIntegral M rho Y (1/2-Re(rho)).
```

Composing with the existing inverse-Mellin theorem gives the identical formula with
`classicalDetectorSmoothedSeries M Y rho` on the left.

For `M>=1`, absolute summability also gives the exact source coefficient-gap split

```text
1 + (exp(-1/Y)-1)
  + sum_(n>=0) classicalDetectorSmoothedTerm M Y rho (n+M+1)
  =
    Y^(1-rho) * Gamma(1-rho) * classicalDetectorMollifier M 1
    + classicalDetectorMellinLineIntegral M rho Y (1/2-Re(rho)).
```

## Compiled chain

```text
actual zero condition
-> holomorphic pole-removed numerator P(w)
-> source equality P(w)/(w-(1-rho)) away from 0 and 1-rho
-> w=0 removable without a simple-zero assumption
-> exact retained residue P(1-rho)
-> uniform fixed-strip horizontal majorant
-> top and bottom horizontal integrals tend to zero
-> actual source and shifted vertical lines are integrable
-> finite one-pole weighted-Cauchy rectangle
-> infinite shifted-line identity
-> shifted smoothed series
-> coefficient-gap head/tail identity.
```

## Historical omission result

The Maynard--Pratt Appendix C contour shift can be reconstructed under its literal assumptions.
The Gamma pole at `w=0` contributes no residue at an actual zeta zero, and no simplicity premise
is needed. The only retained pole is the translated zeta pole at `w=1-rho`.

No overlooked weakening in this step eliminates the next arithmetic input. The first open H2
successor is the source's quantitative dyadic Type-I/Type-II block and tail estimates that turn
the coefficient gap into a zero-density dichotomy.

## Local audit

- new production module: 1305 lines;
- no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, `unsafe`, heartbeat, or
  recursion-depth relaxation;
- warning-as-error compiles: production module, `Targets.lean`, `TargetChecks.lean`,
  `AxiomsAudit.lean`, and `LeanLab.lean`;
- exact TargetChecks: six;
- selected axiom prints: seven, each using only `propext`, `Classical.choice`, and `Quot.sound`;
- exact Target registration: one proven target;
- forbidden/resource scans and `git diff --check`: empty;
- full build: `8802/8802`.

## Claim boundary

The result does not prove the dyadic Type-I/Type-II estimates, a zero-density exponent, the
exclusion of sparse off-line zeros, H2, or RH. It closes the selected known contour inference,
not the whole classical detector route.

The persistent RH Goal remains active.

## Public implementation

Frozen implementation commit `b87e9164395b14723f61d8451e3ed1b0cd0ae1c8` passed Lean Action
run `30484701769`, build job `90687338466`, in `2m39s`. The five proof and registration files
have an empty diff from that commit at immutable-evidence publication.

Immutable-evidence commit `1cc20bca2455d9eb9ca27a0e42fbaf86b340b4e8` passed Lean Action
run `30485116278`, build job `90688732121`, in `1m36s`. The frozen diff remains empty.

Final-ledger commit `8ab5c9f0fcf187a240ad3bb371e14f788e127997` passed Lean Action run
`30485360308`, build job `90689557179`, in `2m13s`; the frozen diff remains empty.
