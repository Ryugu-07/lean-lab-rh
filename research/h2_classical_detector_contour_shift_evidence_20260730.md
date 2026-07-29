# H2 Classical Detector Contour-Shift Immutable Evidence

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Classification: `FULL_SUCCESS / KNOWN_CONTOUR_SHIFT_FORMALIZED`

## Frozen implementation

- commit: `b87e9164395b14723f61d8451e3ed1b0cd0ae1c8`;
- Lean Action run: `30484701769`;
- build job: `90687338466`;
- result: passed in `2m39s`;
- local full build before publication: `8802/8802`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/ClassicalZeroDetectorContourShift.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
```

Their diff from the implementation commit is empty at evidence publication.

## Certified endpoint

`classicalDetectorContourShift_endpoint` packages:

- the actual pole-removed contour numerator and source equality;
- cancellation of the Gamma pole at `w=0` by the actual zero condition;
- the exact translated-zeta residue at `w=1-rho`;
- the fixed-strip majorant and both horizontal-edge limits;
- integrability on the source and shifted vertical lines;
- the finite one-pole rectangle and infinite shifted-line identity;
- the shifted smoothed detector series;
- the exact coefficient-gap head/tail identity.

Six exact TargetChecks compile. Seven selected axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Historical finding and boundary

The source contour shift has no hidden simple-zero assumption and no extra residue at the
canceled Gamma pole. The first open arithmetic producer is the actual dyadic Type-I/Type-II
block and tail estimate following the coefficient gap.

This evidence does not certify a zero-density theorem, sparse-exception exclusion, H2, or RH.
