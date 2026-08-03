# H12 Height-Ten Left Middle Cell Evidence

Date: 2026-08-03

Implementation commit: `a4ded06a39519fa1c37d0e97aef8e60a32eb33fb`

Public Lean Action run: `30819281694`

Build job: `91704779376`

Result: passed in `3m51s`.

## Frozen Lean blobs

- `LeanLab.lean`: `d82c3ac3bf6a0d37202f16e5c89d2858123abfbc`
- `LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftMiddleCell.lean`:
  `729007341d025999d100f95df2656c529da00752`
- `LeanLab/Riemann/Targets.lean`: `a57730fe3ba47d81afd2e4a0f2c35b6070f247ec`
- `LeanLab/Riemann/TargetChecks.lean`: `8b78bcd3b633f7204be70a67a2f456d2a6606210`
- `LeanLab/Riemann/AxiomsAudit.lean`: `1e9205de19db1267e9a22be92e8b6624504d22ac`

These blobs contain the project import, complete rational middle-cell certificate, registered
Tier-1 target, exact interval witness, and selected axiom prints used by the passing public run.

## Compiled result

Lean proves

```lean
theorem speiserZetaDerivRatio_leftVertical_im_neg_six_thirteenHalves
    {y : Real} (hy0 : 6 <= y) (hy1 : y <= 13 / 2) :
    (speiserZetaDerivRatio ((y : Complex) * Complex.I)).im < 0
```

The fixed-center finite quotient, paired shifted archimedean phase, and complete actual-function
error ball are all rationally certified. The center imaginary part is below `-9/50`; the total
phase radius is at most `3/25`. Hence the actual sign is strict on the whole frozen interval.

## Axiom and claim boundary

The selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The
production module contains no forbidden placeholder, custom axiom, unsafe declaration, opaque
declaration, or relaxed resource option.

This is the preregistered `meaningful_partial`: `[6,13/2]` is closed, while positive real part on
`(0,6]` remains open. The complete left edge, other height-ten boundary producers, complete
height-ten certificate, H12, and RH remain open. The phase campaign, parent campaign, and global
RH Goal remain active.

## Immutable verification

Pending a docs-only evidence commit and independent public Lean Action run. The next commit must
not change any of the five frozen Lean paths.
