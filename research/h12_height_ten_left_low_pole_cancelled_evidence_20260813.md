# H12 Height-Ten Left Low Pole-Cancelled Evidence

Date: 2026-08-13

Implementation commit: `69eb02d96f64ba3e94794c7b8f79f9d2f2171834`

Public Lean Action run: `31666657844`

Build job: `94342566271`

Result: passed in `2m46s`.

## Frozen Lean blobs

- `LeanLab.lean`: `7519d5f898a7151deec53ed4271509e06e1dec08`
- `LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftLowPoleCancelled.lean`:
  `46a37e64d33d63fc6fb2b3174bd101a53d89d2d6`
- `LeanLab/Riemann/Targets.lean`: `1d9b7ef379b3c65a29da02e873c07ff29c9cc43a`
- `LeanLab/Riemann/TargetChecks.lean`: `658228ef4b096b5ae251cc7b434a4f9c55b5ee22`
- `LeanLab/Riemann/AxiomsAudit.lean`: `e3c211214fec83dad74e80a8d3e23f543e0e74f2`

These blobs contain the project import, the complete pole-cancelled interval certificate, the
registered Tier-1 target, exact interval witnesses, and selected axiom prints used by the passing
public run.

## Compiled result

Lean proves

```lean
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_oneQuarter
    {y : Real} (hy0 : 0 <= y) (hy1 : y <= 1 / 4) :
    0 < (speiserZetaDerivRatio ((y : Complex) * Complex.I)).re
```

The proof cancels the reflected zeta pole exactly through `F(w)=(w-1)zeta(w)`, evaluates the
`N=1` pole-removed centers as explicit polynomials, and transports exact rational margins from a
center real part greater than `2/5` through a total error at most `1/8`. The zero endpoint is
handled by its existing exact theorem, and every positive height uses the pole-cancelled
actual-function ball.

## Axiom and claim boundary

The selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`. The
production module contains no forbidden placeholder, custom axiom, unsafe declaration, opaque
declaration, or relaxed resource option.

This closes only the preregistered interval `[0,1/4]`. Positive real part on `[1/4,6]`, the
complete left edge, other height-ten boundary producers, the complete height-ten certificate,
H12, and RH remain open. The enclosing campaign, parent campaign, and global RH Goal remain
active.

## Immutable verification

This evidence commit is docs-only. After its public Lean Action run passes, each of the five paths
will be read again from the evidence commit and compared with the implementation blobs above.
