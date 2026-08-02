# Height-ten left boundary above seven evidence

Date: 2026-08-02

Implementation commit: `135d631c24c2a51b0158c3d3ef335c9d6a16dcdd`

Public Lean Action run: `30727229831`

Build job: `91441050957`

Result: passed in `2m33s`.

## Frozen Lean blobs

- `LeanLab.lean`: `9c4c6ad804d8653191c4ec333ad9d913ce9eeccc`
- `LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftHigh.lean`:
  `4aa42e2641282e057d330913fc6f60091bf97820`
- `LeanLab/Riemann/Targets.lean`: `c61e4f4a005b440d7e1c378bf460fdbe4aac2330`
- `LeanLab/Riemann/TargetChecks.lean`: `719974366437ec2c859cd6f77dc34d3adf8369f2`
- `LeanLab/Riemann/AxiomsAudit.lean`: `5897169049f56ee877c3f7b19b772598139ae367`

These blobs contain the project import, production theorem chain, exact target registration,
exact statement checks, and axiom prints used by the passing implementation run.

## Immutable verification

Docs-only evidence commit: `b0a2d35b0882364fae153df3eeb79e7a29f09228`.

Lean Action run `30727358310`, build job `91441411867`, passed in `1m47s`.

Each of the five paths was read again from that commit. Every blob identity exactly matches the
implementation record above.

## Claim boundary

The implementation proves positive-imaginary-axis zeta nonvanishing and closes the actual left
vertical rotated-slit condition for `y>=7`. It does not prove the residual `[13/2,7]` interval, the
remaining boundary zones, the complete height-ten certificate, H12, or RH.

The complete-boundary subattack, parent campaign, and global RH Goal remain active.
