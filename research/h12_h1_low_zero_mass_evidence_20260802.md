# H12 x H1 Low-Zero Paired-Mass Evidence

Date: 2026-08-02

Implementation commit: `53199a715aa5a0c61be34046e9b0f0ebd2f811a8`

Public Lean Action run: `30731573751`

Build job: `91452790708`

Result: passed in `2m49s`.

## Frozen Lean blobs

- `LeanLab.lean`: `533949fc2bf65486c71894325febf1f112e107c5`
- `LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftLowZeroMass.lean`:
  `e7b843bc348a696fba577e579463414bfdd7a0cc`
- `LeanLab/Riemann/Targets.lean`: `4431c486e2afec6925df3a1e6af59b5da643fc30`
- `LeanLab/Riemann/TargetChecks.lean`: `3f5a73f7007cdbf6111d20a3fa764ef475a7d255`
- `LeanLab/Riemann/AxiomsAudit.lean`: `f5beda2bf06330859467ed253432f451b7c4b290`

These blobs contain the project import, the complete low-zero paired-mass production chain, exact
target registration, exact statement witnesses, and axiom prints used by the passing public run.

## Immutable verification

Docs-only evidence commit: `9185790247f0ab4098da14be422afac1ed52e52c`.

Lean Action run `30731746028`, build job `91453211188`, passed in `2m39s`.

Each of the five paths was read again from that commit. Every blob identity exactly matches the
implementation record above.

## Compiled result

Lean proves the actual signs `0<hardyXi(10)` and `hardyXi(17)<0`, hence an actual critical-line
zero in `[10,17]`. One multiplicity-bearing paired divisor term from that zero is at most
`-1/221` throughout `[13/2,7]`. Eight exact digamma shifts prove the archimedean term is below
`9/2000`; therefore the actual logarithmic-derivative quotient has negative real part and its
rotation by `I` lies in `Complex.slitPlane` on the whole residual left-high interval.

## Axiom and claim boundary

The selected final declarations use only `propext`, `Classical.choice`, and `Quot.sound`. No
decimal zero ordinate, external zero table, forbidden placeholder, or custom axiom is a premise.

This closes the residual left-high interval, not the complete height-ten boundary. Left low and
middle zones, right low and middle zones, compact-middle top, the complete height-ten certificate,
H12, and RH remain open. The complete-boundary campaign and global RH Goal remain active.

