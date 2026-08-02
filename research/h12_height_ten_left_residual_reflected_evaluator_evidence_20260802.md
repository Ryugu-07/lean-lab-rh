# H12 Height-Ten Residual-Left Reflected Evaluator Evidence

Date: 2026-08-02

Implementation commit: `299ced5b6825e98ff52462d7e2743e3c8441f834`

Public Lean Action run: `30729012677`

Build job: `91445811240`

Result: passed in `2m42s`.

## Frozen Lean blobs

- `LeanLab.lean`: `dedd4b6bc743663c9efbd39ce8d90ed911c373ec`
- `LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurinSecond.lean`:
  `58337403b9b8bd530a81baaf54f2aec48921ef44`
- `LeanLab/Riemann/LevinsonMontgomeryHeightTenLeftResidual.lean`:
  `ee5fcb799bcd0f0a832d46dde745277137397e0a`
- `LeanLab/Riemann/Targets.lean`: `f3993231f72dc00d4ee80d8d4d27dc6db9c8e831`
- `LeanLab/Riemann/TargetChecks.lean`: `d10064c579e025b066db85177c8f36c1ff98d15c`
- `LeanLab/Riemann/AxiomsAudit.lean`: `3071553c8363bc6e517f4e68acb926c9bc72357a`

These blobs contain the project imports, both production theorem chains, exact target registration,
exact statement checks, and axiom prints used by the passing implementation run.

## Immutable verification

Docs-only evidence commit: `121a96e344b7dbb8a2191b5e6425ec02b7c8ede3`.

Lean Action run `30729165366`, build job `91446218169`, passed in `1m50s`.

Each of the six paths was read again from that commit. Every blob identity exactly matches the
implementation record above.

## Claim boundary

The implementation proves an actual second-corrected Euler--Maclaurin value and derivative
evaluator, a twice-shifted reflected archimedean enclosure, the virtual-axis reflection identity,
and a generic consumer from finite reflected margins to the actual rotated-slit condition. It does
not produce the finite rational subcover of `[13/2,7]` and does not prove the complete vertical
boundary, height-ten certificate, H12, or RH.

The complete-boundary subattack, parent campaign, and global RH Goal remain active.
