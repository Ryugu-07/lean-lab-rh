# H6 x H14 x H12 Height-Ten Riemann--Siegel Low-Zero Evidence

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-LOW-ZERO-01`

Classification: `MEANINGFUL_PARTIAL / PUBLIC_IMPLEMENTATION_GREEN /
IMMUTABLE_EVIDENCE_GREEN / SUBATTACK_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Frozen implementation

Implementation commit: `440a70b4d8f34445948f50e7befe13d8a8d13321`

Public Lean Action:

- run: `30714830344`;
- build job: `91408552652`;
- result: passed;
- duration: `2m25s`.

Frozen production blobs:

| file | blob |
| --- | --- |
| `LeanLab.lean` | `4594e1a68875544dcf83b8c7b91c424183eb11ca` |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelLowZero.lean` | `9bef7439b942b2c8d14d0b538fc1d22955e7d019` |
| `LeanLab/Riemann/Targets.lean` | `2a9d87f83f16091df5196f8b535fbb49e23c1caa` |
| `LeanLab/Riemann/TargetChecks.lean` | `ff063fa37462511d816a96ddeeb09f3061654701` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `e1a23ec2e5fc9825c439781f882c110515b3e644` |

The evidence commit is docs only. Its public CI and the post-CI blob check preserve all five
identities in the table above.

## Immutable evidence verification

Docs-only evidence commit `11f3de01fb7fadcb9ac5ba0ce6534e3887eea7ec` passed Lean Action run
`30714989369`, build job `91408961299`, in `1m43s`. A post-CI `git ls-tree` check confirms that
all five production blobs remain exactly equal to the frozen table.

## Compiled claim boundary

The frozen implementation proves:

- exact critical-line conjugation of the two finite Riemann--Siegel halves for arbitrary `N`;
- exact cutoff-one prefactor-plus-remainder real decomposition for `riemannXi`;
- a no-sorry conditional chain from the literal uniform real-part remainder margin to xi and
  zeta nonvanishing on `13/2<=y<=10`, then to the right-high Speiser quotient sign;
- a closed integral bound for the existing cancellation-free source majorant;
- that the displayed right side of this existing majorant is greater than `1` on the target
  interval.

The final item concerns only the coarseness of the current upper bound. It is not a lower bound
on the actual contour remainder and does not falsify the desired uniform margin.

## Audit boundary

Local audit before the frozen commit:

- standalone module `8745/8745`;
- full build `8829/8829`;
- all registration files and aggregate entry pass `-DwarningAsError=true`;
- seven selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
- forbidden scan and `git diff --check` are empty.

## Strict limits

The uniform remainder margin, actual interval nonvanishing, unconditional right-high vertical
zone, other five vertical zones, compact-middle top sign, complete boundary, height-ten
certificate, H12, and RH remain open. This record does not close the subattack, parent campaign,
or global Goal.

The next exact producer is a phase-preserving source-line estimate or a formal classical
Riemann--Siegel saddle/remainder theorem. Historical omission search remains the route-selection
priority; conjecture proposal, falsification, and direct RH attacks remain open.
