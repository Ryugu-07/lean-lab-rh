# H6 x H14 x H12 Height-Ten Riemann--Siegel Phase-Norm Evidence

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-RIEMANN-SIEGEL-PHASE-NORM-01`

Classification: `HISTORICAL_OMISSION_CHECKPOINT / PREFACTOR_PRODUCER_CLOSED /
ENDPOINT_MASS_OPEN / PUBLIC_IMPLEMENTATION_GREEN / IMMUTABLE_EVIDENCE_GREEN /
SUBATTACK_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Frozen implementation

Implementation commit: `6191095ff2bf8da3634059e36b46c55dd9a1183f`

Public Lean Action:

- run: `30718017024`;
- build job: `91416905387`;
- result: passed;
- duration: `3m30s`.

Frozen production blobs:

| file | blob |
| --- | --- |
| `LeanLab.lean` | `7ca5f5ee3a210f2b45207cef59483bdeb65f869e` |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelPhaseNorm.lean` | `f85dfcad2e70b6d55dea454792a59548290e0b08` |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelPhaseMargin.lean` | `4f1df0b7c80af06b1210134bf3da648e9778e663` |
| `LeanLab/Riemann/Targets.lean` | `0ecbd2fca27a7e6110fd8df57a8e80fb8cbc0d56` |
| `LeanLab/Riemann/TargetChecks.lean` | `6a53df17596ec6b2ba1df93ef31c7632ac6c1792` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `236788b244c070ae49c52efb7a6311d244a44f26` |

The evidence commit is docs only. Its public CI and the post-CI blob check preserve all six
identities in the table above.

## Immutable evidence verification

Docs-only evidence commit `41b2006719acdc14fcfc7ac52c2263f13b93e26e` passed Lean Action run
`30718252798`, build job `91417523983`, in `2m22s`. A post-CI `git ls-tree` check confirms that
all six production blobs remain exactly equal to the frozen table.

## Compiled claim boundary

The frozen implementation proves:

- the exact critical-line norm of the principal complex power, the source-line argument signs,
  and domination by the two fixed endpoint-height integrands;
- a reduction of the complete raw contour norm to the sum of two fixed endpoint half-line
  masses;
- a rectangular Stieltjes majorant giving norm at most `1/16` for the actual logarithmic Gamma
  remainder throughout `13/2<=y<=10`;
- exact factorization of the actual source prefactor through the project's Gamma function and a
  uniform strict real-to-norm phase margin greater than `9/10`;
- a no-sorry conditional chain from the fixed endpoint-mass proposition to the literal
  Riemann--Siegel remainder margin and the existing interval-nonvanishing consumers.

The endpoint-mass proposition is not proved by this implementation. It is the exact assertion
that the two fixed endpoint masses sum to at most `3/5`.

## Audit boundary

Local audit before the frozen commit:

- both new production modules pass standalone `-DwarningAsError=true` compilation;
- the registered targets, exact checks, aggregate project entry, and axiom audit compile;
- full build passes `8831/8831`;
- six selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
- focused forbidden scans and `git diff --check` are empty.

## Strict limits

The fixed endpoint-mass bound, unconditional Riemann--Siegel remainder margin, actual interval
nonvanishing, unconditional right-high vertical zone, other five vertical zones, compact-middle
top sign, complete boundary, height-ten certificate, H12, and RH remain open. This record does
not close the subattack, parent campaign, or global Goal.

The next exact producer is `HeightTenRiemannSiegelOneEndpointMassBound`. Historical replay
remains omission search: the closed actual-Gamma phase shows that this apparently delicate
component is not the live obstruction. Independent conjecture proposal, falsification, and
direct RH attacks remain open at every stage.
