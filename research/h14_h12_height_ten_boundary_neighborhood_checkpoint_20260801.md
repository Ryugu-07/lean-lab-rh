# H14 x H12 Height-Ten Boundary Neighborhood Checkpoint

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-TWO-BOUNDARY-NEIGHBORHOODS-01`

Status: `ACTUAL_TOPOLOGICAL_REDUCTION_IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
CAMPAIGN_ACTIVE / GLOBAL_GOAL_ACTIVE`

## Historical-route role

Levinson--Montgomery page 52 needs strict negativity on the complete height-ten horizontal. The
project already had an analytic proof at the left endpoint and a proof-producing
Euler--Maclaurin certificate at the right endpoint. This checkpoint joins them through actual
analytic continuity and removes both endpoint regions from the remaining top-edge problem.

This is not numerical constant optimization. No radius is computed or assumed.

## Compiled mathematical result

`LeanLab/Riemann/LevinsonMontgomeryHeightTenBoundaryNeighborhood.lean` proves without `sorry`:

1. an actual positive-width interval `[0,a]` on which zeta and its derivative are nonzero and
   `Re(zeta'/zeta)<0` at height ten;
2. an actual positive-width interval `[b,1/2]` with the same three properties;
3. existence of trimmed cut points `0<a<=b<1/2`; and
4. a theorem that the same actual strict data on the compact middle `[a,b]` imply
   `SpeiserStrictNegativeHorizontal 10` by a complete left/middle/right split.

The registered endpoint is `exists_heightTen_compactMiddle_reduction`.

## Exact limitation

The cut points are classical continuity witnesses, not explicit rational values. Consequently
this checkpoint does not provide the finite rational middle cover required by the full top-edge
certificate. It proves that endpoint behavior is not an obstruction, while leaving quantitative
middle certification open.

The multiplicity-bearing low-zero count equality is independent and also remains open. No
`LevinsonMontgomeryHeightTenCertificate`, CountDichotomy, Speiser equivalence, H12, or RH is
claimed.

## Local audit

- The new module builds successfully as `8741/8741` jobs.
- The module, `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` pass
  `-DwarningAsError=true`.
- Three exact statement witnesses compile.
- The selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The project Lean-source scan finds no `sorry`, `admit`, or `native_decide`.
- The changed Lean files contain no `maxHeartbeats`, `maxRecDepth`, `axiom`, `opaque`, or
  `unsafe` declaration.
- `git diff --check` passes.
- Full `lake build` passes `8825/8825` jobs.

## Next producers

1. Add quantitative finite-center variation or Taylor-box bounds on the remaining compact
   middle, then kernel-check a finite rational cover.
2. Independently construct the actual multiplicity-bearing low-zero count equality below height
   ten, preferably through a one-dimensional boundary-winding certificate before a two-dimensional
   box cover.

The global RH Goal and parent campaign remain active.

## Public implementation

- Commit `cb466395ba6f9cd828497386090c7f0723a0a009` passed Lean Action run
  `30706556950`, build job `91386580043`, in `3m3s`.
- The new module, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, and `LeanLab.lean` are
  frozen by Git blob in
  `research/h14_h12_height_ten_boundary_neighborhood_evidence_20260801.md`.
- Documentation-only evidence commit `055ee2ff0cfd3afedd6a9227016f3d3c8e6ffade` passed Lean
  Action run `30706763852`, build job `91387115826`, in `1m43s`; all five frozen Lean blobs are
  unchanged.
