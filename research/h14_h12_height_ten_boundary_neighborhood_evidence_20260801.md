# H14 x H12 Height-Ten Boundary Neighborhood Evidence

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-TWO-BOUNDARY-NEIGHBORHOODS-01`

Classification: `ACTUAL_TOPOLOGICAL_REDUCTION / IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
RH_FRONTIER_DELTA_0`

## Public implementation

- Commit: `cb466395ba6f9cd828497386090c7f0723a0a009`
- Lean Action run: `30706556950`
- Build job: `91386580043`
- Result: passed in `3m3s`
- Local full build: `8825/8825`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenBoundaryNeighborhood.lean` | `7dd8f4fa2b59653fde25ab564079a353bbb1b5ca` |
| `LeanLab/Riemann/Targets.lean` | `88e64d3a925d78ef92c2bf4edeb0559d741e5443` |
| `LeanLab/Riemann/TargetChecks.lean` | `37458e808c3c457b07f1b8465d402cc73078656a` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `dc84edf0920a5dabb73bc66b777e77bac7abdcfe` |
| `LeanLab.lean` | `6d79a45d6fca918e2a3693a9bf0fcfd6093c89bf` |

This immutable-evidence change is documentation only. These five blobs must remain identical to
the public implementation commit.

## Immutable evidence

- Documentation-only commit: `055ee2ff0cfd3afedd6a9227016f3d3c8e6ffade`
- Lean Action run: `30706763852`
- Build job: `91387115826`
- Result: passed in `1m43s`
- Blob check: all five frozen Lean blobs are unchanged from the public implementation commit

## Audited endpoints

1. `exists_heightTen_left_strictNegative_interval`
2. `exists_heightTen_right_strictNegative_interval`
3. `exists_heightTen_compactMiddle_reduction`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies actual positive-width strict-negative neighborhoods at both ends of the
height-ten horizontal and an exact reduction of the full top edge to an existential compact
middle. The cut points are not explicit rationals, so there is no finite replayable middle cover.

The actual multiplicity-bearing low-zero count equality, full height-ten certificate,
CountDichotomy, Speiser equivalence, H12, and RH remain open. The campaign and global RH Goal
remain active.
