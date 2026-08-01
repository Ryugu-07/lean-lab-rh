# H14 x H12 Height-Ten Boundary-Ray Producer Evidence

Date: 2026-08-02

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-BOUNDARY-RAY-PRODUCER-01`

Classification: `ACTUAL_BOTTOM_EDGE / HISTORICAL_EVALUATOR_REUSE /
PUBLIC_IMPLEMENTATION_GREEN / IMMUTABLE_EVIDENCE_PENDING / RH_FRONTIER_DELTA_0`

## Public implementation

- Commit: `82c2e991a22d0a21db318f9023941c7b2a764ff2`
- Lean Action run: `30711032719`
- Build job: `91398404697`
- Result: passed in `17m17s`
- Local full build: `8827/8827`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenBoundaryRayProducer.lean` | `6c3c0798e94fa0803d1f4fa609c1b375e7128d64` |
| `LeanLab/Riemann/ZetaConvexity.lean` | `ebefd041effb23bb79a7af28abb9891036c31247` |
| `LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurin.lean` | `31e9d56432ad0fb3ba928f6bfb8259f09aff35bc` |
| `LeanLab/Riemann/Targets.lean` | `0505e538074773e743235dbb2c19d51819532eb0` |
| `LeanLab/Riemann/TargetChecks.lean` | `5092eb9cf4ef99382fb9971762b195f9639031a8` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `9d391af6db0a4086f04529f1fb8b3801e969338d` |
| `LeanLab.lean` | `b10cd38bf58d3fab040aed2e197d01ef7cfd160a` |

This change is documentation only. These seven blobs must remain identical to the public
implementation commit. The immutable-evidence state becomes public green only after this record's
own Lean Action succeeds and all blob identities are replayed.

## Audited endpoints

1. `riemannZeta_eq_zetaPartialSum_sub_tail_of_re_pos`
2. `riemannZeta_eq_eulerMaclaurinOneZetaApprox_add_remainder_of_re_pos`
3. `norm_riemannZeta_sub_eulerMaclaurinOneZetaApprox_le_of_re_pos`
4. `deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox_of_re_pos`
5. `norm_deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox_le_of_re_pos`
6. `riemannZeta_realSegment_re_neg`
7. `deriv_riemannZeta_realSegment_re_neg`
8. `speiserZetaDerivRatio_realSegment_re_pos`
9. `speiserBottom_mem_rotatedSlit`
10. `SpeiserStrictNegativeHorizontal.toRotatedSlitBoundary_of_vertical`
11. `levinsonMontgomeryHeightTenCertificate_of_verticalRayAvoidance`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies actual zeta and derivative negativity on the complete real segment
`0<=sigma<=1/2`, actual quotient positivity there, and unconditional bottom rotated-slit
membership. It also certifies that the complete boundary and height-ten certificate follow from
the independent top sign plus exactly two vertical ray-avoidance clauses.

It does not prove either vertical clause, the compact-middle top sign,
`SpeiserRotatedSlitBoundary I 10`, the literal height-ten certificate, CountDichotomy, Speiser
equivalence, H12, or RH. The parent campaign and global RH Goal remain active.
