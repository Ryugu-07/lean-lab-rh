# H14 x H12 Height-Ten Rotated-Slit Winding Evidence

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-POSITIVE-IMAGINARY-RAY-WINDING-01`

Classification: `ACTUAL_COUNT_CONSUMER / PUBLIC_IMPLEMENTATION_GREEN /
IMMUTABLE_EVIDENCE_PENDING / RH_FRONTIER_DELTA_0`

## Public implementation

- Commit: `8ec5dfba37d050dbcb0ac9889b3bc95f9cbf2253`
- Lean Action run: `30708752970`
- Build job: `91392334217`
- Result: passed in `2m51s`
- Local full build: `8826/8826`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenRotatedSlitWinding.lean` | `54d7c3a901339e6a74f80d09cd689d84a8403b78` |
| `LeanLab/Riemann/Targets.lean` | `2e8b014d2e520a81323efe4c1911a5c78bac2aa1` |
| `LeanLab/Riemann/TargetChecks.lean` | `5e269070191ab1d6afede20cc663539c0fd924f3` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `87b92d709a56dab3f9931a22903b7bc327bc4c88` |
| `LeanLab.lean` | `7aa25d2bcb93ca65b41312ccff6e88b14a39cb41` |

This immutable-evidence change is documentation only. These five blobs must remain identical to
the public implementation commit.

## Audited endpoints

1. `intervalIntegral_deriv_div_eq_log_sub_of_smul_mem_slitPlane`
2. `rectangleBoundaryIntegral_logDerivDifference_eq_zero_of_rotatedSlit`
3. `speiserUpperLeftCounts_eq_of_rotatedSlitBoundary`
4. `levinsonMontgomeryHeightTenCertificate_of_positiveImaginaryRayAvoidance`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies a generic actual-zeta consumer: a common rotated slit-plane branch on all
four source-rectangle edges implies exact multiplicity-count equality. It also certifies the
height-ten constructor from this boundary condition and the independent top-sign condition.

It does not prove `SpeiserRotatedSlitBoundary I 10`, the compact-middle top sign, the full
height-ten certificate, CountDichotomy, Speiser equivalence, H12, or RH. The campaign and global
RH Goal remain active.
