# H14 x H12 Height-Ten Actual Endpoint Evidence

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `MEANINGFUL_PARTIAL / IMPLEMENTATION_PUBLIC_GREEN /
IMMUTABLE_EVIDENCE_CI_PENDING / HEIGHT_TEN_CERTIFICATE_OPEN`

## Public implementation

- Commit: `3ed50eed1abefea20a810d39ce3ce89f2f61fe3a`
- Lean Action run: `30668355865`
- Build job: `91280491604`
- Result: passed in `2m50s`
- Local full build: `8824/8824`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenEndpoint.lean` | `74f411f9f2ab2597a164880ac5af2f1b608dcb22` |
| `LeanLab/Riemann/Targets.lean` | `506a66b68b699fb5f3fc9520cb36339cf3a8fdd8` |
| `LeanLab/Riemann/TargetChecks.lean` | `d63a5ad5428c8587a5e8fcc8ff46b2565857ed37` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `057f108ab9d393eccef5093fc8a5449191de6e14` |
| `LeanLab.lean` | `e7de68e538ff4c915e89dfa8c77a0c7ba934a1c9` |

This immutable-evidence change is documentation only. These five blobs must remain identical to
the public implementation commit.

## Immutable evidence

- Documentation-only commit: pending
- Lean Action run: pending
- Build job: pending
- Result: pending
- Blob check: pending

## Audited endpoints

1. `pi_lt_threeThousandOneHundredFortyTwo_div_oneThousand`
2. `log_pi_lt_twoHundredTwentyNine_div_twoHundred`
3. `heightTen_reflectedArchimedeanUpper_lt_neg_eleven_div_twentyFive`
4. `heightTen_eulerMaclaurinOneZetaError_lt_thirteen_div_twoHundredFifty`
5. `heightTen_eulerMaclaurinOneZetaDerivError_lt_eleven_div_fifty`
6. `neg_fiveHundredFortyNine_div_oneThousand_lt_eulerMaclaurinOne_finite_cross_re`
7. `speiserStrictNegativePoint_heightTenEndpoint`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies actual zeta and derivative nonvanishing and strict
`Re(zeta'/zeta)<0` at the single point `s=1/2+10i`. It does not prove a positive-width sigma
interval, a finite horizontal cover, the multiplicity-bearing low-zero count equality,
`LevinsonMontgomeryHeightTenCertificate`, CountDichotomy, Speiser equivalence, H12, or RH. The
campaign and global RH Goal remain active.
