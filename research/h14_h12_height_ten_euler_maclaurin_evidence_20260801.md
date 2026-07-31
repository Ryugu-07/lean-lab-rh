# H14 x H12 Height-Ten Euler--Maclaurin Evidence

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `MEANINGFUL_PARTIAL / IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
HEIGHT_TEN_CERTIFICATE_OPEN`

## Public implementation

- Commit: `f55f2efce7ae21e6fc0f78d677fecbb6606b526c`
- Lean Action run: `30661192482`
- Build job: `91257563206`
- Result: passed in `2m24s`
- Local full build: `8822/8822`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurin.lean` | `4858a9ac1f3a036df7b81026626d2c03b96b8e5b` |
| `LeanLab/Riemann/LevinsonMontgomeryTranscendentalInterval.lean` | `9f7eb4c944e482113976a65fc33cd777ec7aa1d0` |
| `LeanLab/Riemann/Targets.lean` | `788a6eb01b3c9709fde76203c874b971a1ead57d` |
| `LeanLab/Riemann/TargetChecks.lean` | `efbf5bf3be73c423cecdd1970aba716150b7953b` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `32fb78b01e6066e8b27d1bfc32be0cd967f80514` |
| `LeanLab.lean` | `b1dfe2e8e26b8a09d0bfbb3e4c5848685e851fd2` |

This immutable-evidence change is documentation only. These six blobs must remain identical to
the public implementation commit.

## Immutable evidence

- Documentation-only commit: `1e33d4a762301785e329bf6477a8152134efa734`
- Lean Action run: `30661486385`
- Build job: `91258507742`
- Result: passed in `1m35s`
- Blob check: all six frozen Lean blobs are unchanged from the public implementation commit

## Audited endpoints

1. `integral_abelCenteredFractKernel_eq_quadraticTail`
2. `riemannZeta_eq_eulerMaclaurinOneZetaApprox_add_remainder`
3. `norm_riemannZeta_sub_eulerMaclaurinOneZetaApprox_le`
4. `deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox`
5. `norm_deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox_le`
6. `speiserStrictNegativePoint_of_reflected_eulerMaclaurinOne_margins`
7. `abs_log_div_sub_logAtanhPartial_le`
8. `norm_complex_exp_sub_taylor_of_near`
9. `norm_ofReal_cpow_sub_taylor_of_log_near`
10. `abs_log_two_sub_logAtanhPartial_eight_le`
11. `norm_exp_heightTenScale_sub_taylor_eighty_le`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies actual-zeta one-correction Euler--Maclaurin value and derivative remainder
balls, a reflected finite-margin consumer, and generic proof-producing transcendental enclosures.
It does not certify the 30 generated finite-term enclosures, their aggregate margins, a uniform
height-ten cover, low-height multiplicity counts, `LevinsonMontgomeryHeightTenCertificate`, the
unconditional count dichotomy, Speiser equivalence, H12, or RH. The campaign and global RH Goal
remain active.
