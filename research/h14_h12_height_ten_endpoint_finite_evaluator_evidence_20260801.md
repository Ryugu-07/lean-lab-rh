# H14 x H12 Height-Ten Endpoint Finite Evaluator Evidence

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `MEANINGFUL_PARTIAL / PUBLIC_IMPLEMENTATION_GREEN /
IMMUTABLE_EVIDENCE_CI_PENDING / HEIGHT_TEN_CERTIFICATE_OPEN`

## Public implementation

- Commit: `9f3d28f7e4c1dbbf7647c8cd1418b50a7c34d656`
- Lean Action run: `30665506516`
- Build job: `91271458715`
- Result: passed in `6m19s`
- Local full build: `8823/8823`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryEulerMaclaurin.lean` | `594930a0f5ed3fb770553083116abb296e6c3d4e` |
| `LeanLab/Riemann/LevinsonMontgomeryTranscendentalInterval.lean` | `3070a3276a77de50be1e58d8da3a46a6a1d07b13` |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenFiniteEvaluator.lean` | `ac8ee159807bd5fd8695056fbb16131c4f4a5ec5` |
| `LeanLab/Riemann/Targets.lean` | `6df48c8740590c34b50ed518f899eb541458bffe` |
| `LeanLab/Riemann/TargetChecks.lean` | `578be0786184ed458eabc8a960ff4f511d28a7c1` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `92a5a9bdad56f710309cffaa2d324c128de98edb` |
| `LeanLab.lean` | `bf7bcfbb45be3955ff9cd7fd8627129d12cd5d5c` |

This immutable-evidence change is documentation only. These seven blobs must remain identical to
the public implementation commit.

## Audited endpoints

1. `norm_pow_sub_pow_le_of_norm_le`
2. `norm_ofReal_cpow_sub_binaryScaledCpowCenter_le`
3. `eulerMaclaurinOneZetaDerivApprox_eq_finiteFormula`
4. `norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le`
5. `norm_zetaPartialSum_reflectedEndpoint_sub_rounded_le`
6. `norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_sub_rounded_le`
7. `norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_sub_rounded_le`
8. `eulerMaclaurinOne_finite_cross_re_lt_neg_fiftyThree_div_oneHundred`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies all thirty finite complex-power enclosures and the complete finite value
and derivative margins at the reflected critical endpoint. It does not combine the analytic
Euler--Maclaurin remainder or reflected archimedean bound, prove the actual-zeta endpoint sign,
give a positive-width sigma cover, establish low-height multiplicity counts,
`LevinsonMontgomeryHeightTenCertificate`, the unconditional count dichotomy, Speiser equivalence,
H12, or RH. The campaign and global RH Goal remain active.
