# H14 x H12 Height-Ten Reflected Evaluator Evidence

Date: 2026-08-01

Campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Classification: `MEANINGFUL_PARTIAL / PUBLIC_IMPLEMENTATION_GREEN /
HEIGHT_TEN_CERTIFICATE_OPEN`

## Public implementation

- Commit: `6f1b51b33304bffd756522c06dc36cfc79ecfd01`
- Lean Action run: `30656931596`
- Build job: `91243536693`
- Result: passed in `2m37s`
- Local full build: `8820/8820`

## Frozen Lean blobs

| file | Git blob |
| --- | --- |
| `LeanLab/Riemann/LevinsonMontgomeryHeightTenCertificate.lean` | `452b7b029715d53ca47b1e1350f088f393910363` |
| `LeanLab/Riemann/Targets.lean` | `d414921d54565e4a815d5484ab341c80b6994687` |
| `LeanLab/Riemann/TargetChecks.lean` | `8eb12b44fb60bf89daaa3807f4026c1c9056092a` |
| `LeanLab/Riemann/AxiomsAudit.lean` | `e3c519d840952396c21eeef91022379dd86e3878` |
| `LeanLab.lean` | `a1bb3e96f482474dae0e926d08799c706f4e0fda` |

The immutable-evidence commit is documentation only. These five blobs must remain identical to
the public implementation commit.

## Immutable evidence

- Documentation-only commit: `b691569b0c08277bf26debebe44670faf8ae6394`
- Lean Action run: `30657223620`
- Build job: `91244526442`
- Result: passed in `1m58s`
- Blob check: all five frozen Lean blobs are unchanged from the public implementation commit

## Audited endpoints

1. `hardyLittlewoodEtaFactor_ne_zero_of_re_lt_one`
2. `norm_deriv_hardyLittlewoodEta_sub_partialSum_le`
3. `norm_deriv_riemannZeta_sub_hardyLittlewoodZetaDerivApprox_le`
4. `logDeriv_riemannZeta_re_reflection`
5. `speiserStrictNegativePoint_of_reflected_hardyLittlewood_margins`

All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact claim boundary

The evidence certifies an actual-zeta reflected evaluator reduction. It does not certify the
finite transcendental margins, a uniform height-ten cover, the low-height multiplicity counts,
`LevinsonMontgomeryHeightTenCertificate`, the unconditional count dichotomy, Speiser equivalence,
H12, or RH. The campaign and global RH Goal remain active.
