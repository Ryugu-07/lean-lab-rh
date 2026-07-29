# H2 Classical Detector Contour-Shift Attempts

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Node: `H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01`

Status: `FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_CI_PENDING`

## Fixed question

Can the actual classical zero-detector inverse-Mellin line be shifted across its one retained
translated-zeta pole, with the Gamma pole at zero removed by the actual zeta-zero condition and
both horizontal edges discharged by compiled Gamma and zeta estimates?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | The closed H1 Abel-transfer identifies a new broad oscillatory producer. H7/H8 and H10 still need global objects, while H11 lacks a sparse-exception amplifier. H2 has one exact historical inference between two compiled parts of the detector. | Re-enter H2 at the infinite contour shift, not at another local residue or inverse-line lemma. |
| 2 | `SOURCE_RECHECK` | Maynard--Pratt Appendix C shifts from the original inverse-Mellin line to `Re(w)=1/2-beta`, crosses only `w=1-rho`, and uses `zeta(rho)=0` to cancel the Gamma pole at zero. | Preserve the literal left line and residue. Keep the later dyadic Type-I/Type-II bounds outside the fixed endpoint. |
| 3 | `SINGULARITY_AUDIT` | The existing `classicalDetectorCancelledGammaZeta` removes `w=0` locally, but the rectangle proof is cleaner after multiplying by `(rho+w-1)` through `zetaPoleRemoved`. A second `dslope` at `rho` yields a numerator holomorphic on `Re(w)>-1`. | Use `P(w)/(w-(1-rho))`; prove source equality away from both exceptional points and evaluate `P(1-rho)` exactly. |
| 4 | `LIBRARY_AUDIT` | `WeilZeroCutoff` supplies weighted-Cauchy rectangle calculus; `BettinGonekInverseMellinConvolution` supplies finite-strip horizontal-limit patterns; `BaezDuarteZetaRatio` and the exact half-line Gamma norm supply exponential decay after polynomial losses; `ReciprocalZetaSubpower` supplies linear zeta growth on the required strip. | Preregister the unconditional actual-factor contour theorem. No abstract contour-shift premise is allowed. |
| 5 | `FEASIBILITY_BOUNDARY` | The right line is in the absolute Dirichlet-series region. The shifted line has `Re(rho+w)=1/2` and `-1/2<Re(w)<0`, so Gamma recurrence moves to a positive strip and contributes a harmless reciprocal factor away from zero. | Require actual integrability on both lines and uniform horizontal decay; Gamma integrability alone is an explicit negative control. |
| 6 | `PREREGISTRATION` | Full, partial, falsification, singularity, normalization, and claim-boundary criteria are fixed. | Publish docs only and await public CI before editing `LeanLab/`. |
| 7 | `PUBLIC_GATE` | Docs-only commit `c82a77039e939d904038de1c39625bef50ea9dd3` passed Lean Action run `30482171994`, build job `90678758000`, in `2m12s`. | Open the production gate without changing the frozen endpoint. |
| 8 | `SINGULARITY_AND_RESIDUE` | The source factor is represented by `P(w)/(w-(1-rho))`. The actual zero removes `w=0` with no simplicity premise, and `P(1-rho)` compiles to the exact source residue. | Count only `w=1-rho` in the rectangle. |
| 9 | `HORIZONTAL_DECAY` | Finite mollifier growth, complex-power control, zeta strip growth, Gamma recurrence, and exponential Gamma decay combine into a uniform fixed-strip majorant. Both horizontal interval integrals tend to zero. | The local residue can now be promoted beyond a finite rectangle. |
| 10 | `VERTICAL_INTEGRABILITY` | The actual contour factor is integrable on `Re(w)=2` and on `Re(w)=1/2-Re(rho)`. On the left, `beta>1/2` keeps the line strictly left of the canceled point and Gamma recurrence supplies an integrable inverse-square majorant. | Preserve the source's strict off-line hypothesis for the shifted raw line. |
| 11 | `FINITE_RECTANGLE` | Weighted Cauchy calculus gives the oriented finite rectangle identity with exactly one pole and the exact `2*pi*i` normalization. | Pass to infinite height using the compiled edge limits and line integrability. |
| 12 | `INFINITE_SHIFT` | `classicalDetectorMellinLineIntegral_two_eq_residue_add_shifted` proves the actual source line shift. Composing with inverse Mellin proves `classicalDetectorSmoothedSeries_eq_residue_add_shifted`. | Close the fixed historical inference; do not infer a density estimate. |
| 13 | `COEFFICIENT_GAP` | Absolute summability for `Re(z)>0` permits an exact head/tail split. For `M>=1`, `classicalDetectorCoefficientGap_shifted_identity` exposes the source gap before the dyadic decomposition. | Name the dyadic Type-I/Type-II block estimates as the strict successor. |
| 14 | `LOCAL_AUDIT` | The 1305-line module, Targets, TargetChecks, AxiomsAudit, and root import pass warning-as-error. Seven selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden/resource scans and `git diff --check` are empty; full build succeeds with `8802/8802`. | Freeze and publish the implementation before creating immutable evidence. |
| 15 | `PUBLIC_IMPLEMENTATION` | Frozen commit `b87e9164395b14723f61d8451e3ed1b0cd0ae1c8` passed Lean Action run `30484701769`, build job `90687338466`, in `2m39s`. The five proof and registration files have an empty diff from the frozen commit. | Publish immutable evidence as a docs-only commit and require a fresh public-green run. |
| 16 | `IMMUTABLE_EVIDENCE` | Docs-only commit `1cc20bca2455d9eb9ca27a0e42fbaf86b340b4e8` passed Lean Action run `30485116278`, build job `90688732121`, in `1m36s`. The frozen proof diff remains empty. | Publish the final ledger and require public CI before issuing the closure receipt. |
| 17 | `FINAL_LEDGER` | Docs-only commit `8ab5c9f0fcf187a240ad3bb371e14f788e127997` passed Lean Action run `30485360308`, build job `90689557179`, in `2m13s`. The frozen proof diff remains empty. | Publish one closure receipt and require public CI, then stop only this campaign. |

## Current frontier

- `selected_edge`: closed locally as
  `classicalDetectorContourShift_endpoint`.
- `compiled_left_context`: coefficient gap, source product, local singularity calculations,
  inverse Mellin line, and generic finite detector.
- `strict_successor`: source dyadic decomposition and quantitative block/tail estimates leading
  to a zero-density dichotomy.
- `local_classification`: `FULL_SUCCESS / KNOWN_CONTOUR_SHIFT_FORMALIZED`.
- `current_gate`: closure-receipt docs-only commit and public Lean Action.
- `not_claimed`: density exponent, exclusion of all off-line zeros, H2, or RH.
- `protected_files`: inherited modified and untracked files remain untouched and unstaged.
- `global_goal`: active.
