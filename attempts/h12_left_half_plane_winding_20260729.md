# H12 Levinson--Montgomery Left-Half-Plane Winding Attempt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01`

Node: `H12-LM-LEFT-HALF-PLANE-WINDING-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `FULL_SUCCESS_LOCAL / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Fixed target

Kernel-check the source inference from strict left-half-plane containment to zero logarithmic
winding, then instantiate its endpoint formula on an actual strict-negative horizontal
`zeta'/zeta` slice.

The full statement, negative control, and claim boundary are fixed in
`research/h12_left_half_plane_winding_prereg_20260729.md`.

## Attempt log

| phase | action | result | decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the actual modulo-seven Conrey flat-interval campaign. | Final ledger `5dab6664c49e5e03effe9ac309256eaf91e5a171` and closure receipt `fa3e22d4a8cf9dcd082eec3ef2d2d6b788b0d5ca` are public-green. | Return to forced cross-family route selection. |
| `CROSS_FAMILY_AUDIT` | Compared H9 main-family flat exclusion, H12 global counting, H7 spectral convergence, H10 number-field trace transfer, and the current H1/H2/H11 analytic frontiers. | H9 has a real new arithmetic distinction but no universal mechanism; H7/H10 require new infinite objects; H1/H2/H11 require global estimates. H12 has one exact printed inference separated by the previous winding falsification. | Select H12 left-half-plane winding. |
| `PRIMARY_SOURCE_RECHECK` | Re-read Levinson--Montgomery 1974 Theorem 1 and Section 2, especially page 52. | The source uses strict left-half-plane containment, not mere nonvanishing, to force zero change of argument before applying the argument principle. | Fix the principal-log endpoint theorem and actual horizontal ratio formula. |
| `REENTRY_DIFFERENCE` | Compared the target with `SpeiserAdmissibleContour.lean`. | The predecessor proves zero-free slices and a winding-one countermodel. It does not prove the positive left-half-plane theorem or the actual ratio derivative identity. | Re-entry is materially distinct. |
| `PREREGISTRATION_LOCAL` | Recorded theorem shapes, success/falsification criteria, negative control, and output boundary. | Docs only; no `LeanLab/` source changed. | Publish and require public CI before proof editing. |
| `PREREGISTRATION_PUBLIC_CI` | Published docs-only commit `a0f051cb09c8ef309cd9458e712adfcf1029851b`. | Lean Action run `30402375932`, build job `90420000555`, passed in `1m39s`. | Production gate satisfied; begin the fixed proof attempt. |
| `GENERIC_LOG_BRANCH` | Negated a strict-left path and used the principal complex logarithm on the slit plane. | Compiled the endpoint formula and its closed-path zero-integral corollary. | The positive counterpart to the inherited winding-one control is complete. |
| `ACTUAL_RATIO_DERIVATIVE` | Differentiated `deriv riemannZeta / riemannZeta` and restricted it to a real horizontal parameter. | Compiled the exact factorization by `logDeriv zeta' - logDeriv zeta`. The horizontal theorem requires `0 < t` to prove the point is not `1`. | Record the totalized-zeta boundary; do not weaken the analytic premise. |
| `ACTUAL_HORIZONTAL_ENDPOINT` | Combined the ratio derivative, inherited integrability, strict negativity, and the principal-log endpoint theorem. | Compiled the exact actual `zeta'/zeta` horizontal endpoint formula. | Register the aggregate target and exact checks. |
| `LOCAL_AUDIT` | Ran warning-as-error compiles, seven exact TargetChecks, seven selected axiom prints, three forbidden scans, `git diff --check`, and the full build. | All checks passed; selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`; full build completed `8789/8789`. | Freeze implementation and require public CI. |

## Current frontier

- `compiled_predecessor`: nonvanishing closed paths can have nonzero winding.
- `fixed_positive_edge`: strict left-half-plane paths have a principal-log primitive.
- `actual_instantiation`: horizontal `zeta'/zeta` derivative divided by the ratio equals
  `logDeriv zeta' - logDeriv zeta`.
- `first_later_global_edge`: finite indented contour assembly plus a multiplicity-aware argument
  principle.
- `separate_asymptotic_edge`: Jensen `O(log T)` top variation.
- `rh_frontier_delta`: `0`.
- `local_classification`: `FULL_SUCCESS_LOCAL`.
- `next_gate`: frozen implementation commit and public Lean Action CI.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary after H9 closure and re-read the governing
  and route-specific files before selecting this campaign.
- `global_goal`: active.
- `protected_files`: the inherited six protected files remain untouched and unstaged.
