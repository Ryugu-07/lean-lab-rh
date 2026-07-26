# H12 Levinson--Montgomery Critical-Zero Indentation

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-CRITICAL-INDENTATION-01`

Selected node: `H12-LM-CRITICAL-INDENTATION-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`.
- `exact_mathematical_statement`: every critical-line xi zero strictly above height `10` has a
  punctured left half-neighborhood on which zeta is nonzero and
  `Re(zeta'/zeta)<0`; hence it admits a complete negative left semicircle indentation.
- `relation_to_RH`: this is the critical-boundary indentation used in the
  Levinson--Montgomery count proof of Speiser's criterion. The bottom edge, admissible top
  contours, argument principle, count comparison, and unconditional derivative-zero exclusion
  remain open.
- `success_criterion`: both exact neighborhood and semicircle endpoints plus all local and public
  gates.
- `falsification_criterion`: an exact residual-sign mismatch, totalized-log-derivative leak, or
  endpoint-gluing obstruction.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Verified the boundary-sign final ledger. | Commit `53f781929605243e05dcec36bb188afb1b0c50a5` passed run `30193513376`, job `89770844367`, in `1m51s`. | Return the global Goal to route selection. |
| `CROSS_FAMILY_AUDIT` | Compared H1, H2/H11, H7/H10, D9, and the next H12 source paragraph. | H1 is at an open arbitrary-length moment; H2/H11 lack an actual sparse-exception amplifier; H7/H10 lack the number-field object; D9 needs actual high-point-value or universality certification. H12 retains a literal published edge with compiled local factors. | Select the critical-zero indentation. |
| `SOURCE_RECONSTRUCTION` | Re-read Levinson--Montgomery page 52 and inspected the source semicircle sentence. | Principal-pole dominance is clear on the strict middle arc, but its real part vanishes at the critical-line endpoints. The parent boundary theorem supplies endpoint signs, while a normalized residual theorem may give the stronger whole half-disk result. | Register the residual-continuity attack and endpoint-gluing fallback. |
| `PREREGISTRATION_LOCAL` | Fixed actual-zeta endpoints, assumptions, falsifiers, source boundary, and local stop before proof edits. | Docs-only preregistration is complete. | Publish and require public CI before production editing. |
| `PREREGISTRATION_PUBLIC` | Published commit `54b5eabdf46acf44878db80cf2e38657f7fb7378`. | Public run `30193955050`, build job `89772029846`, passed in `1m35s`. | Open the fixed production gate. |
| `ATTACK_B_XI_RESIDUAL` | Transported the local xi factor through `z -> 1-conj(z)` and differentiated the resulting analytic-unit identity at the critical-line center. | `levinsonMontgomery_zeroFactor_logDeriv_re_eq_zero` compiles; the exact xi unit residual has zero real logarithmic derivative at the center. No value of totalized `logDeriv riemannXi rho` is used as limit evidence. | Divide by the analytic completed-zeta unit. |
| `ATTACK_C_ZETA_RESIDUAL` | Factored actual zeta locally and subtracted the xi/zeta unit logarithmic derivative. | `exists_riemannZeta_critical_zero_analytic_factor` compiles with positive exact multiplicity and strictly negative center residual. | Extend the strict residual sign by continuity. |
| `ATTACK_C_HALF_NEIGHBORHOOD` | Combined residual continuity with nonvanishing of the analytic unit and the nonpositive real part of `m/(z-rho)` on the closed left side. | `exists_levinsonMontgomery_critical_zero_left_neighborhood` compiles and is stronger than the source semicircle. | Extract a positive-radius semicircle. |
| `GEOMETRIC_ENDPOINT` | Chose half the neighborhood radius. | `exists_levinsonMontgomery_negative_left_semicircle` compiles for the complete closed left semicircle, including both critical-line endpoints. | Register the result and run all local gates. |
| `LOCAL_GATES` | Ran warning-as-error, Target, six TargetChecks, five selected axiom prints, three forbidden scans, `git diff --check`, and full build. | New module has no diagnostics; axioms are only `propext`, `Classical.choice`, `Quot.sound`; scans are empty; full build is `8767/8767`. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC` | Published frozen implementation commit `49d43eda415c00c10939c2df529b6231c973aa5b`. | Public run `30195029807`, build job `89774903553`, passed in `2m44s`. | Keep proof source frozen; publish docs-only immutable evidence. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: continued from a compacted live state, then re-read governance, HANDOFF,
  the live DAG, parent proof and attempt files, cross-family route cards, the Conrey--Li TeX
  source, and rendered Levinson--Montgomery source pages 51--52 before selection.
- `global_goal`: active.

## Current boundary

Result is `FULL_CRITICAL_INDENTATION_SUCCESS` with a public-green frozen implementation.
Immutable-evidence and final-ledger public CI remain before fixed-campaign closure. This closes
the local critical-zero indentation edge only. The bottom `t=10` certificate, cofinal admissible
top contours, global indented argument-principle bookkeeping, exact count equality, `O(log T)`,
full Levinson--Montgomery theorem, Speiser equivalence, and RH remain open. The six inherited
user/exposure files remain untouched and unstaged.
