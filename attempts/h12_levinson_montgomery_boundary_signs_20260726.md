# H12 Levinson--Montgomery Boundary Signs and Integer-Height Dichotomy

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-BOUNDARY-SIGNS-01`

Selected node: `H12-LM-BOUNDARY-SIGNS-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`.
- `exact_mathematical_statement`: extend source equation `(2.1)` to both vertical boundaries,
  prove strict negativity of `Re(zeta'/zeta)` on `sigma=0` and on zero-free points of
  `sigma=1/2` for `t>=10`, and prove the exact integer-height alternative between cofinal
  negativity and eventual nonnegative interior witnesses.
- `relation_to_RH`: these are the boundary and dense-branch inputs in the
  Levinson--Montgomery proof of Speiser's criterion. The missing bottom certificate,
  indentation, and count theorem remain decisive.
- `success_criterion`: every exact closed-Gamma, closed-equation, paired-sign, boundary-sign,
  dichotomy, and dense-consumer endpoint plus all local and public gates.
- `falsification_criterion`: any exact Gamma, factorization, paired-sign, or totalized-logarithmic
  derivative mismatch.

## Prior state

- `parent_closed`: H12 log-derivative mass-bridge final-ledger commit
  `7e745ffb509fd425a965a6eed99e49c6a070464e`, public run `30192288017`, build job
  `89767603710`, passed in `1m30s`.
- `compiled_parent_edge`: actual paired sum `=Re(xi'/xi)`, explicit digamma remainder, equation
  `(2.1)`, archimedean negativity, nonnegative log derivative to negative paired mass, and the
  dense branch.
- `nearest_primary_source`: Levinson--Montgomery 1974, Theorem 1, paragraph following
  `(2.1)`--`(2.4)`.
- `new_attack_angle`: use Mathlib's generic Gamma differentiability away from negative integers
  and prove the boundary pair signs termwise over the actual xi divisor.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Verified the final ledger for the log-derivative mass bridge. | Commit `7e745ffb509fd425a965a6eed99e49c6a070464e` passed run `30192288017`, job `89767603710`, in `1m30s`. | Return the global Goal to route selection. |
| `CROSS_FAMILY_AUDIT` | Compared the nearest open H2, H11, H10, H7, H1, and H12 edges. | H2/H11 lack a published exception amplifier; H10 lacks the spectral object; H7 sources explicitly leave the uniform scalar inequality or nonlocal nodal theory open; H1 is at Farmer's open moment conjecture. | Select the adjacent H12 source paragraph. |
| `SOURCE_RECONSTRUCTION` | Re-read source pages 51--52 after equation `(2.4)`. | The proof separately uses left-boundary negativity, critical-line negativity plus indentations, and a top-height witness alternative. The bottom `t=10` edge depends on a low-zero certificate. | Split boundary signs and logic from numerical and contour count obligations. |
| `API_AUDIT` | Inspected paired kernels, equation `(2.1)`, GammaR, generic Gamma differentiability, xi-zero strip bounds, and the existing dense consumer. | Critical-line paired terms vanish termwise. Left-boundary kernels have the source sign. Mathlib supports Gamma differentiation away from poles, so the imaginary-axis extension has a concrete path. | Register Attacks A--C and indentation reconnaissance D. |
| `PREREGISTRATION_LOCAL` | Fixed exact endpoints, assumptions, source boundaries, falsifiers, and local stop before production proof edits. | Local docs complete; public CI is required. | Commit and push docs only. |
| `PREREGISTRATION_PUBLIC` | Published the docs-only preregistration. | Commit `a071e954c0433b072e16facba02b3a6f8647f391` passed run `30192787155`, build job `89768923636`, in `1m36s`. | Open production proof editing. |
| `PAIRED_BOUNDARY_SIGNS` | Evaluated the actual paired reciprocal terms at `sigma=0` and `sigma=1/2`. | The critical-boundary sum is zero termwise. On the left boundary, `0<beta<1` makes every paired kernel nonnegative and the reciprocal sum nonpositive. | Extend equation `(2.1)` to the closed region. |
| `GENERIC_GAMMA_NONPOLE` | Generalized GammaR differentiation, nonvanishing, and its logarithmic derivative from `Re(s)>0` to points outside the nonpositive even poles. | All generic non-pole identities compile with the same normalization as the open-half-plane formulas. | Reconstruct the xi/Gamma/zeta logarithmic derivative on the imaginary axis. |
| `CLOSED_EQUATION_2_1` | Used local nonvanishing of GammaR and the exact completed-zeta factorization to extend equation `(2.1)`. | `levinsonMontgomery_equation_two_one_closed` compiles on `0<=sigma<=1/2`, `t>=10`. | Combine with the paired signs and archimedean negativity. |
| `VERTICAL_BOUNDARY_SIGNS` | Proved xi has no imaginary-axis zero, transferred this to zeta, and combined closed `(2.1)` with both paired signs. | Strict negativity compiles on `sigma=0` and on every zero-free point of `sigma=1/2` for `t>=10`. | Formalize the exact top-height logical alternative. |
| `INTEGER_HEIGHT_DICHOTOMY` | Negated cofinal strict negativity while keeping zeta nonvanishing explicit in the predicate. | Eventual nonnegative zero-free witnesses compile and feed the existing dense branch. No totalized-log-derivative fake witness is admitted. | Run indentation reconnaissance. |
| `INDENTATION_RECONNAISSANCE` | Factored xi analytically at an actual zero, proved residual log-derivative continuity, and proved the multiplicity pole points strictly left. | These local components compile. Uniform whole-semicircle dominance is not claimed because the principal real part approaches zero near the two critical-line endpoints; endpoint/middle-arc gluing remains. | Retain the compiled local lemmas and audit the mandatory endpoint. |
| `LOCAL_AUDIT` | Registered one proven Target, nine mandatory TargetChecks, and selected axiom prints; ran warning-as-error checks, forbidden scans, patch check, and the full build. | The 426-line module passes. Selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`; full build passes `8766/8766`. | Freeze proof source and require public implementation CI. |
| `IMPLEMENTATION_PUBLIC` | Published the frozen proof implementation and registries. | Commit `d45e87b3c6ab9d41217f671b0dc96ec979167b45` passed public run `30193246131`, build job `89770129416`, in `2m7s`. | Keep proof source frozen and publish immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC` | Published the implementation run identifiers and exact claim boundary without changing proof source. | Docs-only commit `4c0ad75da06648c564fa58d9d29c762d46bff823` passed run `30193425500`, build job `89770603420`, in `1m34s`. | Publish one final ledger and require CI. |

## Final classification

- `result`: `FULL_BOUNDARY_SIGNS_AND_INTEGER_DICHOTOMY_SUCCESS`.
- `indentation_reconnaissance`: `LOCAL_FACTOR_AND_PRINCIPAL_SIGN_COMPILED`.
- `source_analytic_bridge_delta`: `1`.
- `historical_route_coverage_delta`: `1`.
- `known_theorem_formalization_delta`: `0` until the full Levinson--Montgomery theorem.
- `hard_gap_delta`: `0` for RH.
- `rh_frontier_delta`: `0`.
- `next_exact_H12_obstacle`: glue critical-line endpoint neighborhoods to a quantitatively
  dominated middle indentation arc, certify the bottom edge, and build the admissible count
  contour.
- `route_policy_after_closure`: return to cross-family historical `ROUTE_SELECTION`; conjecture
  and direct-proof tracks remain open.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: continued from the compacted live state, then verified the repository,
  governance, final parent closure, exact Lean APIs, Mathlib Gamma APIs, route logs, and primary
  source boundary paragraph before selection.
- `global_goal`: active.

## Current boundary

The two vertical boundary signs and exact integer-height dichotomy compile locally. The bottom
`t=10` zero certificate, whole-semicircle indentation, contour admissibility, exact count
equality, `O(log T)`, full Levinson--Montgomery theorem, Speiser equivalence, and RH remain open.
The six inherited user/exposure files remain untouched and unstaged. Frozen implementation
commit `d45e87b3c6ab9d41217f671b0dc96ec979167b45` passed public run `30193246131`, build job
`89770129416`, in `2m7s`. Docs-only immutable evidence
`4c0ad75da06648c564fa58d9d29c762d46bff823` passed run `30193425500`, build job
`89770603420`, in `1m34s`; one final-ledger CI remains.
