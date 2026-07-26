# H12 Levinson--Montgomery Boundary Signs and Integer-Height Dichotomy

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-BOUNDARY-SIGNS-01`

Selected node: `H12-LM-BOUNDARY-SIGNS-01`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

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

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: continued from the compacted live state, then verified the repository,
  governance, final parent closure, exact Lean APIs, Mathlib Gamma APIs, route logs, and primary
  source boundary paragraph before selection.
- `global_goal`: active.

## Current boundary

No production theorem is claimed yet. The six inherited user/exposure files remain untouched and
unstaged. The next gate is docs-only public preregistration CI.

