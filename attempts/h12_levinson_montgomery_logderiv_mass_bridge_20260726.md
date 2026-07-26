# H12 Levinson--Montgomery Log-Derivative to Paired-Mass Bridge

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-LOGDERIV-MASS-BRIDGE-01`

Selected node: `H12-LM-LOGDERIV-MASS-BRIDGE-01`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / PROOF-ATTEMPT`.
- `exact_mathematical_statement`: prove source equation `(2.1)` over the actual paired xi
  divisor, prove the explicit Stieltjes digamma remainder and its sign consequence for
  `0<=sigma<=1/2, t>=10`, and derive negative paired mass from a nonnegative real zeta
  logarithmic derivative.
- `relation_to_RH`: this is the analytic input to the dense branch in the
  Levinson--Montgomery proof of Speiser's criterion. It neither supplies the source contour
  witness nor proves RH.
- `success_criterion`: all exact equation, Gamma, sign, mass, and dense-consumer endpoints plus
  all local and public proof gates.
- `falsification_criterion`: any exact normalization, remainder-strength, threshold, or source
  boundary mismatch.

## Prior state

- `parent_closed`: H12 paired-mass final-ledger commit
  `69774e9d4d7b96590d48acd8ad5f6f9b152f0dc2`, public run `30190977973`, build job
  `89764077666`, passed in `1m47s`.
- `compiled_parent_edge`: the paired reciprocal identity, negative-mass half-unit upper-left
  zero localizer, and eventual `N^-(T)>T/2` branch.
- `nearest_primary_source`: Levinson--Montgomery 1974, Theorem 1, equations `(2.1)`--`(2.4)`.
- `new_attack_angle`: identify the compiled paired sum with `Re(xi'/xi)` by Hadamard
  cancellation and derive the digamma bound from the project's already compiled differentiable
  Stieltjes remainder instead of assuming a new Gamma estimate.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Verified the final ledger for the paired-mass density campaign. | Commit `69774e9d4d7b96590d48acd8ad5f6f9b152f0dc2` passed run `30190977973`, job `89764077666`, in `1m47s`. | Return the global Goal to route selection. |
| `ROUTE_SELECTION` | Compared H12 with H1 mollifiers, H7/H10 spectral and function-field transfer, H2 density, and H11 zero statistics. | H1 is at Farmer's open moment conjecture; H7/H10 need a new positivity/spectral object; H2/H11 need a sparse-exception amplifier. H12 retains an adjacent published theorem edge with compiled inputs. | Select equation `(2.1)` and explicit Gamma control. |
| `SOURCE_RECONSTRUCTION` | Re-read source pages 51--52 and equations `(2.1)`--`(2.4)`. | The exact implication needed for the dense branch is `Re(zeta'/zeta)>=0 -> I1<0`, once the nonzero term `A(s)` is strictly negative. | Separate this bridge from the later low-height and contour certificate. |
| `API_AUDIT` | Inspected the paired-mass module, Li Hadamard cancellation, xi/zeta factorization, digamma recurrence, and the Stieltjes scaled-Gamma module. | All algebraic objects exist. The Stieltjes remainder is differentiable under its integral, and radial inverse-cube bounds can produce an explicit `O(norm(z)^-2)` remainder without a new premise. | Register direct Hadamard/Stieltjes Attack A and derivative-cancellation fallback B. |
| `PREREGISTRATION_LOCAL` | Fixed exact endpoints, thresholds, assumption frontier, source boundaries, and stop conditions before any Lean proof edit. | Local docs complete; public CI is required. | Commit and push docs only. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: the compacted state was reloaded from governance, HANDOFF, active memory,
  the H12 parent attempt, hard-gap DAG, live repository status, exact Lean APIs, and the rendered
  primary source before selection.
- `global_goal`: active.

## Current boundary

No production Lean source has been created or edited. The low-height `t=10` zeta sign
certificate, lower/critical contour signs, indented argument-principle count, `O(log T)` count
difference, full Levinson--Montgomery dichotomy, Speiser equivalence, and RH remain open.

The six inherited user/exposure files remain untouched and unstaged.
