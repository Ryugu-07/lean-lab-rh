# H12 Levinson--Montgomery Log-Derivative to Paired-Mass Bridge

Date: 2026-07-26

Campaign:
`LITERATURE-20260726-H12-LEVINSON-MONTGOMERY-LOGDERIV-MASS-BRIDGE-01`

Selected node: `H12-LM-LOGDERIV-MASS-BRIDGE-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

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
| `PREREGISTRATION_PUBLIC` | Published the docs-only preregistration. | Commit `8a3c54d5092c13b8489e2c92c49d586f79176e95` passed run `30191371867`, build job `89765103953`, in `1m49s`. | Open production editing. |
| `HADAMARD_PAIR_CANCELLATION` | Reindexed the actual xi divisor by `rho -> 1-conj(rho)` and averaged the compensated Hadamard terms. | `levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re` compiles with no residual constant. | Differentiate the existing Stieltjes Gamma identity. |
| `STIELTJES_DIGAMMA` | Differentiated the scaled-Gamma equality, identified the explicit derivative kernel, and integrated the inverse-cube majorant. | `levinsonMontgomery_digamma_stirling` and the remainder bound `27/(64*norm(z)^2)` compile. | Reconstruct source equation `(2.1)` and close the sign estimate. |
| `SOURCE_EQUATION_2_1` | Took the logarithmic derivative of the actual xi pole/Gamma/zeta factorization and applied the digamma recurrence. | `levinsonMontgomery_equation_two_one` compiles over the actual paired sum. | Bound the nonzero archimedean term on the source region. |
| `ARCHIMEDEAN_SIGN` | Combined explicit pole, logarithm, inverse correction, and Stieltjes remainder estimates at `t>=10`. | `levinsonMontgomeryLogDerivArchimedeanTerm_neg` compiles for `0<=sigma<=1/2`. | Apply the paired-mass identity in the open strip. |
| `MASS_AND_COUNT_CONSUMER` | Combined `(2.1)`, strict archimedean negativity, the paired mass identity, and the existing integer-height count injection. | Both `levinsonMontgomeryPairedMass_neg_of_logDeriv_riemannZeta_re_nonneg` and `levinsonMontgomeryDenseBranch_of_eventuallyNonnegativeLogDerivAtIntegers` compile. | Register and audit the fixed endpoint. |
| `LOCAL_AUDIT` | Added the proven Target, seven exact TargetChecks, and seven selected axiom prints; ran direct warning-as-error checks, forbidden scans, patch check, and the full build. | The 615-line module and registries pass; selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`; the full build passes `8765/8765`. | Freeze the implementation and require public CI. |
| `IMPLEMENTATION_PUBLIC` | Published the frozen proof implementation and registries. | Commit `076b4e2023114c33fdf80cce123bc91c07d5c5a0` passed public run `30192061892`, build job `89766933675`, in `2m14s`. | Keep proof source frozen and publish immutable evidence. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: the compacted state was reloaded from governance, HANDOFF, active memory,
  the H12 parent attempt, hard-gap DAG, live repository status, exact Lean APIs, and the rendered
  primary source before selection.
- `global_goal`: active.

## Current boundary

The exact source identity, explicit Gamma remainder and sign bridge, paired-mass consequence,
and dense-branch consumer now compile locally. The low-height `t=10` zeta sign certificate,
lower/critical contour signs, existence of the interior nonnegative-log-derivative witness,
indented argument-principle count, `O(log T)` count difference, full Levinson--Montgomery
dichotomy, Speiser equivalence, and RH remain open.

The six inherited user/exposure files remain untouched and unstaged.
