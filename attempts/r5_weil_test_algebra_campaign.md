# R5 Weil Test Algebra Campaign

Campaign: `CAMPAIGN-20260715-R5-WEIL-TEST-ALGEBRA-01`

Date: 2026-07-15

Status: `CLOSED_KNOWN_THEOREM_FORMALIZED`

Route: R5, explicit formula and test-function positivity.

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | R1 sparse Gram and R3 Li are closed; R2 and R4 retain immediate RH-strength frontiers; R5 is the distinct unexhausted route. | Admit R5 source reconstruction. |
| 2 | `CONJECTURE_GENERATION` | Generated five candidates: full explicit formula, Li-special family, semi-local positivity, finite tests, and exact Weil test algebra. | Keep C1 and C5 for adversarial audit. |
| 3 | `ADVERSARIAL_TEST` | C1 is the correct but oversized frontier; C2 repeats R3; C3 is explicitly conjectural; C4 cannot transfer to the full class; C5 survives zero, endpoint, conjugation, critical-line, and divergence-convention tests. | Select C5 and preregister its exact endpoint. |
| 4 | `PROOF_ATTEMPT_A` | `WeilTestAlgebra.lean` proves positive-half-line involutivity, `M(f_tilde)(s)=M(f)(1-s)`, the `0/1` endpoint swap, conjugate-star covariance, and its critical-line specialization. | Endpoint compiles standalone. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | Audit found that a transform-value identity alone does not certify convergence under Mathlib's nonintegrable-integral convention. Added exact `MellinConvergent` iff theorems for the involution and star, plus a compiled counterexample at `x=0`. | Strengthen the batch without changing the source endpoint. |
| 6 | `INDEPENDENT_AUDIT` | Compared definitions and parameter directions against Lagarias (A.1)-(A.2) and (A.7), rechecked `1-conj(1/2+it)=1/2+it`, compiled exact target witnesses, and audited every new declaration. | Close as `KNOWN_THEOREM_FORMALIZED`; return to route selection. |

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_delta`: 0
- `assumption_frontier`: full explicit formula and unconditional Weil positivity
- `normalized_tuple`: recorded in
  `research/r5_weil_test_algebra_prereg_20260715.md`

No helper theorem counts as campaign closure. The campaign closes only when all preregistered
involution, Mellin covariance, endpoint-swap, conjugate-star, and critical-line statements pass the
verification gates together.

## Closure

Result: `KNOWN_THEOREM_FORMALIZED`

- `LeanLab/Riemann/WeilTestAlgebra.lean` compiles the complete preregistered endpoint.
- `mellinConvergent_weilInvolution_iff` and `mellinConvergent_weilStar_iff` ensure later test-space
  work cannot mistake the Bochner integral's nonintegrable-value convention for convergence.
- `weilInvolution_involution_not_at_zero` is the Lean-checked boundary counterexample that forces
  the pointwise theorem to remain on `0<x`.
- All selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Standalone compilation, exact target checks, the 8,662-job full build, all forbidden scans, and
  `git diff --check` pass locally.
- Implementation commit `24621330af4a24269a1748c5b3a4f924c16a7768` passed public Lean Action
  CI run `29409014307`, build job `87331366564`, in 2m27s.
- `hard_gap_before`: full R5 convolution/test class, explicit formula, density, and positivity.
- `hard_gap_after`: the exact involution/star and Mellin-convergence subedge is compiled; full
  convolution/test class, explicit formula, density, and positivity remain.
- `hard_gap_delta`: 0 for RH.
- `assumption_frontier_before`: complete explicit formula and unconditional Weil positivity.
- `assumption_frontier_after`: unchanged.

The mathematical campaign is closed; immutable evidence backfill and final clean synchronization
remain. The persistent RH goal stays active and returns to
`INDEPENDENT_AUDIT -> ROUTE_SELECTION`; a successor may not count algebraic wrappers around these
theorems as a new campaign.
