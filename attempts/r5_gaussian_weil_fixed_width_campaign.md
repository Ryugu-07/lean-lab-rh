# R5 Gaussian-Weil Fixed-Width Campaign

Campaign: `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-FIXED-WIDTH-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes; work resumed from the preserved task summary,
  repository state, HANDOFF, Targets, attempts, and external ACTIVE checkpoints

## Normalized Tuple

- `statement`: for every fixed `a0>0`, RH iff all finite real Gaussian-Weil arithmetic
  quadratics at exactly width `a0` are nonnegative
- `assumptions`: the existing xi divisor, finite Gaussian packet explicit formula, all-width
  reverse criterion infrastructure, and standard Mathlib analysis only
- `strategy`: realize Gaussian width increase as a dominated limit of finite Rademacher/cosh
  multipliers that remain inside the fixed-width test algebra
- `unresolved_frontier`: publication and independent public CI

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP_AND_DISCOVERY` | Re-audited the existing Gaussian criterion. Its reverse proof uses widths tending to infinity to suppress every higher decay layer and phase-lock one off-line layer; positivity at one fixed width cannot be inserted directly. | Test whether the finite real shift algebra can itself approximate width increase. |
| 2 | `LITERATURE_AND_LIBRARY_AUDIT` | Targeted source searches found the general Weil criterion and Gaussian/distributional variants, but no exact one-fixed-width finite-translation theorem. Mathlib has finite-measure characteristic-function uniqueness but no packaged Bochner theorem or almost-periodic support API sufficient for the naive infinite-kernel proof. | Treat novelty as unresolved and avoid the Bochner/support route. |
| 3 | `ADVERSARIAL_MODEL_TEST` | Every finite symmetric off-line zero model violates fixed-width positive definiteness by exponential growth. The infinite divisor remains the real obstruction because it has no known maximal off-line real part and may exhibit cancellation. | Require a proof using the complete multiplicity-bearing divisor and an explicit summable majorant. |
| 4 | `CONJECTURE_GENERATION` | The finite exponential multiplier `A_n(z)=cosh(sqrt(c/n)*z)^n` remains in the allowed real shift algebra, while `A_n(z)A_n(-z)` converges to `exp(c*z^2)`. Since centered xi zeros have real part in `(-1/2,1/2)`, `norm(cosh u)<=exp((Re u)^2/2)` gives a height-independent bound and the base Gaussian supplies divisor summability. | Admit the exact fixed-width iff endpoint; begin Lean Proof Attempt A with the cosh limit and finite Rademacher realization. |
| 5 | `LEAN_PROOF_ATTEMPT_A_ANALYTIC_CORE` | Lean proves `n*(cosh(sqrt(c/n)*z)^2-1) -> c*z^2`, derives `cosh(sqrt(c/n)*z)^(2*n) -> exp(c*z^2)`, and realizes each `cosh` power exactly as a finite Rademacher exponential sum. The tensor product with an arbitrary finite real packet stays inside the fixed-width test class. | Continue to the complete divisor rather than closing at the finite identity. |
| 6 | `LEAN_PROOF_ATTEMPT_A_DOMINATED_TRANSFER` | Lean proves `norm(cosh z) <= exp(z.re^2/2)`, bounds every centered xi-zero multiplier by `exp(c)`, and applies `tendsto_tsum_of_dominated_convergence` using the summable base-width Gaussian packet. It transfers any negative larger-width arithmetic quadratic to a finite negative quadratic at exactly `a0`. | Strengthen the existing off-line separator to exceed any prescribed width threshold. |
| 7 | `LEAN_PROOF_ATTEMPT_A_ENDPOINT` | Lean compiles the threshold-strengthened off-line negativity theorem, the contradiction from fixed-width positivity, and the exact preregistered iff. Targets and exact type witnesses compile; five transitive axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`. | Mark the proof locally complete and run repository-wide hygiene/build verification before publication. |
| 8 | `INDEPENDENT_LOCAL_AUDIT` | The standalone formal module cold-compiles without diagnostics. Repository-wide Lean scans find no `sorry`, `admit`, `native_decide`, added `axiom`/`constant`, or `unsafe`; the changed integration files contain no scratch names or resource-limit relaxation. `git diff --check` and the full 8,677-job build pass. | Close locally as verified; publish the implementation and require independent public CI before external use. |
| 9 | `PUBLIC_CI_IMPLEMENTATION` | Implementation commit `f56b70478ab552802cac719b8e9af0f56fc44b1d` passed public Lean Action CI run `29458594435`, build job `87497146736`, in `2m15s`. | Publish the immutable evidence backfill and require that commit's own public CI before campaign closure. |

## Current Accounting

- `hard_gap_before`: every positive Gaussian width is quantified in the compiled RH criterion
- `hard_gap_after`: one arbitrary preassigned positive width suffices
- `hard_gap_delta`: 0 for unconditional RH, W2, and G7
- `assumption_frontier_before`: no finite-test width-increase closure theorem
- `assumption_frontier_after`: finite real Gaussian tests at one base width are proved closed under
  larger-width transfer through a dominated finite Rademacher approximation
- `classification`: `NEW_RELEVANT_LEAN_THEOREM` pending independent novelty review and public CI
- `next_gate`: evidence-backfill commit and its independent public GitHub Actions result
