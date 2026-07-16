# R5 Gaussian Prime-Kernel Sign Audit

Audit: `AUDIT-20260716-R5-GAUSSIAN-PRIME-KERNEL-SIGN-01`

Date: 2026-07-16

Status: `IMPLEMENTATION_CI_PASSED`

Mode: `DISCOVERY -> FALSIFICATION`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap; audit bounded by the fixed
  two-dimensional arithmetic-kernel endpoint
- `compaction_since_previous_campaign`: yes; work resumed from the preserved task summary,
  repository state, HANDOFF, Targets, attempts, route portfolio, and external ACTIVE ledger

## Normalized Tuple

- `statement`: the actual `n=2` symmetric Gaussian von-Mangoldt translation kernel is indefinite
  on one explicit two-shift family
- `assumptions`: existing direct Gaussian explicit formula definitions and standard Mathlib real
  exponential, logarithm, complex-power, and positive-semidefinite matrix facts
- `strategy`: choose width `(log 2)^2/16`, compare diagonal and `log 2` off-diagonal weights, and
  use exact two-coordinate quadratic witnesses for both signs
- `unresolved_frontier`: exact rewrite of the complex arithmetic weight and Lean verification of
  both strict matrix-sign witnesses

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `INDEPENDENT_AUDIT` | The compact Laplace separator campaign is fully closed with three independent public CI runs. W1c1 and W2/G7 remain open; M2/G3 remains parked. Repackaging the separator as another RH-equivalent reverse criterion would repeat the Gaussian strategy with zero hard-gap delta. | Rotate from LITERATURE to DISCOVERY and inspect arithmetic-kernel mechanisms. |
| 2 | `CONJECTURE_GENERATION_AND_ADVERSARIAL_SCREEN` | Five exact mechanisms were screened. Full fixed-width positivity is already RH-equivalent; local pole/prime semidefinite decompositions face two-point sign tests. The actual `n=2` prime kernel has an exact candidate witness with width `(log 2)^2/16` and shifts `0, log 2`. | Admit only the two-sided prime-kernel indefiniteness endpoint and begin Lean Falsification Attempt A. |
| 3 | `LEAN_FALSIFICATION_ATTEMPT_A` | Lean rewrites the existing complex von-Mangoldt weight to an exact real kernel, proves the witness width positive, computes the diagonal factor `exp(-4)` and off-diagonal factor `(1+exp(-16))/2`, and proves the latter is strictly larger. The vector `(1,-1)` gives a negative quadratic value while the diagonal is positive. | The actual `n=2` kernel and its negation both fail positive semidefiniteness; classify the termwise local-prime sign branch as eliminated. |
| 4 | `INDEPENDENT_LOCAL_AUDIT` | The 251-line module, exact Targets and TargetChecks, four standard-only axiom prints, forbidden/scratch/resource scans, `git diff --check`, aggregate import, and full 8,679-job build pass. | Local gate passed; publish the implementation and require independent public CI. |
| 5 | `IMPLEMENTATION_PUBLIC_CI` | Implementation commit `01ea63517670a81b8c640de1135dec62d44436b9` passed public Lean Action CI run `29462677629`, build job `87509304721`, in `1m54s`. | Backfill immutable evidence, publish it, and require the evidence commit's own CI before closure. |

Preregistration commit `672f965556fbd68f74e9c5e8d322e46b97db7fed` passed public Lean Action CI
run `29462185050`, build job `87507838744`, before the mathematical implementation was committed.

## Current Accounting

- `hard_gap_before`: G6/W1 open; G7/W2 open; G3/M2 parked
- `hard_gap_after`: unchanged; the termwise same-sign local-prime assembly branch is eliminated,
  while complete Weil positivity remains open
- `hard_gap_delta`: 0
- `assumption_frontier_before`: no unconditional positivity mechanism for the complete Weil form
- `assumption_frontier_after`: any unconditional G7 proof must use cancellation or a genuinely
  global operator/form identity; no same-sign semidefinite decomposition exists prime term by
  prime term for this Gaussian family
- `classification`: `BRANCH_ELIMINATED`
- `next_gate`: evidence-backfill publication and independent public CI

## Compiled Endpoint

`LeanLab/Riemann/WeilGaussianPrimeKernelSignAudit.lean` proves
`exists_pos_symmetricGaussianPrimeKernelMatrix_indefinite` with the exact preregistered arithmetic
kernel. No RH premise, project axiom, placeholder, numerical evaluator, or normalized surrogate is
used. The result does not determine the sign of the complete Weil arithmetic quadratic.
