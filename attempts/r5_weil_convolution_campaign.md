# R5 Weil Convolution Campaign

Campaign: `CAMPAIGN-20260715-R5-WEIL-CONVOLUTION-01`

Date: 2026-07-15

Status: `CLOSED_KNOWN_THEOREM_FORMALIZED`

Route: R5, explicit formula and test-function positivity.

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | R1's sparse branch is closed negatively; R2's first positive edge is RH-hard; R3's Li equivalence is complete; R4 still lacks an honest operator/spectrum bridge; R5 has the exact open W1 convolution/formula edge. | Audit whether new evidence permits one same-route successor. |
| 2 | `CONJECTURE_GENERATION` | Generated five candidates: full explicit formula, full `A_delta` algebra, generic convergent Mellin convolution, compact-smooth subclass, and a direct zero-sum quadratic form. | Keep the generic convolution and full test class for attack. |
| 3 | `ADVERSARIAL_TEST` | The full class is dependency-inverted before a product theorem; compact support is too narrow; a direct zero sum bypasses W1; the generic theorem survives Jacobian, direction, conjugation, critical-line, and nonintegrable-integral tests only with explicit convergence hypotheses. | Select and preregister C3 as one indivisible endpoint. |
| 4 | `PROOF_ATTEMPT_A` | `WeilConvolution.lean` transports the exact `dy/y` convolution through `x=exp(-w)`, proves the logarithmic lift is Mathlib additive convolution, and applies Bochner Fubini to close both convergence and the Mellin product. | The complete preregistered endpoint compiles standalone. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | Reattacked the nonintegrable convention and star parameter. The proof uses the two exact convergence hypotheses before Fubini; star convergence is obtained by the prior iff, and the self-star specialization compiles to `normSq`. | Strengthen the consumer endpoint without adding an assumption. |
| 6 | `INDEPENDENT_AUDIT` | Compared the `dy/y`, `w-u`, `1-conj(s)`, and critical-line directions against Lagarias (A.7); exact target witnesses, all public axiom outputs, scans, and the 8,663-job full build pass. | Close W1a as `KNOWN_THEOREM_FORMALIZED`; W1b-W1c remain open. |

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: W1 lacks convolution and the complete explicit formula
- `hard_gap_after`: W1a convolution/Mellin product is complete; W1b test class and W1c explicit formula remain
- `hard_gap_delta`: 0 for RH
- `assumption_frontier_before`: complete explicit formula and unconditional Weil positivity
- `assumption_frontier_after`: unchanged
- `normalized_tuple`: `research/r5_weil_convolution_prereg_20260715.md`

Helper change-of-variable, Fubini, or integrability lemmas remain one engineering batch and do not
count as separate loops.

## Closure

Result: `KNOWN_THEOREM_FORMALIZED`

- `mellinConvergent_iff_integrable_mellinLogLift` records the exact logarithmic-coordinate
  convergence equivalence.
- `mellinLogLift_weilConvolution` identifies physical multiplicative convolution with Mathlib's
  additive Bochner convolution.
- `mellinConvergent_weilConvolution` proves closure under the two exact pointwise convergence
  assumptions; no compact-support, continuity, or strip-analyticity premise is inserted.
- `mellin_weilConvolution` proves the Mellin product, and the star theorems recover the exact
  `1-conj(s)` parameter and the critical-line Hermitian product.
- `mellin_weilAutocorrelation_criticalLine` compiles the self-star value to `Complex.normSq`.
- Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Standalone compilation, exact targets, scans, `git diff --check`, and the 8,663-job full build
  pass locally.

This closes only W1a. It does not package Lagarias's analytic-strip `A_delta`, define the Weil
distribution, prove any zero/prime/pole/archimedean explicit formula, or establish positivity. RH
and the persistent global goal remain unchanged.
