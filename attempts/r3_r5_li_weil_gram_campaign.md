# R3/R5 Li-Weil Gram Campaign

Campaign: `CAMPAIGN-20260715-R3-R5-LI-WEIL-GRAM-01`

Date: 2026-07-15

Status: `CLOSED_KNOWN_THEOREM_FORMALIZED`

Route: R3/R5 bridge, Li coefficients as a Weil-positive test-function Gram form.

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | W1b is publicly complete, but W1c immediately requires conditional zero cutoffs, local Euler-factor terms, and regularization. The exact Li criterion is complete but lacks its source-level Weil Gram packaging. Lagarias Theorem 3.1 is a distinct cross-route edge. | Audit one Li-test Weil Gram campaign. |
| 2 | `CONJECTURE_GENERATION` | Generated five candidates: full W1c, finite-height covariance, a raw W1b Weil functional, a reflection-averaged Li Gram kernel, and a coefficient-defined Gram matrix. | Keep the reflection-averaged kernel and raw functional for attack. |
| 3 | `ADVERSARIAL_TEST` | Full W1c is too large; finite cutoffs do not reduce it; the raw W1b functional lacks a justified zero limit; a coefficient-defined kernel is circular. The reflection average cancels the nonsummable reciprocal term and reduces to compiled symmetrized Li terms. Real finite coefficients retain the diagonal reverse criterion and avoid an unproved complex Hermitian extension. | Select and preregister C4. |
| 4 | `PROOF_ATTEMPT_A` | Defined the reflection-averaged divisor kernel. The first Lean attempt exposed exactly the expected inverse-power and index-normalization failures; after explicitly normalizing `q^(m+1)=q^(n+1)q^(m-n)`, the pointwise identity compiled. Every kernel term reduces to two compiled symmetrized Li terms minus the distance term, so summability and the exact coefficient matrix follow without an unsymmetrized raw zero sum. Tests `(0,1)`, `(0,2)`, and the diagonal compile. | Continue to the full finite real span. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | Defined `liWeilCombination` and `liWeilQuadratic`. Proved finite double sums commute with the absolutely convergent divisor tsum. Under RH, `1-rho=conj(rho)` turns every finite integrand into `Complex.normSq`; the norm-square sequence is summable. A genuine `Finsupp.single n 1` recovers `2*Re(lambda_(n+1))`, yielding the exact quadratic positivity iff RH. | Fixed endpoint reached; do not extend to complex coefficients or W1c without a separate campaign. |
| 6 | `INDEPENDENT_AUDIT` | Rechecked the reflection average, multiplicity, source/project index shift, real-coefficient restriction, and reverse implication against Lagarias Theorem 3.1. Exact Targets include `(0,1)`, `(0,2)`, diagonal, norm-square, and iff statements. All 15 public axiom prints are standard-only; forbidden scans, `git diff --check`, standalone builds, and the 8,665-job full build pass. | Close as `KNOWN_THEOREM_FORMALIZED`; publication follows the fixed evidence sequence. |

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: the exact Li criterion has no compiled Weil Gram test-space interpretation
- `hard_gap_after`: the finite real Li-test Weil Gram criterion compiles; W1c and W2 remain
- `hard_gap_delta`: 0 for RH
- `assumption_frontier_before`: W1c explicit formula and W2 unconditional full-class positivity
- `assumption_frontier_after`: W1c explicit formula and W2 unconditional full-class positivity
- `normalized_tuple`: `research/r3_r5_li_weil_gram_prereg_20260715.md`

Kernel algebra, finite-sum interchange, and one-coordinate specialization are one indivisible
campaign and do not count as separate research loops.

## Public Result

Result: `KNOWN_THEOREM_FORMALIZED`

- `liWeilGramTerm_eq_symmetrized` performs the cancellation before tsum.
- `liWeilGram_eq_liCoefficients` gives the exact successor-indexed matrix and
  `liWeilGram_diagonal` gives `2 * liCoefficientCandidate n`.
- `RiemannHypothesis.liWeilQuadratic_eq_tsum_normSq` supplies the zero-side Gram interpretation,
  with separate summability proofs for both sides.
- `riemannHypothesis_iff_forall_liWeilQuadratic_nonneg` is the exact finite-real-span criterion.
- Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- Standalone compilation, exact targets, scans, `git diff --check`, and the 8,665-job full build
  pass locally and in public CI.

This theorem is knowingly equivalent to the already compiled Li criterion and does not prove
either side. Complex-coefficient Hermitian extension, W1c, W2, and RH remain open. The campaign
is publicly closed; only the final closure-log CI and clean synchronization check remain.

Implementation commit `2317143e73e1d788d65dcdff9b609a98f8ac60b2` passed public Lean Action CI
run `29415448733`, build job `87352327801`, in 1m48s. Evidence-backfill commit
`89fb947b493c8fd315bbe67a5be8c09fc99cdfa3` passed public Lean Action CI run `29415725269`, build
job `87353260131`, in 1m35s.
