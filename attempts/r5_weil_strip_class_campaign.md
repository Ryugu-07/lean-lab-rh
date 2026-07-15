# R5 Weil Strip Class Campaign

Campaign: `CAMPAIGN-20260715-R5-WEIL-STRIP-CLASS-01`

Date: 2026-07-15

Status: `IMPLEMENTATION_PUBLICLY_VERIFIED`

Route: R5, explicit formula and test-function positivity.

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | W1a is publicly closed; R1 sparse is negatively closed, R2's next edge is RH-hard, R3 Li is complete, and R4 still lacks a spectrum bridge. Lagarias's `A_delta` class is the exact new W1b edge. | Audit one same-route source-class successor. |
| 2 | `CONJECTURE_GENERATION` | Generated five candidates: complete metric `A_delta`, a physical strip predicate, compact-smooth functions, transform-only analytic functions, and a critical-line-only class. | Keep the physical predicate and complete metric formulations for attack. |
| 3 | `ADVERSARIAL_TEST` | Raw-function uniform distance need not separate points and completeness needs Mellin uniqueness/inversion; compact and line-only classes are too narrow; transform-only closure loses the physical representative. The explicit physical predicate survives strip, convergence, boundedness, star-analyticity, and convolution tests. | Select and preregister C2; defer quotient/completeness honestly. |
| 4 | `PROOF_ATTEMPT_A` | Defined the exact open and closed strips and proved invariance under `1-s`, `conj(s)`, and `1-conj(s)`. Packaged positive width, pointwise closed-strip Mellin convergence, open-strip analyticity, closed-strip continuity, and an explicit finite uniform bound. Zero, addition, scalar multiplication, and Weil involution closure compile. Pointwise function addition/scalar goals required explicit lambda `change` steps; no mathematical assumption changed. | Continue to the anti-holomorphic and convolution cases. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | Proved conjugation closure by deriving differentiability of `conj o mellin(f) o conj`; the two conjugations cancel anti-holomorphicity. Derived `weilStar` closure, then used W1a's exact Mellin convergence/product laws for convolution analyticity, continuity, the `C*D` bound, and autocorrelation closure. | Endpoint reached without inversion, uniqueness, completeness, or density premises. |
| 6 | `INDEPENDENT_AUDIT` | Checked the source-facing fields against the preregistered endpoint and attacked the vacuous-strip, nonintegrable-value, conjugation, and product-bound failure modes. Standalone compilation, exact target witnesses, all 16 public axiom prints, empty forbidden/declaration/resource scans, `git diff --check`, and the 8,664-job full build pass. | Close locally as `KNOWN_THEOREM_FORMALIZED`; public CI remains. |

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: W1b has no source-faithful compiled physical strip algebra
- `hard_gap_after`: W1b's physical analytic-strip algebra core compiles; quotient/uniqueness/completeness, density, W1c, and W2 remain
- `hard_gap_delta`: 0 for RH
- `assumption_frontier_before`: complete explicit formula and unconditional Weil positivity
- `assumption_frontier_after`: complete explicit formula and unconditional Weil positivity
- `normalized_tuple`: `research/r5_weil_strip_class_prereg_20260715.md`

Strip geometry, analytic congruence, and closure helpers remain one engineering batch and do not
count as separate research loops.

## Local Result

`LeanLab/Riemann/WeilStripClass.lean` proves the fixed endpoint without `sorry`, project axioms,
`native_decide`, hidden closure fields, or resource relaxations. The result is infrastructure for
stating the explicit formula on one physical algebra; it does not establish a separated complete
metric space of raw functions, density, the explicit formula, positivity, or RH. Evidence
backfill, its public CI, and final clean synchronization are the remaining campaign gates.

Implementation commit `335d6dfa175a345555aaa408b5581ed743d2abf7` passed public Lean Action CI
run `29412820223`, build job `87343685661`, in 1m42s. Immutable evidence backfill and final clean
synchronization remain.
