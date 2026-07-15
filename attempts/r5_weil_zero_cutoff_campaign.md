# R5 Weil Finite-Height Zero-Cutoff Campaign

Campaign: `CAMPAIGN-20260715-R5-WEIL-ZERO-CUTOFF-01`

Date: 2026-07-15

Status: `LOCAL_BRIDGE_REDUCED_AWAITING_PUBLIC_CI`

Route: R5, source-faithful Weil explicit formula.

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | W1c0 is complete. The adjacent indivisible source edge is the finite-height weighted argument principle; W1c2 regularization and the complete class-E limit remain later nodes. | Audit residue, divisor, and uniform-series APIs. |
| 2 | `CONJECTURE_GENERATION` | Generated the complete class-E formula, finite-height weighted xi identity, unweighted count, one-pole residue helper, and an assumed finite rational-kernel identity. | Send all five to adversarial audit. |
| 3 | `ADVERSARIAL_TEST` | C1 is too large; C3 and C4 are too narrow; C5 bypasses xi. C2 is unconditional, not RH-equivalent, and is supported by existing genus-one summability plus the compact far-zero estimate already compiled for positive derivatives in `LiZeroFormula.lean`. | Select and preregister C2 without shrinking it. |
| 4 | `PROOF_ATTEMPT_A` | Completed engineering batch: proved genuine `k=0` local-uniform summability on the xi nonzero set, finite interior support, arbitrary-pole and entire-weighted Cauchy rectangle integrals, generic compact-edge sum/integral interchange, and the four-edge rectangle `HasSum`. `LeanLab/Riemann/WeilZeroCutoff.lean` compiles without errors. | The infinite zero-sum interchange is now justified; proceed to pointwise residue evaluation and finite-support collapse. No hard-gap reduction is claimed yet. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | Completed the fixed endpoint. Each compensated zero term is classified as the strict-interior residue or zero under the zero-free boundary hypothesis; the boundary `tsum` collapses to the finite multiplicity-bearing `finsum`; and the Hadamard polynomial derivative vanishes after multiplication by the entire weight and rectangle integration. `rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum` compiles with the preregistered statement. | Admit the result to independent audit. This closes the finite-height W1c1 zero-side subedge if all gates pass; height limits and regularization remain open. |
| 6 | `INDEPENDENT_AUDIT` | Rechecked positive orientation, strict-inside versus closed-boundary geometry, outside-pole vanishing, analytic multiplicity, compensation, local-uniform rather than pointwise convergence, and the Hadamard polynomial cancellation. The new module compiles without warnings; exact TargetChecks, seven standard-only axiom prints, empty placeholder/declaration/`native_decide`/unsafe/resource scans, `git diff --check`, the 8,635-job standalone module build, and the 8,667-job full build pass. | Close locally as `BRIDGE_REDUCED`; publish the implementation and require public CI before final campaign closure. |

## Fixed Accounting

- `hard_gap_before`: W1c1 finite-height zero-cutoff passage open
- `hard_gap_after`: W1c1 finite-height weighted zero cutoff complete; height-limit/decay and W1c2 regularization remain
- `hard_gap_delta`: 1 source-level W1c1 subedge; 0 for RH
- `normalized_tuple`: `research/r5_weil_zero_cutoff_prereg_20260715.md`

All local-uniformity, finite-support, translated reciprocal-integral, `dslope`, four-edge
interchange, and Hadamard-splice lemmas are one engineering batch and do not count as separate
research loops.

## Local Closure

Classification: `BRIDGE_REDUCED` locally, pending public CI.

The campaign proves the complete fixed endpoint without RH or a weakened surrogate. It does not
prove a height limit, horizontal-edge decay, prime-side inversion, endpoint regularization, the
complete Weil explicit formula, W2 positivity, or RH.
