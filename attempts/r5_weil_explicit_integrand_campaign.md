# R5 Weil Explicit-Integrand Campaign

Campaign: `CAMPAIGN-20260715-R5-WEIL-EXPLICIT-INTEGRAND-01`

Date: 2026-07-15

Status: `CLOSED_BRIDGE_REDUCED`

Route: R5, source-faithful Weil explicit formula.

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | R1/R2 are parked at RH-hard approximation edges, R3's exact Li criterion and Li-Weil Gram packaging are complete, R4 still lacks an operator/spectrum bridge, and R5 has the unique open source bridge W1c. | Audit bounded W1c subedges. |
| 2 | `CONJECTURE_GENERATION` | Generated five candidates: the full class-E formula, finite-prime terms, the archimedean local term, the right-half-plane logarithmic-derivative integrand, and a single fixed test function. | Send all five to source and strength audit. |
| 3 | `ADVERSARIAL_TEST` | The full formula exceeds one campaign; isolated local terms and a fixed test do not connect both sides. The integrand identity is unconditional, strictly weaker than RH, sign-testable from the xi product, and supported by existing Hadamard and von Mangoldt APIs. | Select and preregister C4. |
| 4 | `PROOF_ATTEMPT_A` | The first Lean compile exposed eta-expansion of `GammaR`, denominator normalization in the pole factor, the von Mangoldt minus sign, and missing neighborhood scope. After explicit repairs, `GammaR` differentiability, the local xi product, and `logDeriv xi = poles + logDeriv GammaR - L(vonMangoldt)` compile on `Re(s)>1`. | Continue without changing the fixed statement. |
| 5 | `PROOF_ATTEMPT_B_OR_PIVOT` | `Re(s)>1` excludes project nontrivial zeros through Mathlib's zeta nonvanishing theorem. The existing genus-one Hadamard logarithmic-derivative sum therefore splices directly with the prime/archimedean identity, with multiplicity retained. The standalone module compiles. | Fixed endpoint reached; begin independent audit. |
| 6 | `INDEPENDENT_AUDIT` | Rechecked `xi = s(s-1) GammaR(s) zeta(s)/2`, the two pole signs, `L(vonMangoldt) = -zeta'/zeta`, the `Re(s)>1` nonvanishing domain, and multiplicity on the Hadamard sum. Exact TargetChecks, all six public axiom prints, empty forbidden scans, `git diff --check`, standalone builds, and the 8,666-job full build pass. No contour, cutoff, regularization, or RH premise is used. | Close locally as `BRIDGE_REDUCED`; public evidence remains. |

## Fixed Accounting

- `hard_gap_before`: W1c integrand bridge open
- `hard_gap_after`: W1c0 integrand bridge complete; W1c1 contour passage and W1c2 regularization open
- `hard_gap_delta`: 1 source-level W1c subedge, 0 for RH
- `assumption_frontier_before`: W1c contour/regularization and W2 positivity
- `assumption_frontier_after`: W1c1/W1c2 and W2 positivity
- `normalized_tuple`: `research/r5_weil_explicit_integrand_prereg_20260715.md`

All helper lemmas in the factor, nonvanishing, and logarithmic-derivative calculation belong to
this one indivisible campaign and do not count as separate loops.

## Local Result

Result: `BRIDGE_REDUCED`

- `differentiableAt_GammaR_of_re_pos` supplies the missing real-place differentiability domain.
- `logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt` compiles the exact unconditional
  prime/pole/archimedean integrand on `Re(s)>1`.
- `exists_weilExplicitIntegrand_eq_hadamardZeroSum` identifies that integrand with the existing
  multiplicity-bearing genus-one zero sum.
- Exact TargetChecks and all six public transitive axiom prints pass; every new theorem depends
  only on `propext`, `Classical.choice`, and `Quot.sound`.
- Empty forbidden/declaration/resource scans, `git diff --check`, standalone builds, and the
  8,666-job full build pass.

This closes W1c0 only. Test-function integration, contour and zero-cutoff limits, local
regularization, the covariance extension, W2 positivity, and RH remain open. Implementation
commit `89d4dd12ebedc75c13261a0d43a9254b5931c30d` passed public Lean Action CI run
`29417432562`, build job `87359008630`, in 1m47s. Evidence-backfill commit
`1b405639a4e28c72fc1e2484259c047ad95ed0b2` passed public Lean Action CI run `29417710278`, build
job `87359940112`, in 1m31s. The campaign is publicly closed; only the final closure-log CI and
clean synchronization check remain.
