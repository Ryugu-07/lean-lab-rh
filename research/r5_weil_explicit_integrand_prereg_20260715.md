# R5 Weil Explicit-Integrand Preregistration

Campaign: `CAMPAIGN-20260715-R5-WEIL-EXPLICIT-INTEGRAND-01`

Date: 2026-07-15

Status: `LOCALLY_VERIFIED`

## Source Boundary

Lagarias Appendix A states the trace and covariance forms of Weil's explicit formula and warns
that the zero cutoff, local terms, and endpoint regularization are essential. Burnol's
`The Explicit Formula in simple terms`, pp. 4 and 11-14, gives the Riemann-zeta local
decomposition in terms of the real Gamma factor and the finite-prime von Mangoldt series.

Primary sources:

- https://www.numdam.org/item/10.5802/aif.2311.pdf
- https://arxiv.org/abs/math/9810169

The complete test-function formula is not preregistered here. This campaign targets only its
pointwise analytic integrand on `Re(s) > 1`, where every factor is nonzero and the von Mangoldt
Dirichlet series converges absolutely.

## Route Map And Candidate Audit

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: complete Burnol class-E explicit formula | Requires Mellin inversion, rectangle limits, zero cutoffs, and the archimedean regularization in one batch. | Reject as larger than one bounded campaign. |
| C2: finite-prime sum alone | Summability and prime-power reindexing are useful but do not connect the prime side to xi or zeros. | Reject as a standalone research endpoint. |
| C3: archimedean local functional alone | The finite integral has a nontrivial singular regularization at `x=1` and remains disconnected from the zero side. | Defer. |
| C4: right-half-plane logarithmic-derivative integrand | Existing project xi/Hadamard infrastructure and Mathlib's von Mangoldt L-series theorem meet exactly here; no cutoff or RH premise is needed. | Select. |
| C5: one fixed compactly supported test function | A single evaluation cannot establish a source-faithful test-class formula or density. | Reject. |

C4 is not equivalent to RH and does not imply RH. It follows from the Euler product,
archimedean completion, and the already audited genus-one Hadamard product. What becomes easier is
the remaining W1c contour task: its integrand will already be a compiled equality between the
zero, pole, finite-prime, and archimedean sides, leaving cutoff passage and regularization as
separate explicit obligations.

## Fixed Lean Endpoint

The implementation module will be `LeanLab/Riemann/WeilExplicitIntegrand.lean`.

```lean
theorem differentiableAt_GammaR_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.Gammaℝ s

theorem logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s -
        L ↗ArithmeticFunction.vonMangoldt s

theorem exists_weilExplicitIntegrand_eq_hadamardZeroSum
    {s : ℂ} (hs : 1 < s.re) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      Polynomial.eval s P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) =
        1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s -
          L ↗ArithmeticFunction.vonMangoldt s
```

Names may change only to match actual imported notation; the mathematical statement, domain, and
signs are fixed. Exact checks must include a direct rewrite to Mathlib's
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and the Hadamard zero-sum
endpoint.

## Falsification And Stop Conditions

- Check the product signs against `xi(s) = s(s-1) GammaR(s) zeta(s) / 2`.
- Check that `Re(s)>1` really discharges `s != 0`, `s != 1`, zeta nonvanishing, Gamma-factor
  nonvanishing, and exclusion from the project nontrivial-zero carrier.
- Reject any proof that uses the full explicit formula, RH, or a zero-cutoff limit as a premise.
- Close as `BRIDGE_REDUCED` only if both the prime/archimedean decomposition and the Hadamard
  splice compile with standard axioms. Otherwise close as `NO_PROGRESS` or
  `DEPENDENCY_GAP_IDENTIFIED` and return to route selection.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: W1c has no compiled equality joining the xi zero-side logarithmic derivative
  to the pole, GammaR, and von Mangoldt terms
- `hard_gap_after`: if successful, W1c0 integrand identity complete; contour cutoff,
  test-function integration, and regularization remain
- `hard_gap_delta`: 1 source-level analytic subedge if successful, 0 for RH
- `assumption_frontier_before`: complete W1c explicit formula and W2 positivity
- `assumption_frontier_after`: W1c contour/regularization and W2 positivity
- `normalized_tuple`: `(right-half-plane xi log-derivative decomposition and Hadamard splice,
  Re(s)>1, product log derivatives plus Mathlib von Mangoldt L-series, contour and regularization)`

## Verification Gate

No result may be used later until standalone and full builds, exact TargetChecks, transitive
standard-only axiom output, empty forbidden/declaration/resource scans, `git diff --check`, and
public CI all pass. No `sorry`, project axiom, `native_decide`, or resource relaxation is allowed.

## Local Result

The fixed endpoint compiles in `LeanLab/Riemann/WeilExplicitIntegrand.lean` without changing its
domain or signs. The proof derives the local xi product on `Re(s)>1`, takes logarithmic derivatives
only after proving all factors nonzero and differentiable, rewrites the zeta term using Mathlib's
von Mangoldt L-series theorem, and splices the result with the compiled multiplicity-bearing
Hadamard zero sum.

Exact TargetChecks, all six public transitive axiom prints, empty forbidden/declaration/resource
scans, `git diff --check`, standalone builds, and the 8,666-job full build pass. Every new theorem
uses only `propext`, `Classical.choice`, and `Quot.sound`. Classification is locally
`BRIDGE_REDUCED`: W1c0 closes, while W1c1/W1c2, W2, and RH remain open. Publication and public CI
remain.
