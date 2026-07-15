# R5 Weil Gaussian Arithmetic Explicit-Formula Preregistration

Campaign: `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-EXPLICIT-FORMULA-01`

Date: 2026-07-16

Status: `LOCALLY_COMPLETE_BRIDGE_REDUCED`

## Route Boundary

The publicly closed predecessor proves the zero side for the fixed entire weight

```text
G_a(s) = exp(a * (s - 1/2)^2),    a > 0.
```

For every `c>1`, selected zero-free truncations of the weighted right vertical xi logarithmic
derivative converge to `pi` times the absolute multiplicity-bearing Gaussian zero sum. The exact
adjacent frontier is now arithmetic: replace the right-half-plane logarithmic derivative by its
pole, real-Gamma, and von-Mangoldt terms; justify all full-line limits and series/integral
interchanges; evaluate the pole pair and every prime-series Gaussian transform.

This campaign does not reopen the selected-height proof, the generic `A_delta` limit, or any
closed Baez-Duarte criterion.

Primary sources:

- Lagarias, Appendix A (A.3)-(A.6):
  https://www.numdam.org/item/10.5802/aif.2311.pdf
- Burnol, local-place formulations of the explicit formula:
  https://arxiv.org/abs/math/9810169
- Balanzario--Cardenas, the centered Gaussian Mellin weight used for zero isolation:
  https://arxiv.org/abs/2312.00108
- Groskin, finite Guinand-Weil dictionary and archimedean cutoff audit:
  https://arxiv.org/abs/2607.02828

Balanzario--Cardenas assumes RH and simple zeros for its shifted isolation application; this
campaign uses neither. Groskin's finite band-limited dictionary is an important falsification
check on finite-cutoff spectral claims, but its Galerkin carrier is not substituted for the fixed
Gaussian endpoint.

## Candidate Audit

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: full fixed-Gaussian arithmetic explicit formula | Adjacent to the compiled zero-side limit. Gaussian Fourier transform gives an explicit super-polynomial von-Mangoldt weight; reciprocal pole terms can be evaluated by the same contour/reflection mechanism; digamma grows only logarithmically. The identity is unconditional and does not imply RH. | Select. |
| C2: only prove full-line integrability of the right vertical integrand | Necessary helper but leaves every arithmetic term unevaluated and does not cross the fixed frontier. | Reject as a shrink of C1. |
| C3: generic `A_delta` arithmetic formula | Closed-strip boundedness still supplies no horizontal decay or absolute zero ordering. | Reject without new generic decay evidence. |
| C4: finite Guinand-Weil Galerkin dictionary | Exact finite values are useful checks, but importing its carrier requires a new quotient/matrix formalization and finite positivity is not RH progress. It is not adjacent to the Gaussian module. | Defer. |
| C5: screw-function self-adjoint operator limit | The 2026 source states the zero-spectrum limit as a conjecture. The project has no proved spectrum correspondence. | Reject as conjectural bridge. |
| C6: positivity or complete monotonicity of the Gaussian zero sum in `a` | No unconditional positivity mechanism survives the off-critical-line stress test; a positivity family would risk hiding an RH-strength assertion. | Reject before use. |

## Fixed Definitions And Endpoint

Harmless algebraic reordering and naming changes are allowed. The final theorem must retain all
three arithmetic components and the exact signs.

```lean
def gaussianVonMangoldtWeight (a : Real) (n : Nat) : Complex :=
  ((Real.pi / a : Real) : Complex) ^ (1 / 2 : Complex) *
    (ArithmeticFunction.vonMangoldt n : Complex) *
      Complex.exp
        (-(Real.log n : Complex) / 2 -
          (Real.log n : Complex) ^ 2 / (4 * a))

def gaussianXiArchimedeanIntegral (a c : Real) : Complex :=
  integral fun y : Real =>
    riemannXiGaussianWeight a (c + y * Complex.I) *
      logDeriv Complex.GammaR (c + y * Complex.I)

theorem gaussianXi_arithmetic_explicit_formula
    {a c : Real} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : Complex) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)) =
      2 * (Real.pi : Complex) * Real.exp (a / 4) +
        gaussianXiArchimedeanIntegral a c -
          tsum (gaussianVonMangoldtWeight a)
```

The endpoint must also expose, as proved dependencies, absolute summability of the explicit prime
weight and integrability of the archimedean integrand. It may not leave an assumed full-line limit,
series/interchange premise, or pole evaluation premise.

## Proof DAG

1. Derive the exact line form of `G_a(c+iy)` and its Gaussian norm.
2. Prove the Fourier-Gaussian integral of one positive-index von-Mangoldt L-series term and simplify
   it to the `c`-independent weight above; check `n=0` separately.
3. Prove a summable, `y`-independent majorant from L-series absolute convergence at `Re(s)=c`, then
   exchange the full real integral and the von-Mangoldt series.
4. Derive `logDeriv GammaR(s) = -log(pi)/2 + digamma(s/2)/2` on `Re(s)>0`; combine logarithmic
   digamma growth with Gaussian decay to prove archimedean integrability.
5. Prove the pole-pair full-line integral equals `2*pi*exp(a/4)`, using either Laplace/Fubini plus
   the Gaussian Fourier transform or an independent two-pole rectangle/reflection argument.
6. Show any symmetric truncation tending to infinity converges to each full-line integral. Apply
   the compiled selected-height zero-side theorem and the right-half-plane logarithmic-derivative
   decomposition, then pass to the limit and rearrange the exact equality.

## Falsification And Stop Conditions

- Reject `a=0`; neither the absolute zero sum nor Gaussian domination is available.
- Keep `c>1`; the von-Mangoldt L-series is used only in its absolute Euler-product half-plane.
- Treat `n=0` explicitly. Do not use `log 0` algebra as if the index were positive.
- Preserve analytic zero multiplicity through `RiemannXiDivisorZeroIndex`.
- The prime term must use `ArithmeticFunction.vonMangoldt`, not primes without prime powers.
- Audit the signs in `logDeriv xi = poles + logDeriv GammaR - L(vonMangoldt)`.
- Audit the Gaussian transform exponent: it must simplify to
  `-log(n)/2 - log(n)^2/(4a)` and become independent of `c`.
- Audit the pole factor against both residues `s=0,1`; the total is `2*pi*exp(a/4)`.
- Do not assume RH, simple zeros, a zero enumeration, Riemann--von Mangoldt, or a generic explicit
  formula.
- Reject any project axiom, `sorry`, `admit`, `native_decide`, unsafe/opaque declaration, or
  resource-limit relaxation.
- If two independent mechanisms fail to prove either the prime interchange, Gamma integrability,
  or pole evaluation, close this campaign as `NO_PROGRESS` and return to route selection. Do not
  close on helper lemmas.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged unless a later unconditional positivity edge is reduced
- `hard_gap_before`: fixed Gaussian zero-side W1c1 limit complete; arithmetic-side evaluation open
- `hard_gap_after`: if successful, one complete unconditional fixed-Gaussian explicit formula with
  zero, pole, archimedean, and prime-power terms
- `hard_gap_delta`: 1 fixed-test arithmetic explicit-formula subedge if successful; 0 for RH
- `assumption_frontier_before`: full-line arithmetic integrability, prime interchange, pole
  evaluation, generic class extension, regularization, W2 positivity
- `assumption_frontier_after`: generic class extension, singular-test regularization, W2 positivity
- `normalized_tuple`: `(centered entire Gaussian G_a, a>0 and c>1, absolute zero and prime-power
  sums plus GammaR line integral, exact zero=pole+archimedean-prime identity, generic test class and
  positivity remain open)`

## Verification Gate

No new declaration becomes a later premise until the complete endpoint, exact TargetChecks,
selected transitive axiom prints, forbidden/declaration/resource scans, standalone and full builds,
`git diff --check`, and public CI all pass.

## Endpoint Update

Proof Attempt A reaches the exact preregistered endpoint as
`gaussianXi_arithmetic_explicit_formula` in
`LeanLab/Riemann/WeilGaussianExplicitFormula.lean`. The module also exposes
`summable_gaussianVonMangoldtWeight` and `integrable_gaussianXiArchimedean` as proved dependencies.
The prime transform treats `n=0` separately; the pole value is obtained independently from the
two residues at `0` and `1`; and the final splice uses the compiled selected-height zero-side
limit. Exact TargetChecks and five standard-only axiom prints pass; every print uses only
`propext`, `Classical.choice`, and `Quot.sound`. The standalone module build, all forbidden-token,
declaration, and resource-option scans, `git diff --check`, and the 8,670-job full build pass. The
campaign is locally complete as `BRIDGE_REDUCED`; publication and public CI remain, and the
persistent RH Goal stays active.
