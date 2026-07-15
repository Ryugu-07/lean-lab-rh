# R5 Weil Symmetric Gaussian Translate-Family Preregistration

Campaign: `CAMPAIGN-20260716-R5-WEIL-SYMMETRIC-GAUSSIAN-FAMILY-01`

Date: 2026-07-16

Status: `LOCALLY_COMPLETE_PENDING_PUBLIC_CI`

## Route Boundary

The publicly closed predecessor proves the complete explicit formula for the single centered
Gaussian

```text
G_a(s) = exp(a * (s - 1/2)^2),    a > 0.
```

The new endpoint is the full reflection-symmetric translate family

```text
G_(a,b)(s) = exp(a * (s - 1/2)^2) * cosh(b * (s - 1/2)),
             a > 0, b real.
```

On the critical line, `b` is a Fourier modulation. On the prime side it translates the Gaussian
heat kernel to the two log-prime centers `+b` and `-b`. Thus the family supplies a genuine
translation parameter rather than another isolated smoothing width. It is adjacent to Arias de
Reyna's prime/archimedean distribution and its Hermite-Gaussian dense test set, but this campaign
does not assume Schwartz density or temperedness.

Primary sources and closest mechanisms:

- Lagarias, Appendix A, the source-faithful Weil explicit formula and test algebra:
  https://www.numdam.org/item/10.5802/aif.2311.pdf
- Arias de Reyna, Theorem 1 and Theorem 3, the prime/archimedean distribution and the Hermite
  test-function core:
  https://arxiv.org/abs/2402.10604v2
- Moriya, Proposition 2.2 and Theorem 3.3, Gaussian-Perron translation/localization formulas:
  https://arxiv.org/abs/2607.04316v1
- Balanzario--Cardenas, the centered Gaussian zero-isolation specialization:
  https://arxiv.org/abs/2312.00108

Moriya's later localization theorems require damping, pole, shifted-contour, RH, or simplicity
conditions. None of those conditional claims is imported here. Arias de Reyna's temperedness
criterion is RH-equivalent and is also not a premise.

## Candidate Audit

| Candidate | Adversarial result | Decision |
|---|---|---|
| C1: full symmetric Gaussian translate-family explicit formula | The existing selected heights are independent of the weight. `cosh(b(s-1/2))` is reflection invariant and uniformly bounded on every fixed vertical strip, while its two Fourier branches give exact centers `log n-b` and `log n+b`. `b=0` must recover the closed formula. | Select. |
| C2: Moriya Gaussian-Perron defect formula | The source gives a useful error-function prime weight, but its exact carrier has a `1/z` pole, shifted zeta contours, trivial-zero bookkeeping, and Riemann--von Mangoldt input not present in the adjacent project endpoint. Later localization is conditional. | Defer as a separate source campaign. |
| C3: Arias de Reyna tempered-distribution iff | This is exactly RH-equivalent and requires constructing the prime/archimedean Radon measure as a Schwartz functional plus the reverse pole argument. Gaussian probes are the honest prerequisite. | Defer; do not postulate temperedness. |
| C4: de Bruijn--Newman heat flow | The heat family is source-valid, but the first decisive zero-reality edge and the de Bruijn--Newman constant infrastructure are much larger than one bounded campaign. | Defer. |
| C5: screw-function finite-interval operators | Suzuki's 2026 operator limit is explicitly conjectural. Finite self-adjoint realizations do not provide the missing spectral-limit bridge. | Reject as a proof route without new spectral evidence. |
| C6: R1 Gram/projection continuation | Ehm supplies exact Gram decompositions, but no new unconditional residual upper bound survives the already compiled Wong, Carvill, and sparse-target falsification tests. | Reject for this selection. |

## Pre-Admission Falsification

Lean scratch checks, without placeholders, verify all of the following before source edits:

1. `G_(a,-b) = G_(a,b)`.
2. `G_(a,b)(1-s) = G_(a,b)(s)`.
3. `G_(a,0) = G_a` exactly.
4. The positive exponential branch transforms to
   `exp(-log(n)/2-(log(n)-b)^2/(4a))`.
5. The negative exponential branch transforms to
   `exp(-log(n)/2-(log(n)+b)^2/(4a))`.
6. On every xi zero, the new factor has norm at most `exp(|b|/2)`, so the full zero family is
   absolutely summable from the compiled Gaussian zero sum.

The boundary `a=0` is rejected. The family is even in `b`, and all formulas must retain that
symmetry. No positivity claim is admitted: on the critical line the new factor is `cos(b*gamma)`,
which can have either sign.

## Fixed Definitions And Endpoint

Harmless naming and algebraic reordering are allowed. Both translated prime weights, the exact
pole factor, and the `b=0` specialization must remain visible.

```lean
def riemannXiSymmetricGaussianWeight (a b : Real) (z : Complex) : Complex :=
  riemannXiGaussianWeight a z * Complex.cosh ((b : Complex) * (z - 1 / 2))

def symmetricGaussianVonMangoldtWeight (a b : Real) (n : Nat) : Complex :=
  (((Real.pi / a : Real) : Complex) ^ (1 / 2 : Complex)) *
    (ArithmeticFunction.vonMangoldt n : Complex) *
      (Complex.exp
          (-(Real.log n : Complex) / 2 -
            ((Real.log n - b : Real) : Complex) ^ 2 / (4 * a)) +
        Complex.exp
          (-(Real.log n : Complex) / 2 -
            ((Real.log n + b : Real) : Complex) ^ 2 / (4 * a))) / 2

def symmetricGaussianXiArchimedeanIntegral (a b c : Real) : Complex :=
  integral fun y : Real =>
    riemannXiSymmetricGaussianWeight a b (c + y * Complex.I) *
      logDeriv Complex.GammaR (c + y * Complex.I)

theorem symmetricGaussianXi_arithmetic_explicit_formula
    {a b c : Real} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : Complex) *
        tsum (fun p : RiemannXiDivisorZeroIndex =>
          riemannXiSymmetricGaussianWeight a b (riemannXiDivisorZeroValue p)) =
      2 * (Real.pi : Complex) * Real.exp (a / 4) * Real.cosh (b / 2) +
        symmetricGaussianXiArchimedeanIntegral a b c -
          tsum (symmetricGaussianVonMangoldtWeight a b)
```

The endpoint must also expose absolute zero and prime summability, archimedean integrability, the
selected-height zero-side limit, the exact pole integral, and exact `b=0` specialization lemmas.

## Proof DAG

1. Prove differentiability, reflection, `b`-evenness, `b=0`, and the strip-uniform `cosh` norm
   bound. Deduce absolute zero summability.
2. Reuse the weight-independent selected zero-free heights. Bound the new top edge by a fixed
   `b,c` constant times the compiled polynomial-Gaussian majorant, apply the finite rectangle
   theorem, and pass the finite zero cutoff to the new absolute `tsum`.
3. Bound the right-line `cosh` factor by a constant and transfer the compiled digamma-Gaussian
   integrability proof to the new archimedean term.
4. Split `cosh` into two exponentials. Evaluate each positive-index von-Mangoldt term by
   `integral_cexp_quadratic`, treat `n=0` separately, and prove the absolute sum/integral
   interchange.
5. Re-run the two-pole symmetric rectangle with the new weight. The residues at `0` and `1` are
   both `exp(a/4)*cosh(b/2)`; prove full-line integrability and the exact pole value.
6. Pass every arithmetic truncation along the selected heights, splice with the zero-side limit,
   and prove all `b=0` definitions and the final theorem reduce to the closed centered-Gaussian
   endpoint.

## Stop Conditions

- Reject any loss of the `b=-b` symmetry or either `log(n) +/- b` branch.
- Reject a pole contribution other than `2*pi*exp(a/4)*cosh(b/2)`.
- Reject any bound that grows with the selected height through the `cosh` factor; for real `b` its
  vertical oscillation is uniformly bounded on fixed strips.
- Do not assume RH, simple zeros, a zero enumeration, Riemann--von Mangoldt, generic Weil
  positivity, Schwartz density, or temperedness of the Arias de Reyna measure.
- Reject any project axiom, `sorry`, `admit`, `native_decide`, unsafe/opaque declaration, or
  resource-limit relaxation.
- If two independent mechanisms fail to close either the selected-height zero side or the exact
  two-branch prime transform, close as `NO_PROGRESS`. Do not close on norm or integrability helpers.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged
- `hard_gap_before`: one centered Gaussian W1c formula complete; generic W1c1/W1c2 open
- `hard_gap_after`: if successful, one unconditional two-parameter reflection-symmetric Gaussian
  translate family, with exact log-prime heat-kernel translations
- `hard_gap_delta`: 1 parametric Gaussian-probe-family subedge; 0 for G6, G7, and RH
- `assumption_frontier_before`: no translated probe family; no Schwartz density; no tempered prime
  distribution; no Weil positivity
- `assumption_frontier_after`: Schwartz/Hermite density, tempered-distribution extension, generic
  local regularization, Weil positivity, and RH remain
- `expected_classification`: `NEW_RELEVANT_LEAN_THEOREM`
- `normalized_tuple`: `(G_(a,b)=exp(a(s-1/2)^2)cosh(b(s-1/2)), a>0 and real b, existing selected
  heights plus two exact Gaussian Fourier branches, full zero/pole/GammaR/prime-power identity,
  density and temperedness remain open)`

## Verification Gate

No new declaration becomes a later premise until the complete endpoint, all specialization
checks, exact TargetChecks, selected transitive axiom prints, forbidden/declaration/resource scans,
standalone and full builds, `git diff --check`, and public CI all pass.

## Local Outcome

Proof Attempt A reaches the fixed endpoint without changing the statement or invoking a stop
condition. `WeilSymmetricGaussianFamily.lean` proves the generic selected-height rectangle limit
for any analytic reflection-symmetric weight with an absolutely summable zero restriction and a
vanishing selected top edge. The symmetric Gaussian family discharges those assumptions, both
exponential prime branches evaluate to the preregistered `log(n)-b` and `log(n)+b` kernels, the
pole pair evaluates to `2*pi*exp(a/4)*cosh(b/2)`, and the final theorem is
`symmetricGaussianXi_arithmetic_explicit_formula`. The named zero-translation theorem reduces to
the previous centered-Gaussian formula.

Standalone source, Targets, TargetChecks, and AxiomsAudit builds pass. The selected axiom prints
contain only `propext`, `Classical.choice`, and `Quot.sound`. Placeholder, forbidden declaration,
and diff scans are empty, and the 8,671-job full build passes. Classification is
`NEW_RELEVANT_LEAN_THEOREM`; the fixed accounting remains one parametric probe-family subedge and
zero delta for G6, G7, and RH. Public commit, push, and CI remain before closure.
