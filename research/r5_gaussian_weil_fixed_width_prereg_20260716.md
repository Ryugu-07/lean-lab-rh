# R5 Gaussian-Weil Fixed-Width Criterion Preregistration

Campaign: `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-FIXED-WIDTH-01`

Date: 2026-07-16

Status: `LOCAL_VERIFIED`

## Fixed Proposition

For every preassigned positive Gaussian width, positivity at that one width over every finite
real shift family is already equivalent to RH. The indivisible endpoint is

```lean
theorem riemannHypothesis_iff_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg
    {a0 : R} (ha0 : 0 < a0) :
    RiemannHypothesis <->
      forall (iota : Type) [Fintype iota], forall b w : iota -> R,
        0 <= (gaussianXiArithmeticQuadratic a0 b w 2).re
```

The formal module may use the corresponding Lean Unicode, harmless universe changes, and a more
idiomatic theorem name. The right side must remain the existing direct pole/GammaR/von-Mangoldt
arithmetic expression. It may not be replaced by an assumed zero-side functional or by positivity
over a family of widths.

## Strength And DAG Position

- The existing theorem requires every positive width. This campaign asks whether one arbitrary
  fixed positive width generates all sufficiently large widths inside the finite exponential test
  algebra.
- Completion would strictly compress the parameter family in the known RH-equivalent Gaussian
  criterion, but it would still be an equivalence and would not establish unconditional
  positivity or RH.
- `hard_gap_delta=0` for unconditional W2, G7, and RH.
- The campaign is admitted only because the width transfer has a finite-test approximation and
  does not require an unformalized Bochner representation or complex-measure support theorem.

## Closest Results And Literature Audit

- Lagarias records the full Weil positivity criterion and its equivalence to RH:
  https://arxiv.org/abs/math/0104132
- Arias de Reyna studies a distributional Gaussian/Hermite criterion and the temperedness
  frontier: https://arxiv.org/abs/2402.10604
- The already compiled project theorem
  `riemannHypothesis_iff_gaussianXiArithmeticQuadratic_re_nonneg` proves the corresponding finite
  Gaussian criterion when every positive width is quantified.

Targeted searches for a published one-fixed-width translation criterion did not locate an exact
match. This is not a novelty determination. No claim of first proof or first formalization is
allowed without an independent source and novelty audit.

## Adversarial Audit

1. Finite symmetric zero models support the claim: a nonimaginary exponent makes the fixed-width
   translation kernel unbounded, contradicting finite positive definiteness.
2. That finite argument does not automatically extend to the infinite xi divisor because there
   need not be an off-line zero with maximal real part and infinite cancellations must be
   controlled.
3. A direct Bochner/support proof was rejected as the immediate route: Mathlib has characteristic
   function uniqueness for positive real measures but no packaged Bochner theorem producing such
   a measure from the finite quadratic inequalities, and the xi zero weights form a complex
   discrete measure before RH.
4. The surviving route stays inside finite tests. For `c>0`, set

   ```text
   A_n(z) = cosh(sqrt(c/n) * z)^n.
   ```

   `A_n` is a finite real exponential sum, and

   ```text
   A_n(z) A_n(-z) = cosh(sqrt(c/n) * z)^(2*n) -> exp(c*z^2).
   ```

5. For centered xi zeros `z=rho-1/2`, `abs(Re z)<1/2`. The elementary bounds
   `norm(cosh u)<=cosh(Re u)<=exp((Re u)^2/2)` therefore give a uniform bound for the complete
   approximating multiplier, independent of the zero height and of `n`.
6. Multiplying the original finite exponential polynomial by `A_n` is again one finite real shift
   family. Hence fixed-width positivity applies to every approximant.
7. The base width `a0>0` supplies a summable Gaussian majorant over the complete
   multiplicity-bearing xi divisor, so dominated convergence should transfer the zero quadratic
   from width `a0` to every larger target width `a0+c`.
8. The existing off-line separator proof produces negative packets along widths tending to
   infinity. It must be strengthened to exceed an arbitrary prescribed lower bound, after which
   fixed-width transfer yields a negative quadratic at `a0` and a contradiction.

## Fixed Proof DAG

1. Define a finite Rademacher exponential family indexed by `Fin n -> Bool` and prove its exact
   exponential sum is `cosh(h*z)^n`.
2. Tensor that family with an arbitrary finite real shift packet and prove exact packet
   factorization at the base width.
3. Prove pointwise convergence
   `cosh(sqrt(c/n)*z)^(2*n) -> exp(c*z^2)` using the existing complex exponential power limit and
   `sinh z / z -> 1`.
4. Prove `norm(cosh z) <= Real.cosh z.re`, then the uniform centered-strip bound for the
   Rademacher multipliers.
5. Apply `tendsto_tsum_of_dominated_convergence` with the positive base-width Gaussian packet as
   the complete divisor majorant. Deduce convergence of fixed-width finite zero quadratics to the
   arbitrary larger-width zero quadratic.
6. Transport that convergence through the existing explicit formula at `c=2`, so a strictly
   negative larger-width arithmetic quadratic forces a strictly negative finite quadratic at the
   fixed base width.
7. Strengthen the existing off-line separator endpoint to produce a negative width above every
   real lower bound.
8. Exclude every off-line xi divisor zero from fixed-width positivity and prove the exact iff.
9. Add the exact target witness, transitive axiom prints, forbidden scans, local full build, and
   independent public CI evidence.

## Local Result

`LeanLab/Riemann/WeilGaussianFixedWidthCriterion.lean` compiles the exact fixed proposition
without placeholders. The proof follows the preregistered finite Rademacher route: exact finite
exponential realization, the complex `cosh` power limit, a strip-uniform norm bound, dominated
convergence over the complete multiplicity-bearing xi divisor, transfer of strict arithmetic
negativity back to the base width, and the threshold-strengthened off-line separator.

The exact witnesses in `TargetChecks.lean` compile. Axiom prints for the analytic limit, divisor
`tsum` transfer, off-line negative witness, reverse implication, and final iff report only
`propext`, `Classical.choice`, and `Quot.sound`. Repository-wide forbidden declaration, scratch
name, and resource-relaxation scans are empty; `git diff --check` passes; and the full 8,677-job
build succeeds. Publication and independent public CI remain pending at this checkpoint.

## Rejection Conditions

- Do not assume a Bochner representation, Fourier support uniqueness, almost periodicity, or a
  new complex-measure support theorem.
- Do not assume simple zeros, a zero enumeration, Riemann-von Mangoldt asymptotics, a maximal
  off-line real part, or numerical zero data.
- Do not weaken the endpoint to a finite-zero model, a cosh limit, a width-transfer helper, or
  positivity at more than one width.
- Do not claim unconditional arithmetic positivity or RH.
- Reject any `sorry`, `admit`, `native_decide`, project axiom, unsafe declaration, or
  resource-limit relaxation.
- If either the exact finite exponential realization or the complete-divisor dominated
  convergence fails under two independent formal approaches, close locally as `NO_PROGRESS` and
  return to fresh route selection.

## Accounting

- `research_activity`: active
- `work_class`: `DISCOVERY`
- `classification`: `NEW_RELEVANT_LEAN_THEOREM` pending independent novelty review and public CI
- `hard_gap_before`: the compiled Gaussian arithmetic criterion quantifies every positive width
- `hard_gap_after`: one arbitrary preassigned positive width suffices
- `hard_gap_delta`: 0 for unconditional RH, W2, and G7
- `assumption_frontier_before`: no proved closure of the finite real shift tests under Gaussian
  width increase
- `assumption_frontier_after`: the width parameter is compressed; unconditional
  fixed-width arithmetic positivity remains exactly RH-hard
