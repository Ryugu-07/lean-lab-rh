# R5 Gaussian-Weil Reverse Criterion Preregistration

Campaign: `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-REVERSE-CRITERION-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

## Fixed Proposition

For every finite real exponential polynomial, require positivity of the direct arithmetic
Gaussian-Weil quadratic at every positive width. The indivisible endpoint is

```lean
theorem riemannHypothesis_iff_gaussianXiArithmeticQuadratic_re_nonneg :
    RiemannHypothesis ↔
      ∀ (ι : Type) [Fintype ι] {a : ℝ}, 0 < a →
        ∀ b w : ι → ℝ,
          0 ≤ (gaussianXiArithmeticQuadratic a b w 2).re
```

Harmless universe, binder, naming, and reassociation changes are allowed. The right side must
remain the existing direct pole/GammaR/von-Mangoldt arithmetic expression, not a newly assumed
zero-side functional.

## Strength And DAG Position

- The proposition is intended to be exactly equivalent to RH.
- The forward implication is the publicly verified finite Gaussian-Weil square theorem.
- The reverse implication is a new project edge from positivity on this restricted Gaussian
  family to the absence of off-critical-line xi divisor zeros.
- Completion has `hard_gap_delta=0` for unconditional RH, W2, and G7: it gives another exact
  criterion but proves neither equivalent side unconditionally.
- No Schwartz density, separated temperedness, or general Weil-class continuity is used.

## Closest Results

- Lagarias, Appendix A, records the full Weil positivity criterion and its equivalence to RH:
  https://arxiv.org/abs/math/0104132
- Suzuki develops equivalent Weil quadratic/screw-function criteria:
  https://arxiv.org/abs/2206.03682 and https://arxiv.org/abs/2606.09096
- Arias de Reyna identifies a Gaussian/Hermite core and the RH-equivalent temperedness frontier:
  https://arxiv.org/abs/2402.10604
- A Nicholas Polson SSRN preprint posted 2026-07-09 advertises a Gaussian-family Weil positivity
  and extremal-zero mechanism. Its PDF was not independently retrievable during route selection,
  it is unreviewed, and it is not a premise. Possible overlap must be reported conservatively.

No claim of first proof or first formalization is admitted without a separate novelty audit.

## Adversarial Audit

1. Write `z_p = rho_p - 1/2` and `q_p = -Re(z_p^2)`. Every `q_p ≤ q_0` sublevel is finite because
   xi zeros lie in `0 < Re(rho) < 1` and a bounded `q` bounds `|Im(rho)|`.
2. For any selected off-line zero, its complete `q≤q_0` sublevel is finite. The final proof does
   not need the stronger preregistered choice of a globally minimal off-line `q_0`: the separator
   annihilates every unwanted lower or same-layer square class directly.
3. A finite real polynomial in `exp(h z)` can annihilate every lower or same layer except the
   target square classes `z^2 = z_0^2` and `z^2 = conj(z_0^2)`. The step `h>0` is selected small
   enough to prevent all finite exponential collisions, including conjugate roots.
4. The exact packet factorization is

   ```text
   exp(a*z^2) F(z) F(-z).
   ```

5. After multiplication by `exp(a*q_0)`, every higher layer tends to zero under one fixed
   summable width-one packet majorant. This must be proved by dominated convergence over the full
   multiplicity-bearing divisor index.
6. If `Im(z_0^2) ≠ 0`, a phase-locked sequence of positive widths tending to infinity makes every
   surviving target-square contribution have the same strictly negative real part.
7. If `Im(z_0^2) = 0`, off-line status forces `z_0` to be nonzero real. Squaring the separator and
   multiplying by `X-1` makes `F(z_0)F(-z_0) < 0` directly.
8. A synthetic finite-orbit numerical model gave scaled real sum
   `-1.0687737079002222e-06`, with lower layers annihilated and imaginary residual below
   `3.5e-23`. This is `NUMERICAL_ONLY` and not a premise.

## Fixed Proof DAG

1. Prove exact packet factorization through a finite real exponential polynomial.
2. Prove finite `q` sublevels for an arbitrary selected off-line divisor zero.
3. Construct a positive finite collision-free exponential step and the real separator polynomial.
4. Define the protected separator `Q=P^2*(X-1)` and prove target nonvanishing.
5. Prove the scaled higher-layer `tsum` tends to zero by dominated convergence.
6. Prove phase-locked negativity when `Im(z_0^2) ≠ 0` and direct real-axis negativity when it is
   zero.
7. Build the finite unwanted low-layer set, reduce the low sum to target square classes, and prove
   the scaled complete zero `tsum` is eventually negative.
8. Use the existing explicit formula at `c=2` to contradict arithmetic positivity.
9. Convert absence of off-line divisor zeros to `RiemannHypothesis` using the exact support bridge.
10. Add exact target witnesses, transitive axiom prints, forbidden scans, and full/public builds.

## Rejection Conditions

- Do not assume Schwartz density, Hermite completeness, temperedness, a Bochner theorem, or
  continuity of separated zero/prime distributions.
- Do not assume simple zeros, conjugate multiplicities, a zero enumeration, a numerical zero-free
  height, or Riemann-von Mangoldt asymptotics.
- Do not weaken the endpoint to helper lemmas or zero-side positivity alone.
- Do not state unconditional arithmetic positivity.
- Reject any project axiom, `sorry`, `admit`, `native_decide`, unsafe declaration, or resource-limit
  relaxation.
- If the finite separator or scaled infinite-tail argument fails under two independent exact
  approaches, close locally as `NO_PROGRESS` and return to fresh route selection.

## Accounting

- `research_activity`: active
- `classification_if_complete`: `KNOWN_THEOREM_FORMALIZED` pending independent novelty review
- `hard_gap_before`: W2g0 supplies only RH-forward positivity for the finite Gaussian packet
- `hard_gap_after`: if successful, positivity on that exact restricted arithmetic family is an RH
  criterion
- `hard_gap_delta`: 0 for unconditional RH, W2, and G7
- `assumption_frontier_before`: reverse restricted-family implication is unproved
- `assumption_frontier_after_if_complete`: unconditional positivity/RH remains; the reverse
  restricted-family implication closes without density or temperedness

## Local Completion Evidence

`LeanLab/Riemann/WeilGaussianPositivityCriterion.lean` compiles the exact endpoint without
placeholders. Its 1,476 lines include packet factorization, finite decay sublevels, finite
exponential separation, the real protected separator, target nonvanishing, scaled higher-layer
dominated convergence, phase-locked widths, the real-axis negative-product branch, the direct
arithmetic contradiction, and the final RH equivalence. Exact Targets and TargetChecks compile;
six selected transitive axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
forbidden scans and `git diff --check` are clean; and the full 8,674-job build passes. Public
commit and CI remain before campaign closure.

## Public Implementation Evidence

- implementation commit: `b2d2ce18ff1491f684098b04c7a5be73e0ebdc98`
- Lean Action CI run: `29453270303`
- build job: `87480595744`
- conclusion: `success`
- duration: `2m14s`

The implementation was independently public-built before the evidence-backfill commit below.

## Public Closure Evidence

- evidence-backfill commit: `68e96525f3f89562ae47e1da9e074911701a6c2e`
- Lean Action CI run: `29453470463`
- build job: `87481233198`
- conclusion: `success`
- duration: `1m24s`

Together with the implementation evidence above, this publicly closes the fixed campaign as
`KNOWN_THEOREM_FORMALIZED` pending any later independent novelty review. The broad RH Goal remains
active; unconditional positivity and RH remain open.
