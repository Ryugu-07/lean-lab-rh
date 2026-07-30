# H12 Levinson--Montgomery Jensen Top Zero-Count Preregistration

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-JENSEN-TOP-ZERO-COUNT-01`

Selected node:
`H12-LM-JENSEN-TOP-REAL-ZERO-COUNT-01`

Mode: `LITERATURE / OMISSION-AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCALLY / PRODUCTION_BLOCKED`

## Historical target

Levinson--Montgomery 1974, page 52, closes the proof of Theorem 1 by saying that a
"standard use of Jensen's theorem" bounds the changes of argument of `zeta(sigma+iT)` and
`zeta'(sigma+iT)`, from `sigma=1` to `sigma=0`, by `O(log T)`.

The proof does not spell out:

1. the analytic functions whose zeros count real-part crossings;
2. how the moving height enters their domains;
3. a center value uniformly separated from zero;
4. a polynomial bound on the larger Jensen circle;
5. why the derivative needs a phase normalization;
6. how the resulting complex divisor count controls the real segment.

This campaign reconstructs those points for the actual project zeta objects.

Primary source:

`https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6174-11511_2006_Article_BF02392141.pdf`

## Proposed actual functions

The production module may adjust harmless normalizing constants, but it must retain the
following meanings.

For real `t`, let

```text
Z_t(z) =
  (zeta(z+i*t) + conj(zeta(conj(z)+i*t))) / 2.
```

For real `x`, `Z_t(x)=Re(zeta(x+i*t))`.

Let

```text
D_t(z) =
  exp(i*t*log 2) * zeta'(z+i*t),

Dsym_t(z) =
  (D_t(z) + conj(D_t(conj(z)))) / 2.
```

For real `x`, `Dsym_t(x)=Re(exp(i*t*log 2)*zeta'(x+i*t))`. The phase makes the
`n=2` Dirichlet-series term real and negative at a sufficiently far-right center.

## Fixed geometry

Use one explicit real center `c`, inner radius `r`, and outer radius `R` satisfying:

```text
[0,1] subset closedBall(c,r),
0 < r < R,
```

with `c=20`, `r=20`, and `R=21` preferred. Another fixed rational triple is acceptable only
if it retains the complete source interval and gives explicit analytic and growth margins.

## Fixed proof chain

Full success must compile the following actual chain.

1. For all sufficiently large positive `t`, `Z_t` and `Dsym_t` are analytic on
   `closedBall(c,R)`. Both translated zeta poles must be shown to lie outside the ball.
2. Prove a uniform polynomial bound for actual `riemannZeta s` on the fixed vertical strip
   swept out by the two Jensen circles:

```text
norm(zeta(s)) <= C * (2+abs(Im(s)))^A.
```

   The positive-real-part case may use the compiled Abel estimate. The bounded left part must
   use the functional equation and an explicit fixed-strip Gamma/cosine cancellation bound;
   the global finite-order exponential-square estimate is insufficient.
3. Use a Cauchy derivative estimate on a fixed-radius enlargement to obtain the corresponding
   polynomial bound for `deriv riemannZeta`.
4. Prove a fixed positive lower bound for `norm(Z_t(c))` from absolute convergence far to the
   right.
5. Prove a fixed positive lower bound for `norm(Dsym_t(c))`. The phase-normalized `n=2` term
   must dominate the remaining derivative Dirichlet-series tail.
6. Apply `AnalyticOnNhd.sum_divisor_le` on the fixed outer ball to obtain constants
   `C0,T0` such that, for `t>=T0`, the multiplicity-bearing divisor sums of both
   symmetrizations on the inner ball are at most `C0*log(t+2)`.
7. Prove that every real `x in [0,1]` where the relevant real part vanishes gives a zero of
   the corresponding symmetrization in the inner ball.

## Required theorem-level endpoints

The final API may package constants differently, but exact TargetChecks must expose:

```lean
∃ C T0 : ℝ, 0 ≤ C ∧
  ∀ t : ℝ, T0 ≤ t →
    (∑ᶠ z, divisor (levinsonMontgomeryZetaTopSymm t)
      (Metric.closedBall (20 : ℂ) 20) z : ℝ) ≤
      C * Real.log (t + 2)
```

and the analogous theorem for the phase-normalized actual zeta derivative.

It must also expose the pointwise source alignment on real inputs and the inclusion of every
source crossing in the corresponding inner-ball divisor support.

## Negative controls

1. The global finite-order bound

```text
norm F(z) <= exp(C*(1+norm z)^2)
```

must not be presented as an `O(log T)` producer; Jensen takes its logarithm and retains a
quadratic bound.
2. The derivative symmetrization may not omit its phase normalization. The dominant
`n=2` term rotates with `t` before normalization and has no uniform real-part lower bound.
3. A finiteness theorem at each fixed `t` is not an asymptotic `O(log T)` theorem.
4. An abstract analytic-family theorem whose actual zeta growth or center hypotheses remain
unproved is infrastructure, not full endpoint success.

## Known obstacles and falsification points

- The conjugate-reflected term must be proved analytic; raw complex conjugation is
  antiholomorphic unless paired with conjugation of the input.
- Both zeta and derivative poles move in the auxiliary `z` plane and must be excluded uniformly.
- The fixed-strip bound must cover the outer circle, not only the real segment.
- The zeta derivative center cannot use a nonvanishing theorem alone; Jensen needs a quantitative
  lower bound.
- Divisor multiplicity must be preserved.
- The crossing corollary must use the exact real-input identity, not a numerical approximation.
- The later crossing-to-argument and indented argument-principle layers remain separate unless
  they are actually compiled.

## Success and failure

`FULL_FIXED_ENDPOINT_SUCCESS` requires all seven steps, exact registration, no-sorry
compilation, standard-only axiom audit, empty forbidden scans, full build, and public immutable
evidence.

`MEANINGFUL_PARTIAL` requires at minimum a source-shaped generic Jensen logarithmic-count
theorem, the actual analytic symmetrizations, and the exact first failed actual zeta or
derivative producer. Such a partial must remain registered as infrastructure and cannot close
the H12 node.

Expected full-success classification:

- `result=LEVINSON_MONTGOMERY_ACTUAL_JENSEN_TOP_ZERO_COUNT_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `actual_zeta_top_count_delta=1`;
- `actual_zeta_deriv_top_count_delta=1`;
- `argument_variation_delta=0` unless separately compiled;
- `levinson_montgomery_count_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

## Production gate

No `LeanLab/`, `LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`,
`LeanLab/Riemann/AxiomsAudit.lean`, or `LeanLab.lean` edit is allowed until this docs-only
preregistration passes public Lean Action CI.
