# M1 Mobius Truncated Perron Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-13`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/F1/Balazard-Saias/truncated-Perron`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: dependency gap identified; sole target remains in progress

The fixed gap remains the Balazard-Saias quantitative Mobius partial-sum estimate. M1-12 closed
the RH reciprocal-zeta subpower input. This batch may work only on the source-equivalent truncated
Perron input; it may not count a standalone kernel identity, integral rewrite, or finite-sum
transport as the result.

## Source

E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann Zeta-function*, second
edition, Lemma 3.12, equations (3.12.1)-(3.12.2), and Theorem 14.25(A). Inspected scan:
`/tmp/TitchmarshZeta.pdf`, SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`, PDF pages 35-36 and 189-190.

For a Dirichlet series `f(z) = sum a_n n^(-z)`, Lemma 3.12 approximates the partial sum below a
nonintegral `x` by the truncated vertical integral of `f(s+w) x^w / w`. Its errors are controlled
by the absolute-convergence tail, the coefficients near `x`, and the distance from `x` to the
nearest integer. Theorem 14.25(A) specializes this to `a_n = mu(n)`, `f = 1/zeta`, `c = 2`, and
`x` half an odd integer.

The quantitative theorem quoted by Baez-Duarte as Lemma 2.1 is Balazard-Saias, *Notes sur la
fonction zeta de Riemann, 1*, Lemma 2, DOI `10.1006/aima.1998.1760`. That stronger theorem is not
identified with Titchmarsh's pointwise convergence statement. Its original article is closed-access
in the current source audit; the exact quoted statement is independently visible in Baez-Duarte's
paper and already encoded as `BalazardSaiasEstimate`.

## Sole Lean Target

Define the source vertical integral using `x = N + 1/2` and `w = 2 + i v`:

```text
mobiusTruncatedPerronIntegral N T s
  = (1 / (2*pi)) * integral from -T to T of
      zeta(s + 2 + i*v)^(-1) * x^(2+i*v) / (2+i*v) dv.
```

Prove, without `sorry`, `admit`, a new axiom, or a Perron estimate premise:

```text
exists C > 0, for every N >= 2, T >= 1, and complex s with
  1/2 <= Re(s) <= 1,
norm(mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s)
  <= C * (N+1)^2 / T.
```

The constant is absolute and must not depend on `N`, `T`, `s`, or `Im(s)`. A theorem only for a
fixed `N`, a fixed `s`, an infinite-height limit, or a bound that assumes the desired finite-sum
approximation is not an admissible substitute.

## Why This Specialization Is Source-Equivalent

For `x = N + 1/2`, the set of positive integers below `x` is exactly `{1,...,N}`, while the
distance to either nearest integer is `1/2`. With `|mu(n)| <= 1`, `c = 2`, and
`1/2 <= Re(s) <= 1`, every explicit error in (3.12.1) is bounded by an absolute multiple of
`(N+1)^2/T`. On the integration line, `Re(s+w) > 1`, so Mathlib's checked absolutely convergent
Mobius L-series identity may be used there without replacing the target critical-strip statement.

## Checked Starting Frontier

- `mobiusDirichletPartialSum` is already the exact finite sum used downstream.
- Mathlib proves absolute convergence of the Mobius L-series exactly for `Re(z) > 1` and its
  product identity with zeta there.
- Mathlib has interval integrals, rectangle Cauchy-Goursat, and norm bounds for interval integrals.
- Neither pinned Mathlib nor the audited external Lean modules expose Perron's formula or a
  truncated Perron kernel estimate.
- M1-12 supplies reciprocal-zeta subpower only after the future contour moves left; it is not
  needed to justify the initial `c = 2` line.

## Batched Proof Blocks

The following may be implemented together, but none counts alone:

1. parameterize the vertical complex integral as a real interval integral;
2. prove the truncated Perron kernel estimate by rectangle integration and explicit edge bounds;
3. justify interchange of the absolutely convergent Mobius series and the finite interval integral;
4. split coefficients at `n < x` and sum the kernel errors;
5. specialize `x = N + 1/2` and coarsen every source error to the sole target.

## Classification Rules

- `HARD_GAP_REDUCED`: the sole target compiles, is connected to the existing
  `mobiusDirichletPartialSum`, and its trusted-dependency audit is clean.
- `KNOWN_THEOREM_FORMALIZED`: the sole target compiles but the fixed-DAG connection cannot yet be
  certified.
- `DEPENDENCY_GAP_IDENTIFIED`: the sole target remains open, but a strictly smaller exact theorem
  needed in its proof is isolated and Lean-checked.
- `FORMALIZATION_ONLY`: only mechanical integral or finite-sum infrastructure compiles.
- `NO_PROGRESS`: no exact source boundary improves.

## Gap Accounting Before

- `hard_gap_before`: `G2/F1/Balazard-Saias` lacks truncated Perron and contour balancing.
- `expected_hard_gap_delta`: remove only
  `G2/F1/Balazard-Saias/truncated-Perron` if the sole target compiles.
- `assumption_frontier_before`: RH reciprocal-zeta subpower is checked; no matching truncated
  Perron theorem is available; `BalazardSaiasEstimate` remains explicit and unproved.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; resumed from a generated summary and rechecked the fixed
  target, source audit, worktree, and first compiler state

## Batch Outcome

The sole target did not compile and is not counted as closed. Lean checks the complete `a<0`
rectangle-deformation argument and the source-specialized theorem
`norm_truncatedPerronKernel_two_le_of_lt_one`. The exact missing theorem is now the positive-side
residue contribution: a rectangle crossing zero must contribute `2*pi*i` for `1/w`, yielding a
bound on `norm(truncatedPerronKernel 2 T y - 1)` for `1<y`. Pinned Mathlib has the required
no-pole rectangle Cauchy-Goursat theorem but no ready rectangle residue theorem.

Classification: `DEPENDENCY_GAP_IDENTIFIED`, `hard_gap_delta=0`. After the residue/kernel theorem,
the remaining preregistered blocks are absolute Mobius-series interchange, splitting at `n<x`,
and coarsening the half-integer source errors to `C*(N+1)^2/T`.

Verification: full `lake build` passed with 8603 jobs. Axiom audit for the Mobius L-series identity,
negative-side contour estimate, and source-specialized kernel bound reports only `propext`,
`Classical.choice`, and `Quot.sound`; placeholder and explicit-declaration scans are empty.
