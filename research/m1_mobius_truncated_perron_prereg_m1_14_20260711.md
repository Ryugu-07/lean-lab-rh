# M1-14 Mobius Truncated Perron Continuation Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-14`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/F1/Balazard-Saias/truncated-Perron`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: proven

This batch continues the unchanged sole target from M1-13. It must prove an absolute constant
`C>0` such that, for every `N>=2`, `T>=1`, and `s` with `1/2<=Re(s)<=1`,

```text
norm(mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s)
  <= C * (N+1)^2 / T.
```

No rectangle boundary identity, positive-side kernel bound, series-integral exchange, or finite-sum
rewrite counts alone.

## Fixed Source

E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann Zeta-function*, second
edition, Lemma 3.12 and Theorem 14.25(A). Audited scan: `/tmp/TitchmarshZeta.pdf`, SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`.

The specialization remains `a_n=mu(n)`, `c=2`, and `x=N+1/2`. The stronger Balazard-Saias
estimate is not identified with this truncated Perron input.

## Starting Frontier

M1-13 Lean-checks the complete negative-side kernel estimate for `0<y<1`. The unresolved exact
mathematical dependency is the positive-side residue contribution. For `a=log y>0`, moving the
vertical contour left crosses the simple pole at `w=0`; the rectangle boundary integral of `1/w`
must contribute `2*pi*i`. Pinned Mathlib supplies no-pole rectangle Cauchy-Goursat and the real
integrals of `c/(c^2+x^2)`, but no ready rectangle residue theorem.

## Batched Proof Blocks

1. prove the oriented rectangle boundary identity for `w^-1` with one interior zero;
2. subtract the removable function `(exp(a*w)-1)/w` and derive the `a>0` kernel estimate for
   `norm(K_T(y)-1)`;
3. rewrite reciprocal zeta on `Re(s+w)>1` as the absolutely convergent Mobius L-series;
4. justify interval-integral interchange with the series;
5. split at `n<x`, apply both kernel estimates, and coarsen the half-integral spacing errors to the
   fixed absolute `C*(N+1)^2/T` bound.

## Classification

- `HARD_GAP_REDUCED`: only if the sole target compiles and the dependency audit is clean.
- `KNOWN_THEOREM_FORMALIZED`: only if the sole target compiles but its fixed-DAG consumer cannot be
  certified.
- `DEPENDENCY_GAP_IDENTIFIED`: only if the sole target remains open but a strictly smaller exact
  source dependency is Lean-checked and the next frontier is precise.
- `FORMALIZATION_ONLY` or `NO_PROGRESS`: if only mechanical support or no exact source boundary is
  improved.

## Runtime

- `model`: Codex, GPT-5 family; exact backend identifier not exposed
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no

## Outcome

The sole target compiles as
`exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le`. The proof contains the checked
`2*pi*i` rectangle residue computation, both kernel sides, dominated series-integral exchange,
half-integral logarithmic spacing, and the final `n^(-3/2)` p-series summation.

Classification: `HARD_GAP_REDUCED`. Remove only
`G2/F1/Balazard-Saias/truncated-Perron`; contour shifting and error balancing remain.

Verification: full `lake build` passed with 8603 jobs. Axiom audit for the residue, positive
kernel, dominated series-integral exchange, and final source theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`; placeholder and explicit-declaration scans are empty.
