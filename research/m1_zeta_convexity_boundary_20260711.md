# M1 Zeta Convexity Boundary Closure

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-08`

## Result

- `node_id`: `M1`
- `gap_id`: `G2/F1/zeta-convexity`
- `work_class`: `FORMALIZATION`
- `result_class`: `FORMALIZATION_ONLY`
- `hard_gap_before`: F1 requires Balazard-Saias and an unconditional critical-line zeta exponent
  below `1/2`.
- `hard_gap_after`: unchanged; the critical-line theorem is not compiled.
- `hard_gap_delta`: none under the fixed DAG.

## Compiled Chain

The new module `LeanLab/Riemann/ZetaConvexity.lean` proves:

1. `zetaPoleRemoved` is an entire extension of `(s-1)*riemannZeta s`.
2. Abel summation with `N=ceil(1+|t|)` gives
   `|zeta(1+it)| <= C*(1+|t|)^(1/8)`.
3. Reflection and recurrence give the exact special-line formula
   `|Gamma(1+it)|^2 = pi*t/sinh(pi*t)` for `t != 0`.
4. The Gamma and cosine factors in the zeta functional equation have only square-root growth.
5. Consequently `|zeta(it)| <= C*(1+|t|)^(5/8)`.
6. Multiplication by `s-1` gives boundary powers `9/8` on `Re(s)=1` and `13/8` on `Re(s)=0`.

No general complex Stirling theorem is used for the sharp boundary calculation.

## Remaining Exact Subgap

The next batch must construct Fiori's analytic midpoint symmetrization

```text
f(z)^8 * conj(f(conj(1-z)))^8 /
  ((Q+z)^13 * (Q+1-z)^9)
```

and provide the uniform interior double-exponential growth witness required by
`PhragmenLindelof.vertical_strip`. Boundary estimates only hold asymptotically, so the compact
parts of both edges must also be absorbed into constants. At the midpoint, the quotient estimate
must yield pole-removed exponent `11/8`; division by `|s-1|` then yields the preregistered zeta
exponent `3/8`.

## Assumption Frontier

- `assumption_frontier_before`: no zeta exponent below `1/2`; no corrected weighted strip theorem.
- `assumption_frontier_after`: both sharp polynomial edge inputs are unconditional Lean theorems.
  The weighted midpoint theorem and its growth premise remain absent, and neither is assumed.

## Runtime

- model: Codex, GPT-5 family; exact backend identifier not exposed
- reasoning effort: not exposed
- budget: unbounded persistent-goal budget; no explicit per-round token budget
- compaction: the batch resumed from a generated context summary after preregistration; source,
  worktree, and fixed-DAG state were rechecked before edits continued
