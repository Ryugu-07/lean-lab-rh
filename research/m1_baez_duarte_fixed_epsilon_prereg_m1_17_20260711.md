# M1-17 Baez-Duarte Fixed-Epsilon Convergence Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-17`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/forward/fixed-epsilon-natural-convergence`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

The sole target is the RH-conditional fixed-positive-epsilon convergence theorem from
Baez-Duarte, Section 2.2 and Corollary 3.1. For every admissible fixed `delta>0`, package the exact
source finite sums

```text
f_(delta,N)(x) = sum_(1<=a<=N) mu(a) * a^(-delta) * rho(1/(a*x))
```

in real `L2(0,infinity)` and prove under `Mathlib.RiemannHypothesis` that they converge in norm to
some `f_delta`. The limit must be proved to belong to `baezDuarteKernelClosure`.

An existential limit is source-equivalent at this stage: the batch does not claim the subsequent
unconditional theorem `f_delta -> -chi` as `delta -> 0`, the final RH-to-closure implication, or
the complete M1 equivalence.

## Source Audit

Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*, arXiv
`math/0202141v2`, equations (2.3)-(2.9), proves for fixed sufficiently small positive epsilon that
`f_(epsilon,n)` converges in `L2(0,infinity)` under RH. Corollary 3.1 records this fixed-epsilon
convergence as part of an equivalent criterion. Burnol's published modification replaces the
RH-to-Lindelof estimate in this passage by a critical-line zeta bound and the same Balazard-Saias
partial-sum estimate; M1-09 and M1-15 compile exactly those inputs.

## Exact Lean Route

1. Package `baezDuarteMobiusApprox delta N` as an element of `positiveHalfLineL2` and prove each
   term lies in `baezDuarteKernelSpan`.
2. Prove the classical critical-line Mellin transform of each finite sum is

   ```text
   -zeta(s)/s * mobiusDirichletPartialSum N (s+delta).
   ```

3. Prove, for the required `L1 intersect L2` representatives, compatibility between Mathlib's
   abstract `Lp.fourierTransformLi` and the classical Fourier integral. This is a dependency, not
   a batch result by itself.
4. Use `exists_norm_burnolMobiusTransformedError_le_compiled` and
   `burnolMobiusMajorant_memLp` to show the transformed finite approximants form a Cauchy sequence
   in `L2`.
5. Pull Cauchy convergence back through the Fourier-Mellin linear isometry. Completeness supplies
   a norm limit.
6. Since every finite approximation is in the natural-kernel span and the closure is closed, put
   the limit in `baezDuarteKernelClosure`.

## Existing Checked Inputs

- `hasMellin_baezDuarteKernel`;
- `baezDuarteFourierMellinL2` and `mellin_criticalLine_eq_fourier`;
- `RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le_compiled`;
- `burnolMobiusMajorant_memLp`;
- `tendsto_natCast_rpow_neg_delta_div_three`;
- `baezDuarteKernelSpan` and `baezDuarteKernelClosure`.

None asserts convergence of the source finite approximants.

## Classification Rules

- `HARD_GAP_REDUCED`: the sole source convergence target compiles and the limit is connected to
  the existing natural-kernel closure.
- `KNOWN_THEOREM_FORMALIZED`: norm convergence compiles but closure membership is not connected.
- `DEPENDENCY_GAP_IDENTIFIED`: the target remains open but the exact classical/L2 transform or
  convergence dependency is reduced to a strictly smaller source-level theorem.
- `FORMALIZATION_ONLY`: only transform compatibility or finite-sum interfaces compile.
- `NO_PROGRESS`: the fixed forward frontier is unchanged.

## Gap Frontier Before

- `hard_gap_before`: F1 provides the transformed pointwise error bound, but no Lean theorem says
  the source finite Möbius approximants converge in physical `L2` or have a closure limit.
- `assumption_frontier_before`: no unchecked premise; classical/L2 Fourier compatibility and the
  Cauchy assembly are absent.
- `hard_gap_after`: the fixed-positive-`delta` RH-conditional natural Mobius convergence theorem
  is compiled, including membership of its limit in `baezDuarteKernelClosure`; the unconditional
  `delta -> 0` convergence to the target and the final forward assembly remain open.
- `hard_gap_delta`: remove only `G2/forward/fixed-epsilon-natural-convergence`.
- `assumption_frontier_after`: no unchecked transform-compatibility or Balazard-Saias premise;
  the compiled theorem assumes only `Mathlib.RiemannHypothesis`, `0 < delta`, and
  `delta <= 1/2`.
- `result_class`: `HARD_GAP_REDUCED`.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; work resumed from a generated context summary, then the
  fixed target, preregistration, source equations, worktree, and existing theorem interfaces were
  rechecked before implementation.
- `verification`: full `lake build` passes with 8607 jobs; exact target witnesses, incomplete-proof
  scan, explicit-declaration scan, trusted-dependency audit, and `git diff --check` pass. The
  classical/L2 compatibility theorem, Cauchy theorem, and final fixed-delta theorem use only
  `propext`, `Classical.choice`, and `Quot.sound`. Public commit `2f1503e` passes Lean Action CI
  run `29154261012`, build job `86548687415`, in 1m52s.
