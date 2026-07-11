# M1 Balazard-Saias Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-10`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/F1/Balazard-Saias`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

The fixed hard gap is the quantitative Mobius partial-sum estimate quoted as Lemma 2.1 by
Baez-Duarte and as Theorem 1.4 by Burnol. For `1/2 <= alpha < 1`, `delta > 0`, and `eta > 0`,
zero-freeness of zeta in `Re(s) > alpha` is to imply, uniformly for `N >= 2` and
`alpha + delta <= Re(s) <= 1`,

```text
norm (sum_(1 <= n <= N) mu(n) / n^s - 1 / zeta(s))
  <= C(alpha,delta,eta) * N^(-delta/3) * (1 + |Im(s)|)^eta.
```

The constant must not depend on `N` or `s`. The original source is Michel Balazard and Eric
Saias, *Notes sur la fonction zeta de Riemann, 1*, Advances in Mathematics 139 (1998), 310-321,
DOI `10.1006/aima.1998.1760`, Lemma 2.

## Batch Scope

This batch will:

1. encode the exact source statement as a Lean proposition, without declaring it as an axiom or
   theorem;
2. prove the exact RH specialization of its zero-free premise from the existing compiled RH
   bridge;
3. formalize Burnol's transformed-error majorant using the compiled unconditional zeta exponent
   `3/8` and verify the exact remaining integrability margin `eta < 1/8`;
4. attempt to derive the source estimate itself only from available checked analytic-number-theory
   infrastructure.

The batch must not replace the source theorem by the absolutely convergent `Re(s) > 1` Mobius
L-series identity. A theorem conditional on the encoded source proposition is bookkeeping and is
not by itself a hard-gap reduction.

## Success And Classification

- `HARD_GAP_REDUCED`: only if the Balazard-Saias estimate, or a source-equivalent sufficient
  specialization under RH, compiles without an unchecked premise.
- `DEPENDENCY_GAP_IDENTIFIED`: if source and library audit isolates a strictly smaller named
  analytic theorem needed to prove the estimate, but the estimate remains open.
- `FORMALIZATION_ONLY`: if the exact statement and its Burnol consequence compile but the same
  Balazard-Saias theorem remains as a premise.
- `NO_PROGRESS`: if neither the hard gap nor its exact formal boundary improves.

## Assumption Frontier Before

The project has the RH-to-zero-free bridge, exact fractional-kernel Mellin transforms, the
Fourier-Mellin `L2` isometry, the two later convergence blocks F2/F3, and the unconditional bound
`|zeta(1/2+it)| <= C(1+|t|)^(3/8)`. No checked theorem controls Mobius partial sums in the critical
strip. Pinned mathlib only identifies the Mobius Dirichlet series with `1/zeta(s)` in the absolute
convergence half-plane `Re(s) > 1`.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; continuation resumed from the generated task summary and
  was checked against the clean worktree, HANDOFF, target ledger, and fixed hard-gap DAG.
- `result_class`: `FORMALIZATION_ONLY`

## Source Verification

The exact statement was checked independently in:

1. Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann
   Hypothesis*, Lemma 2.1, inspected PDF SHA-256
   `3ce4aff466443c71094affc1f8b6f5f0dd36cb4377dc5d2ceddbd2537c1d1819`;
2. Jean-Francois Burnol, *On an Analytic Estimate in the Theory of the Riemann Zeta Function and a
   Theorem of Baez-Duarte*, Theorem 1.4, inspected PDF SHA-256
   `797d9b4be56e75b1540b63053a2bec9cd7f7ee7d58f6023a142967026ff2c342`.

Both sources quantify uniformly over the full strip and permit every positive height exponent.
The original Balazard-Saias publisher record was identified by PII `S0001870898917601`; no
line-by-line reconstruction of its proof is claimed. Publisher text-mining returned metadata only,
and the interactive full-text endpoint was blocked by a Cloudflare challenge. OpenAlex reported no
repository full text.

## Lean Results

New module: `LeanLab/Riemann/BalazardSaias.lean`.

- `mobiusDirichletPartialSum` is the exact finite complex Dirichlet sum.
- `BalazardSaiasEstimate` encodes the full source theorem as a proposition. It is not an axiom and
  no theorem proves it in this batch.
- `RiemannHypothesis.exists_balazardSaias_specialized_bound` proves that RH supplies the exact
  zero-free premise at `alpha = 1/2`, conditional on an explicit proof of the encoded estimate.
- `exists_norm_riemannZeta_criticalLine_le_rpow_all` extends the compiled `3/8` bound across the
  compact low-height interval.
- `exists_norm_riemannZeta_div_criticalLine_le_rpow` proves the global `-5/8` quotient decay.
- `RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le` proves, with the source theorem
  still explicit, Burnol's exact transformed-error bound

  ```text
  norm(error_N(t))
    <= K * N^(-delta/3) * (1+|t|)^(-5/8+eta).
  ```

- `burnolMobiusMajorant_memLp` checks the sharp remaining margin `eta < 1/8` for `L2(R)`.
- `tendsto_natCast_rpow_neg_delta_div_three` checks that the coefficient tends to zero for every
  `delta > 0`.

The representative trusted-dependency audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Attempted Source Closure

Pinned mathlib has arithmetic Mobius inversion and the absolutely convergent identity in
`Re(s) > 1`. Its theorem `LSeriesSummable_moebius_iff` is explicitly restricted to that absolute
convergence half-plane. The available Abel-summation and coefficient-sum APIs do not derive the
uniform critical-strip estimate from zero-freeness and contain no matching Perron theorem or
quantitative summatory-Mobius input. Reusing the `Re(s) > 1` theorem would therefore change the
source statement and was rejected.

No public Lean implementation of Balazard-Saias was found in the bounded ecosystem audit. Without
the original proof text, inventing a Perron-contour reconstruction in this batch would not satisfy
the source-audit rule. The estimate itself remains the same named analytic-number-theory gap.

## Gap Accounting

- `hard_gap_before`: `G2/F1/Balazard-Saias` was the sole missing forward quantitative theorem.
- `hard_gap_after`: the same Balazard-Saias theorem remains missing. Its complete Burnol consumer
  chain is now Lean-checked and introduces no additional growth or integrability premise.
- `hard_gap_delta`: `0`.
- `assumption_frontier_before`: the project described the Balazard-Saias estimate textually and
  separately knew that a zeta exponent below `1/2` should suffice.
- `assumption_frontier_after`: the exact source quantifiers are encoded; RH supplies the exact
  zero-free input; Lean computes the quotient exponent `-5/8`, the height margin `eta < 1/8`, and
  the vanishing `N` coefficient. `BalazardSaiasEstimate` remains an explicit premise everywhere.

## Classification

`FORMALIZATION_ONLY`. This batch makes the final forward interface auditable and proves its whole
consumer-side quantitative chain, but it does not prove the Balazard-Saias estimate and therefore
does not reduce G2, M1, D, or RH.

