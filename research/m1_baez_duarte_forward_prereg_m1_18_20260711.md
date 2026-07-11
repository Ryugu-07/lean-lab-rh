# M1-18 Baez-Duarte Forward Criterion Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-18`

## Fixed Target

- `node_id`: `M1/D`
- `gap_id`: `G2/forward/delta-to-zero-and-assembly`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

The sole target is the remaining forward implication of the exact M0-aligned published carrier:

```text
Mathlib.RiemannHypothesis
  -> baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure.
```

If this compiles, combine it with the M1-16 reverse theorem to state the exact Lean equivalence.
The batch must not claim a proof of RH itself.

## Source Audit

Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*, arXiv
`math/0202141v2`, Theorem 1.1 and equations (2.4)-(2.9), proves under RH that the fixed-positive
epsilon natural Mobius sums converge to explicit functions `f_epsilon`, then proves
unconditionally that `f_epsilon -> -chi_(0,1)` in `L2(0,infinity)` as epsilon decreases to zero.
The second passage uses:

```text
M(X_epsilon f_(2 epsilon))(tau)
  = -zeta(1/2-epsilon+i tau)
      / (zeta(1/2+epsilon+i tau) * (1/2-epsilon+i tau)),
```

almost-everywhere convergence of the zeta ratio, Lemma 2.2 domination, Plancherel, and the same
split-at-one weighted-to-unweighted argument used for the finite sums.

## Exact Lean Route

1. Package the finite weighted source functions `X_epsilon f_(2 epsilon,N)` directly in `L2`.
2. Prove their exact finite Mellin/Fourier formula (2.7), avoiding a noncanonical choice of the
   M1-17 fixed-delta limit.
3. Combine the uniform zeta-ratio majorant, a fixed-line RH zeta subpower bound, and the compiled
   Balazard-Saias estimate to prove finite transformed convergence for every fixed epsilon.
4. Use `ae_tendsto_baezDuarteZetaRatio_one` and
   `exists_baezDuarteZetaRatioIntegrand_majorant` to obtain transformed `L2` convergence to the
   transform of `-chi_(0,1)`.
5. Pull convergence back through Plancherel and the weighted-log isometry. Prove the weighted
   target itself tends to the target, then apply `tendsto_norm_zero_of_baezDuarte_weightedTail`.
6. Diagonalize the finite-sum and epsilon limits, then apply the exact finite weighted-tail
   estimate to obtain unweighted natural Mobius sums arbitrarily close to the negative target.
7. Combine with `baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis`.

## Existing Checked Inputs

- `RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2`;
- `hasMellin_baezDuarteMobiusApprox`;
- `fourier_toLp_eq_toLp_fourier` and `baezDuarteFourierMellinL2`;
- `ae_tendsto_baezDuarteZetaRatio_one`;
- `exists_baezDuarteZetaRatioIntegrand_majorant`;
- `tendsto_norm_zero_of_baezDuarte_weightedTail`;
- `baezDuarteTargetL2_mem_closure_iff_complex` and the M1-16 reverse theorem.

None asserts the fixed target.

## Classification Rules

- `KNOWN_THEOREM_FORMALIZED`: the exact forward implication and resulting equivalence compile;
  close M1/G2 and the criterion-to-Mathlib bridge D.
- `HARD_GAP_REDUCED`: the full source `epsilon -> 0` physical `L2` convergence compiles but final
  closure transport remains genuinely open.
- `DEPENDENCY_GAP_IDENTIFIED`: the target remains open but one strictly smaller source-level
  analytic dependency is isolated.
- `FORMALIZATION_ONLY`: only pointwise identification, transform compatibility, or packaging
  compiles.
- `NO_PROGRESS`: the fixed forward frontier is unchanged.

## Gap Frontier Before

- `hard_gap_before`: fixed-positive-delta convergence has a closure limit, but no theorem proves
  those limits tend to the target as delta decreases to zero or derives RH-to-closure.
- `assumption_frontier_before`: no unchecked premise; explicit-limit identification and the
  second source convergence passage are absent.
- `hard_gap_after`: the exact strong positive-natural Baez-Duarte criterion is compiled in both
  directions; no M1 criterion-formalization gap remains.
- `hard_gap_delta`: remove `G2/forward/delta-to-zero-and-assembly`, close `G2`, `M1`, `G1`, and `D`.
- `assumption_frontier_after`: the equivalence assumes no proposition beyond the two theorem
  sides. No new axiom, `sorry`, or encoded analytic premise occurs.

## Result

`result_class`: `KNOWN_THEOREM_FORMALIZED`.

Compiled witnesses include
`RiemannHypothesis.baezDuarteComplexTargetL2_mem_kernelClosure` and
`riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure`.

The final theorem is an equivalence criterion. It does not construct the approximants
unconditionally and does not prove `RiemannHypothesis`.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; one automatic context compaction occurred before the
  continued M1-18 implementation.

## Verification Record

- full `lake build`: 8608 jobs, success;
- incomplete-proof scan: no `sorry`, `admit`, or `sorryAx` in project Lean files;
- explicit declaration scan: no project `axiom` or `constant` declarations;
- `git diff --check`: success;
- final theorem axiom set: `propext`, `Classical.choice`, `Quot.sound` only.
