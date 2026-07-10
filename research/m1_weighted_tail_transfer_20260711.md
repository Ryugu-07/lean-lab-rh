# M1 Baez-Duarte Weighted-Tail Transfer

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-05`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2/F3`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

### Source Reconstruction

Baez-Duarte defines

```text
f_(delta,n)(x) = sum_(a=1)^n mu(a) / a^delta * rho(1/(a*x)).
```

For `x > 1` and `a >= 1`, `0 < 1/(a*x) < 1`, so the fractional part is exactly
`1/(a*x)`. Therefore

```text
f_(delta,n)(x) = (1/x) * sum_(a=1)^n mu(a) / a^(1+delta).
```

With `delta = 2*epsilon`, the exponent is `1+2*epsilon`. The `1+epsilon` printed in equation
`forx>1` is incompatible with the definition and is treated as a source typo, not as a premise.

### Exact Mathematical Statement

Let `epsilon >= 0`, and let `f,w` be real `L2(0,infinity)` functions such that

```text
w(x) = x^(-epsilon) f(x)              almost everywhere,
f(x) = m/x for x > 1                  almost everywhere.
```

Then

```text
||f||_2^2 <= (1 + 2*epsilon) ||w||_2^2,
||f||_2   <= sqrt(1 + 2*epsilon) ||w||_2.
```

The first inequality uses `x^(-epsilon) >= 1` on `(0,1]` and the exact tail integrals

```text
integral_(1,infinity) (m/x)^2 dx = m^2,
integral_(1,infinity) (m*x^(-1-epsilon))^2 dx = m^2/(1+2*epsilon).
```

Consequently, for a family with `epsilon_i -> 0` (or fixed epsilon), weighted `L2` convergence
to zero implies ordinary `L2` convergence to zero whenever every error has the displayed `m_i/x`
tail. This is exactly the transfer invoked twice in Section 2.2.

### Proposed Lean Statements

```lean
theorem baezDuarte_weightedTail_norm_sq_le
    (epsilon m : Real) (hepsilon : 0 <= epsilon)
    (f w : positiveHalfLineL2)
    (hweighted : w =ae[volume.restrict (Set.Ioi 0)]
      fun x => x ^ (-epsilon) * f x)
    (htail : forall_ae x volume.restrict (Set.Ioi 0),
      1 < x -> f x = m / x) :
    ||f|| ^ 2 <= (1 + 2 * epsilon) * ||w|| ^ 2

theorem baezDuarte_weightedTail_norm_le ... :
    ||f|| <= Real.sqrt (1 + 2 * epsilon) * ||w||

theorem tendsto_norm_zero_of_baezDuarte_weightedTail ...
```

The batch must also instantiate the fixed inequality for an actual positive-natural finite kernel
combination using `baezDuarte_finsupp_sum_eq_reciprocalMoment_div_of_one_lt`.

### Published Source

Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
arXiv `math/0202141v2`, Section 2.2, equations `fepsilonn`, `mfepsilonn`, and `forx>1`, and the
sentence immediately following `forx>1`.

Source export SHA-256:
`3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.

### Assumption Frontier Before

Weighted-log/Fourier-Mellin isometry, majorant integrability, and the almost-everywhere zeta-ratio
limit are compiled. G2/F3 still lacks a theorem transferring either source weighted convergence
back to ordinary `L2(0,infinity)` convergence. The source's printed exponent is unresolved in the
ledger.

### Expected Hard-Gap Delta

If the fixed norm inequality, convergence theorem, and natural-kernel instance compile without
unchecked premises, remove F3 from G2 and classify the batch `HARD_GAP_REDUCED`. F1 and F2 remain
open, so neither weighted convergence premise nor either direction of Theorem 1.1 may be claimed.

If only tail integrals or a generic uninstantiated wrapper compile, classify at most
`FORMALIZATION_ONLY`. If the quotient-level `Lp` statement requires an additional unavailable
analytic premise, record it as `DEPENDENCY_GAP_IDENTIFIED` and keep F3 open.

### Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no
- `result_class`: `HARD_GAP_REDUCED`

## Implementation Result

File: `LeanLab/Riemann/BaezDuarteTailTransfer.lean`.

Compiled declarations:

- `baezDuarteMobiusApprox`;
- `baezDuarteMobiusApprox_eq_dirichletTail_of_one_lt`;
- `baezDuarteMobiusApprox_two_mul_eq_dirichletTail_of_one_lt`;
- `integral_Ioi_weighted_moment_mul_self`;
- `baezDuarte_weightedTail_norm_sq_le`;
- `baezDuarte_weightedTail_norm_le`;
- `tendsto_norm_zero_of_baezDuarte_weightedTail`;
- `baezDuarte_finsupp_norm_sq_le_of_weighted`.

The source exponent is now Lean-checked from the finite Mobius definition: above one,
`f_(2*epsilon,n)` has coefficient sum with exponent `1+2*epsilon`. No interpretation of the
printed `1+epsilon` was assumed.

The main theorem is quotient-level: `f` and `w` are actual elements of
`Lp Real 2 (volume.restrict (Ioi 0))`, and their representative formulas are required only almost
everywhere. The proof obtains square-integrability from `Lp.memLp`, splits the positive-half-line
measure into `Ioc 0 1` and `Ioi 1`, and proves the exact tail scaling before recombining the
integrals.

The convergence theorem permits a varying exponent and proves

```text
epsilon_i -> 0,
||x^(-epsilon_i) f_i||_2 -> 0
  ==> ||f_i||_2 -> 0
```

for source-shaped `m_i/x` tails. A fixed positive epsilon is the constant-family special case.
The final finite-sum theorem instantiates the estimate with the project's actual
`baezDuarteKernelL2` combination and its compiled reciprocal-moment tail identity.

## Final Gap Accounting

- `assumption_frontier_before`: weighted convergence did not imply the ordinary convergence needed
  by either source passage; the tail exponent was ambiguous in the printed source.
- `assumption_frontier_after`: weighted-to-unweighted convergence follows from the compiled norm
  inequality whenever the error has the source's `m/x` tail. The finite natural-kernel case and the
  correct `1+2*epsilon` exponent are compiled. No quantitative zeta or Mobius estimate is assumed.
- `hard_gap_before`: G2 contained F1, F2, and F3.
- `hard_gap_after`: remove F3. G2 still contains F1 (Balazard-Saias plus RH-to-Lindelof) and F2
  (Baez-Duarte Lemma 2.2 plus complex-Gamma vertical-strip control).
- `hard_gap_delta`: one fixed source analytic block is closed. Neither weighted convergence premise,
  either implication of Theorem 1.1, G1, D, nor RH is proved.

## Verification

- `lake env lean LeanLab/Riemann/BaezDuarteTailTransfer.lean`: passed;
- exact statement witnesses in `LeanLab.Riemann.TargetChecks`: passed;
- full `lake build`: passed with 8584 jobs;
- representative trusted dependencies: only `propext`, `Classical.choice`, and `Quot.sound`.
