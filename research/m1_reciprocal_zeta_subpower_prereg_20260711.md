# M1 Reciprocal-Zeta Subpower Pre-Registration

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-12`

## Fixed Target

- `node_id`: `M1`
- `gap_id`: `G2/F1/Balazard-Saias`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

The fixed gap remains the Balazard-Saias quantitative Mobius partial-sum estimate. This batch works
only on the reciprocal-zeta growth theorem used in its Perron-contour proof.

## Sole Target

Formalize the RH specialization of Titchmarsh (14.2.6):

```text
RiemannHypothesis ->
for every delta > 0 with delta <= 1/2 and every eta > 0,
there is C > 0 such that, uniformly for
  1/2 + delta <= Re(s) <= 1,
  norm (riemannZeta s)^(-1) <= C * (1 + |Im(s)|)^eta.
```

The constant may depend on `delta` and `eta`, but not on `s`. Compact low-height values must be
absorbed into the same constant. The conclusion must compile without `sorry`, `admit`, a new axiom,
or an explicit assumption of any reciprocal-zeta growth estimate.

This is the exact source-equivalent sufficient specialization used by the project's RH-to-Burnol
route. A theorem only in `Re(s) > 1`, a pointwise convergence statement, or a fixed polynomial
exponent is not an admissible substitute.

## Source

E. C. Titchmarsh, revised by D. R. Heath-Brown, *The Theory of the Riemann Zeta-function*, second
edition, Theorem 14.2 and equations (14.2.1)-(14.2.6). Inspected scan:
`/tmp/TitchmarshZeta.pdf`, SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`.

The source proof uses:

1. polynomial growth of zeta on the Borel outer circle;
2. Borel-Caratheodory for a normalized analytic branch of `log zeta`;
3. Hadamard's three-circles theorem between a bounded right-half-plane circle and the Borel circle;
4. the fact that `exp(O((log t)^theta)) = O(t^eta)` when `theta < 1`.

## Checked Starting Frontier

Available without unchecked premises:

- RH implies zeta has no zeros for `Re(s) > 1/2`;
- `Complex.exists_differentiableOn_eqOn_exp_comp_of_isSimplyConnected` and
  `exists_riemannZeta_differentiableLogBranch` provide analytic logarithm branches on zero-free,
  pole-free simply connected domains;
- `Complex.borelCaratheodory` is available;
- Hadamard three-lines and vertical-strip Phragmen-Lindelof are available, but no packaged
  three-circles theorem is present;
- the Abel continuation formula is available for `Re(s) > 0`;
- the Mobius L-series inverse identity is available only for `Re(s) > 1` and may be used solely to
  normalize/bound the logarithm on the source's right-hand circle, not as the target conclusion.

## Batch Proof Blocks

The implementation may batch the following source-faithful mechanical blocks, but none counts as
the batch result by itself:

1. an explicit polynomial zeta bound on the bounded real strip containing the Borel circles,
   derived from the Abel continuation formula;
2. a uniform bound for a normalized logarithm at a fixed right-half-plane center, using absolute
   convergence there;
3. a translated Borel-Caratheodory estimate on the inner circle;
4. a three-circles consequence derived from existing checked complex-analysis infrastructure;
5. the real asymptotic conversion from a sublinear power of `log` to an arbitrary positive power.

## Classification Rules

- `KNOWN_THEOREM_FORMALIZED`: the sole target compiles and its trusted-dependency audit is clean.
- `HARD_GAP_REDUCED`: only if the compiled theorem is also connected into a source-equivalent
  proof of the Balazard-Saias estimate and removes a fixed DAG edge.
- `DEPENDENCY_GAP_IDENTIFIED`: the sole target remains open, but a strictly smaller exact source
  theorem is isolated and its boundary is Lean-checked.
- `FORMALIZATION_ONLY`: only generic or mechanical blocks compile while the mathematical frontier
  is unchanged.
- `NO_PROGRESS`: no source-proof boundary improves.

## Assumption Frontier Before

The analytic logarithm branch is checked. No theorem bounds its norm by a sublinear power of
`log |t|`, and no uniform arbitrary-power estimate for reciprocal zeta is available in the critical
strip. The truncated Perron and contour-balance blocks remain downstream.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no

## Result

- `result_class`: `HARD_GAP_REDUCED`
- `hard_gap_before`: `G2/F1/Balazard-Saias` still required the RH reciprocal-zeta subpower input,
  truncated Perron, and contour-error balancing.
- `hard_gap_after`: the RH reciprocal-zeta subpower input is closed; truncated Perron and
  contour-error balancing remain before the Balazard-Saias estimate itself is proved.
- `hard_gap_delta`: remove `G2/F1/Balazard-Saias/reciprocal-zeta-subpower` only.
- `assumption_frontier_before`: an analytic logarithm branch existed, but no quantitative norm
  bound or reciprocal-zeta growth theorem was available in the critical strip.
- `assumption_frontier_after`: `RiemannHypothesis.exists_reciprocalZeta_subpower_bound` proves the
  sole preregistered target with no reciprocal-growth assumption.

## Compiled Route

1. The Abel continuation formula gives a coarse linear zeta bound on the Borel outer circle.
2. Absolute convergence in `Re(s) >= 3` bounds the principal logarithm on the fixed small circle.
3. The M1-11 logarithm branch plus `Complex.borelCaratheodory` gives an
   `O_delta(log(2+|t|))` bound on the inner circle.
4. `norm_le_three_circles_of_differentiableOn_ball` derives the needed three-circles theorem from
   Mathlib's checked Hadamard three-lines theorem.
5. Calling Borel with `delta/2` leaves a positive radial margin. Lean proves the resulting uniform
   interpolation exponent `theta_delta` satisfies `0 <= theta_delta < 1`.
6. The logarithm branch is therefore `O_delta((log(2+|t|))^theta_delta)`. Exponentiation and the
   real-power asymptotic give arbitrary positive reciprocal-zeta powers at large height.
7. The zeta residue at `1` controls a pole neighborhood; compactness controls the remaining finite
   rectangle. The shifted height is converted from `2+|t|` to `1+|t|` by changing the constant.

## Compiled Theorem

```text
RiemannHypothesis.exists_reciprocalZeta_subpower_bound
```

The theorem has exactly the sole-target quantifiers and conclusion. Balazard-Saias itself is not
proved or assumed.

## Runtime Continuation

- A generated compaction summary was received after the Borel-Caratheodory theorem was partially
  implemented. The continuation rechecked the fixed target, exact source geometry, worktree, and
  remaining Lean errors before proceeding.

## Verification

- `lake env lean LeanLab/Riemann/ReciprocalZetaSubpower.lean`: pass.
- `lake build`: pass, 8602 jobs.
- `#print axioms` for the sole target: only `propext`, `Classical.choice`, and `Quot.sound`.
- tracked Lean `sorry`/`admit` scan: no matches.
- project Lean explicit `axiom`/`constant`/`opaque` declaration scan: no matches.
- `git diff --check`: pass.
