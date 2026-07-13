# G4-F1 Burnol Unitary Model Audit Pre-Registration

Date: 2026-07-13

Batch ID: `AUDIT-20260713-G4-F1-01`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F1`
- `work_class`: `LITERATURE_AND_DEPENDENCY_AUDIT`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

This loop must recover the exact isometric identification behind Burnol's statement that the
original approximation distance `D(lambda)` is the distance from `chi1` to `C_lambda`. It must
produce one implementation boundary that remains useful for F2.

## Source Identity To Audit

Let `M f(t) = t^-1 * integral_(0,t] f(u) du` and `T = (1-M)^-1`. On the critical Mellin line,
`T` has multiplier `(s-1)/s`, which has modulus one. The source identities are

```text
T chi = chi1,                 chi1(t) = (1 + log t) chi(t),
T (rho(1/t)) = -A,
T D_theta = D_theta T.
```

Here

```text
A(t) = floor(1/t) * log(t) + log(floor(1/t)!) + floor(1/t)
```

on the positive half-line, with `A(t)=0` for `t>1`. Scalar normalization and the minus sign do not
change complex spans, so `T` sends `B_lambda` to Burnol's `C_lambda` and preserves the target
distance.

## Anti-Tautology Gate

The loop may not declare F1 complete by defining `C_lambda := T '' B_lambda` or
`A := -T (rho(1/t))` and then using generic isometry lemmas alone. A viable implementation frontier
must include enough source-facing content for F2, specifically:

1. an explicit `chi1` representative and its packaged `L2` element;
2. an explicit source `A` representative, its `L2(0,infinity)` membership, and support in `(0,1]`;
3. a realizable unitary multiplier `(s-1)/s` in the project's Fourier-Mellin normalization;
4. a nondefinitional identification of that unitary on `chi` and on the fractional-part kernel;
5. the induced span equality and exact distance equality.

## Audit Questions

1. Which existing mathlib/project APIs construct multiplication by a measurable unit-modulus
   function as an `L2` linear isometry equivalence?
2. Which Mellin/Fourier formulas are already compiled for `chi` and `rho(theta/t)`?
3. Is the explicit formula for `A` best proved through `(1-M)A=-rho(1/t)`, through its Mellin
   transform `Z(s)=(s-1)zeta(s)/s^2`, or by a piecewise integral calculation?
4. What exact dilation normalization converts the project's kernel `rho(theta/t)` to Burnol's
   `D_theta` convention?
5. Can F1 be implemented as one bounded batch, or must it be split at a genuinely source-level
   dependency rather than a generic Hilbert-space wrapper?

## Result Rules

- `DEPENDENCY_GAP_IDENTIFIED`: the source identities, signs, normalizations, available APIs, and
  first non-tautological Lean theorem boundary are fixed.
- `BRANCH_FALSIFIED`: the claimed distance identification is incompatible with the project's
  kernel/target normalization.
- `FORMALIZATION_ONLY`: only image spaces or generic isometry wrappers are added.
- `NO_PROGRESS`: no implementable source-facing frontier is obtained.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no

## Result

- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- `hard_gap_after`: F1 is split into source-level F1a (explicit `A`) and F1b (unitary distance
  assembly); F1a is selected next.
- `hard_gap_delta`: source signs, normalizations, and implementation boundary fixed; no Lean theorem
  and no RH progress.
- `assumption_frontier_after`: no added premise; `T=(1-M)^-1`, multiplier `(s-1)/s`,
  `T chi=chi1`, and `T rho(1/t)=-A` are source-checked.
- `commit_SHA`: pending
- `public_CI`: pending
