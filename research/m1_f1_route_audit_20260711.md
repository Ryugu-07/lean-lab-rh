# M1 F1 Route Audit: Balazard-Saias and Zeta Growth

Date: 2026-07-11

Batch ID: `AUDIT-20260711-M1-07`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2/F1`
- `work_class`: `AUDIT`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

### Fixed Source Target

Audit the only remaining forward block F1 against the exact published convergence proof. In
particular, determine whether the RH-to-Lindelof bound currently listed in the DAG is logically
necessary, or whether an accurately cited published route replaces it with a weaker unconditional
zeta estimate.

The target is not a local Lean wrapper. The batch may alter F1 only if primary sources establish a
strictly smaller dependency chain and the pinned mathlib/external Lean audit confirms the exact
formal boundary.

### Sources To Compare

1. Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
   arXiv `math/0202141v2`, especially Lemma 2.1 and equations (2.7)-(2.9).
2. Jean-Francois Burnol, *On an Analytic Estimate in the Theory of the Riemann Zeta Function and a
   Theorem of Baez-Duarte*, arXiv `math/0202166v1`, especially Theorems 1.3-1.4 and Section 2.
3. Michel Balazard and Eric Saias, *Notes sur la fonction zeta de Riemann, 1*, Advances in
   Mathematics 139 (1998), 310-321, DOI `10.1006/aima.1998.1760`, Lemma 2.

### Exact Questions

1. What is the weakest zeta-growth theorem needed after the Balazard-Saias partial-sum estimate?
2. Does the published Burnol proof eliminate RH-to-Lindelof from the fixed-epsilon convergence
   chain?
3. Does pinned mathlib or a licensed external Lean project already contain either the required
   Balazard-Saias estimate or the required zeta-growth theorem?
4. What exact theorem should the next F1 formalization batch target without adding an unchecked
   premise?

### Expected Classification

- `HARD_GAP_REDUCED` only if a previously missing F1 theorem is compiled in Lean without unchecked
  premises.
- `DEPENDENCY_GAP_IDENTIFIED` if the source audit strictly narrows or corrects F1 but no named
  theorem is closed.
- `NO_PROGRESS` if the existing F1 description remains unchanged.

### Assumption Frontier Before

The DAG lists F1 as the conjunction of the Balazard-Saias Mobius partial-sum estimate and an
RH-to-Lindelof zeta-growth theorem. No Lean theorem supplies either statement near the critical
line. F2 and F3 are closed.

### Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; compaction occurred after the source audit and initial
  documentation edits, before final verification. The generated continuation summary was checked
  against the worktree, fixed DAG, and preregistration before work resumed.
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`

## Source Findings

### Baez-Duarte Route

The inspected arXiv v2 PDF has SHA-256
`3ce4aff466443c71094affc1f8b6f5f0dd36cb4377dc5d2ceddbd2537c1d1819`. Lemma 2.1 states that,
assuming zeta has no zeros in `Re(s) > alpha`, for `alpha + delta <= Re(s) <= 1`,

```text
sum_(a <= n) mu(a) / a^s
  = 1/zeta(s) + O_(alpha,delta,eta)(n^(-delta/3) (1+|Im(s)|)^eta).
```

Baez-Duarte applies this at `alpha = 1/2`, `delta = epsilon`, then invokes both Lemma 2.2 and the
RH-to-Lindelof consequence to obtain the `L2` majorant in his weighted transform argument.

### Burnol Route

The inspected arXiv `math/0202166v1` PDF has SHA-256
`797d9b4be56e75b1540b63053a2bec9cd7f7ee7d58f6023a142967026ff2c342`. Burnol restates the
Balazard-Saias theorem as Theorem 1.4 and gives a different fixed-epsilon convergence proof in
Section 2. On the critical line `Re(s)=1/2`,

```text
zeta(s)/s * sum_(n <= N) mu(n)/n^(s+epsilon)
```

converges to `zeta(s)/(s*zeta(s+epsilon))`. The error is bounded by

```text
N^(-epsilon/3) * |s|^theta * |zeta(s)/s|.
```

Burnol uses the unconditional classical bound `|zeta(1/2+it)| = O(|t|^(1/4))`. Hence the error
majorant has power `-3/4 + theta` and is square-integrable whenever `theta < 1/4`. The
Balazard-Saias theorem permits arbitrary positive `theta`.

Therefore RH-to-Lindelof is not logically required for the fixed-epsilon closure step. It is a
feature of Baez-Duarte's chosen weighted proof, not a fixed dependency of Theorem 1.1. Burnol's
published route replaces it with an unconditional critical-line convexity bound.

The original Balazard-Saias article is identified as DOI `10.1006/aima.1998.1760`, pages 310-321.
Its full text was not available from the publisher during this audit. The exact theorem statement
was independently checked in both Baez-Duarte Lemma 2.1 and Burnol Theorem 1.4; no claim is made
here about a line-by-line reconstruction of the original proof.

## Lean Ecosystem Audit

### Pinned Mathlib

- `Mathlib.Analysis.Complex.PhragmenLindelof` supplies constant-boundary Phragmen-Lindelof
  principles for vertical and horizontal strips.
- Pinned mathlib has no Balazard-Saias Mobius partial-sum theorem, no Lindelof theorem for zeta, and
  no critical-line zeta convexity estimate with exponent below `1/2`.
- Existing Mobius L-series inversion remains restricted to absolute convergence `Re(s)>1`.

### PrimeNumberTheoremAnd

At audited Apache-2.0 commit `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, the exact upstream
`RiemannZetaConvexity.lean` file compiles against this project and contains no incomplete-proof or
explicit-axiom markers. Its SHA-256 is
`eee771e22aa4e6dcd93fc7180e22915afedc70831360a2ace85607b32bd74997`.

Despite the filename, its strongest relevant theorem is

```text
norm_riemannZeta_lt_linear_im_on_strip:
  norm (zeta z) < 8 + 2*|Im(z)|
```

on `1/2 <= Re(z) < 3` away from small imaginary parts. This exponent-one bound is too weak: after
division by `s` and multiplication by the Balazard-Saias factor `|s|^theta`, it does not give an
`L2` function.

### Other Public Repositories

- GitHub code search found no Lean implementation of the Balazard-Saias theorem.
- `TristenHarr/thegoldenalgebra` commit `7569f12202041f8759a6274651de86361f183b98` contains a
  `ScratchConvexity.lean` exploration, but explicitly leaves the polynomial-boundary
  Phragmen-Lindelof interpolation and a Gamma vertical-strip bound as `axiom`s. The repository has
  no declared license. No code was copied or imported.
- `CBirkbeck/AINTLIB` commit `f190f93db1b51b73a99051f358eb0b45ea45ad80` contains useful Gamma
  strip infrastructure but no matching completed zeta convexity theorem, and the repository has no
  declared license. No code was copied or imported.

## Corrected F1 Frontier

The remaining fixed forward chain may use the published Burnol route:

```text
Mathlib.RiemannHypothesis
  -> zeta nonzero on Re(s)>1/2                         [Lean-closed]
  -> Balazard-Saias partial-sum estimate              [missing]
  + unconditional critical-line zeta convexity bound [missing]
  -> fixed-epsilon transformed L2 convergence
  -> natural-kernel closure membership
  -> epsilon-to-zero convergence via F2 and F3        [quantitative inputs Lean-closed]
```

The next admissible internal theorem target is a sufficient, non-sharp convexity bound, for example

```lean
exists C > 0, forall t : Real, 1 <= |t| ->
  norm (riemannZeta ((1/2 : Complex) + t * Complex.I))
    <= C * (1 + |t|)^(3/8 : Real)
```

Any exponent strictly below `1/2` suffices after choosing the Balazard-Saias `theta` smaller than
the remaining margin. This target requires the genuine polynomial-boundary Phragmen-Lindelof
interpolation and compatible sharp Gamma boundary control; the existing linear strip bound cannot
be repackaged to prove it.

After that theorem is closed, the Balazard-Saias partial-sum estimate remains the final independent
F1 source theorem. It must not be replaced by the `Re(s)>1` Mobius L-series identity.

## Gap Accounting

- `assumption_frontier_before`: F1 was recorded as Balazard-Saias plus RH-to-Lindelof.
- `assumption_frontier_after`: an accurately cited published route removes RH-to-Lindelof and
  replaces it with the unconditional critical-line zeta convexity theorem; the exact sufficient
  exponent and integrability arithmetic are recorded.
- `hard_gap_before`: F1 contained two conditional number-theoretic inputs with no selected first
  formal target.
- `hard_gap_after`: F1 contains the Balazard-Saias theorem plus an unconditional classical
  convexity bound below exponent `1/2`; the latter is selected as the next internal formalization
  target.
- `hard_gap_delta`: dependency structure corrected and narrowed, but no missing theorem was
  Lean-closed.

## Classification

`DEPENDENCY_GAP_IDENTIFIED`. This audit changes the fixed F1 dependency chain but does not count as
RH proof progress or as formalization of a known theorem.

## Verification

- Full `lake build` passes with 8586 jobs.
- The project Lean tree contains no `sorry`, `admit`, explicit `axiom`, or `opaque` declaration.
- `git diff --check` passes.
- No Lean source file changed in this audit; therefore no new theorem or trusted-dependency claim is
  attributed to M1-07.
