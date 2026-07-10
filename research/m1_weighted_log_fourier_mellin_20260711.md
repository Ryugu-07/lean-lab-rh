# M1 Weighted-Log Fourier-Mellin L2 Isometry

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-03`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

### Exact Mathematical Statement

The weighted logarithmic change of variables

```text
U(f)(u) = exp(-u/2) f(exp(-u))
```

is a complex-linear isometric equivalence from `L2((0, infinity), dx)` to
`L2(real line, du)`. Its inverse is represented, for `x > 0`, by

```text
U^(-1)(g)(x) = x^(-1/2) g(-log x).
```

Composing `U` with the mathlib `L2` Fourier transform gives the Fourier-Mellin
linear isometric equivalence used by Baez-Duarte. Under mathlib's Fourier normalization,
Mellin frequency `tau` corresponds to Fourier frequency `tau / (2*pi)`.

### Exact Proposed Lean Statements

```lean
abbrev realLineComplexL2 : Type :=
  Lp Complex (2 : ENNReal) volume

noncomputable def weightedLogPullback :
    positiveHalfLineComplexL2 ≃ₗᵢ[Complex] realLineComplexL2

theorem weightedLogPullback_coeFn
    (f : positiveHalfLineComplexL2) :
    weightedLogPullback f =ᵐ[volume]
      fun u : Real =>
        (Real.exp (-u / 2) : Complex) * f (Real.exp (-u))

theorem weightedLogPullback_symm_coeFn
    (g : realLineComplexL2) :
    weightedLogPullback.symm g
      =ᵐ[volume.restrict (Set.Ioi (0 : Real))]
        fun x : Real =>
          (x ^ (-1 / 2 : Real) : Complex) * g (-Real.log x)

noncomputable def baezDuarteFourierMellinL2 :
    positiveHalfLineComplexL2 ≃ₗᵢ[Complex] realLineComplexL2 :=
  weightedLogPullback.trans (MeasureTheory.Lp.fourierTransformₗᵢ Real Complex)

theorem norm_baezDuarteFourierMellinL2
    (f : positiveHalfLineComplexL2) :
    ‖baezDuarteFourierMellinL2 f‖ = ‖f‖
```

The implementation may use definitionally equivalent scalar syntax, but it must expose both
representative formulas and package an actual invertible `LinearIsometryEquiv`. A one-way
`LinearIsometry`, a pointwise identity, or an equality of undefined integrals does not satisfy
the batch target.

### Published Source

Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
arXiv `math/0202141v2`, source lines 226-245. The paper defines

```text
M(f)(tau) = integral_0^infinity x^(-1/2 + i*tau) f(x) dx
```

and states that this Fourier-Mellin map is an invertible isometry on the relevant `L2` space.

URLs:

- `https://arxiv.org/abs/math/0202141`
- `https://export.arxiv.org/e-print/math/0202141`

The inspected v2 source export has SHA-256
`3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.

### Assumption Frontier Before

The exact fractional-kernel Mellin transform and all positive-natural scalings are compiled.
Mathlib supplies the pointwise Mellin-to-Fourier conversion and Fourier Plancherel on complex
`L2`. The weighted logarithmic change of variables connecting the two `L2` carriers is not yet
packaged. No unchecked mathematical statement may be used as a premise.

### Expected Hard-Gap Delta

If and only if the full `LinearIsometryEquiv`, both representative formulas, its Fourier
composition, and the trusted-dependency audit pass, remove the packaged weighted-log
Fourier-Mellin `L2` isometry from G2's missing-forward-block list. The quantitative Mobius
estimate, RH-to-Lindelof bound, source-specific convergence, and reverse base criterion remain
open. The expected result class in that case is `HARD_GAP_REDUCED`.

### Batch Boundary

This batch includes the Jacobian identity, forward and inverse `L2` maps, linearity, norm
preservation, inverse laws, representative formulas, and composition with Fourier Plancherel.
It excludes every Mobius estimate, Lindelof estimate, source-specific convergence argument, and
the base Nyman-Beurling equivalence.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; this continuation resumed from a compacted summary
- `result_class`: `HARD_GAP_REDUCED`

## Result

The pre-registered target compiled in `LeanLab/Riemann/FourierMellin.lean`. Lean now packages

```text
U(f)(u) = exp(-u/2) f(exp(-u))
```

as the invertible complex-linear isometry `weightedLogPullback`. Its inverse has the
source-aligned representative `x^(-1/2) g(-log x)` almost everywhere on the positive half-line.
The definition `baezDuarteFourierMellinL2` composes this equivalence with mathlib's Fourier `L2`
isometry, and `mellin_criticalLine_eq_fourier` verifies the pointwise normalization
`tau -> tau/(2*pi)`.

### Lean Theorems

- `expNeg_quasiMeasurePreserving`
- `eLpNorm_weightedLogForwardFun`
- `eLpNorm_weightedLogInverseFun`
- `weightedLogForwardLinearIsometry`
- `weightedLogForward_inverse`
- `weightedLogPullback`
- `weightedLogPullback_coeFn`
- `weightedLogPullback_symm_coeFn`
- `baezDuarteFourierMellinL2`
- `norm_baezDuarteFourierMellinL2`
- `mellin_criticalLine_eq_fourier`

### Gap Accounting

- `assumption_frontier_after`: the logarithmic change of variables is an unconditional compiled
  `LinearIsometryEquiv`; its forward and inverse representative formulas, Jacobian norm identity,
  Fourier composition, and frequency normalization require no unchecked premise.
- `hard_gap_before`: G2 still listed a packaged weighted-log Fourier-Mellin `L2` isometry among
  the missing forward blocks.
- `hard_gap_after`: that block is closed. The Balazard-Saias quantitative Mobius estimate,
  RH-to-Lindelof bound, source-specific convergence, and reverse base criterion remain open.
- `hard_gap_delta`: one literature-stable analytic block was removed from fixed node G2. Neither
  direction of Baez-Duarte Theorem 1.1, G1, D, nor RH is proved.

### Verification

- full `lake build`: passed, 8582 jobs
- exact typed witnesses in `LeanLab.Riemann.TargetChecks`: passed
- trusted dependencies: only `propext`, `Classical.choice`, and `Quot.sound`
- Lean source incomplete-proof keyword scan: no matches
- explicit `axiom` declaration scan: no matches
- `git diff --check`: passed
