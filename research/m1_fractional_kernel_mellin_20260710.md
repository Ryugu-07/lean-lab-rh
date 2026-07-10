# M1 Fractional-Kernel Mellin Identity

Date: 2026-07-10

Batch ID: `BATCH-20260710-M1-02`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

### Exact Mathematical Statement

For `0 < Re(s) < 1`, if `rho(x)` is the fractional part of `x`, then

```text
integral from 0 to infinity of x^(s-1) * rho(1/x) dx = -zeta(s) / s.
```

### Exact Proposed Lean Statement

```lean
theorem hasMellin_fractionalPartKernel_one
    (s : Complex) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun x : Real => (fractionalPartKernel 1 x : Complex)) s
      (-riemannZeta s / s)
```

The theorem must establish both `MellinConvergent` and the transform value. An equality of
formally undefined integrals is not sufficient.

### Published Source

Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
arXiv `math/0202141v2`:

- abstract and Theorem 1.1 for the criterion;
- source lines 226-245 for the Fourier-Mellin isometry and the identity
  `-zeta(s)/s = integral x^(s-1) rho_1(x) dx`, with `0 < Re(s) < 1`;
- the paper attributes the identity to Titchmarsh, equation (2.1.5).

URLs:

- `https://arxiv.org/abs/math/0202141`
- `https://export.arxiv.org/e-print/math/0202141`

The inspected v2 source export has SHA-256
`3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.

### Assumption Frontier Before

The M0 closure carrier is available, and Audit M1-01 supplies the RH-to-zero-free-half-plane
interface. G2 still lacks five forward analytic blocks, including the fractional-kernel Mellin
identity. No unchecked mathematical statement may be used as a premise.

### Expected Hard-Gap Delta

If the exact `HasMellin` theorem compiles and its trusted-dependency audit passes, remove the
fractional-kernel Mellin identity from G2's missing-forward-block list. The quantitative Mobius
estimate, the weighted logarithmic `L2` isometry, and source-specific convergence remain open.

### Batch Boundary

The Abel continuation infrastructure, the split at `x = 1`, the reciprocal change of variables,
convergence, and the final source identity belong to one analytic edge and are included in this
batch. The weighted logarithmic `L2` isometry is a separate nonmechanical edge and is excluded.

## External Lean Audit

GitHub searches found no Lean implementation of Nyman-Beurling, Baez-Duarte, Balazard-Saias, or
the required critical-strip Mobius estimate. The relevant candidate was:

- Alex Kontorovich et al., `PrimeNumberTheoremAnd`, commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`.

Its three Abel-continuation modules and ten transitive support modules compile against this
project's pinned Lean 4.31/mathlib revision. The final theorem
`riemannZeta_eq_zetaAbelContinuationFormula` has trusted dependencies exactly
`propext`, `Classical.choice`, and `Quot.sound`. The candidate repository contains unrelated
unfinished modules, so the full repository will not be added as a dependency; only the audited
Apache-2.0 source subset required by this proof may be vendored.

`EulerProducts` supplies only absolute-convergence-region Dirichlet-series results already present
in mathlib. The repository named `riemann-hypothesis-lean4` was rejected because its central
symmetry theorem was unchecked.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; this continuation resumed from a compacted summary
- `commit_sha`: resolve the commit titled `research: formalize Baez-Duarte Mellin identity`; the
  exact SHA is recorded in the external task ledger after creation
- `lean_verification`: theorem module, typed witnesses, trusted-dependency audit, and the full
  8581-job project build pass
- `result_class`: `HARD_GAP_REDUCED`

## Result

Lean proves:

```text
hasMellin_fractionalPartKernel_one
hasMellin_baezDuarteKernel
```

The first theorem is the exact pre-registered identity, including convergence. The second gives
the factor `n^(-s)` for every positive-natural kernel `rho(1/(n*x))` used in Baez-Duarte's finite
sums.

The proof also establishes `riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos`, extending the
audited Abel formula from its upstream restricted domain to every `s != 1` with `0 < re(s)` by the
identity theorem. It then splits the Mellin integral at one and applies mathlib's reciprocal-rpow
change of variables.

### Gap Accounting

- `assumption_frontier_after`: the source kernel transform and all positive-natural scaled
  transforms are unconditional Lean theorems. No analytic estimate is assumed.
- `hard_gap_before`: G2 listed the fractional-kernel Mellin identity among five missing forward
  blocks.
- `hard_gap_after`: that block is closed. The quantitative Mobius estimate, RH-to-Lindelof bound,
  weighted-log Fourier-Mellin `L2` isometry, source-specific convergence, and reverse base
  criterion remain open.
- `hard_gap_delta`: one literature-stable analytic block was removed from fixed node G2. Neither
  direction of the full published criterion, G1, D, nor RH is proved.

### Verification

- `lake build`: passed, 8581 jobs
- exact typed witnesses in `LeanLab.Riemann.TargetChecks`: passed
- trusted-dependency output: only `propext`, `Classical.choice`, and `Quot.sound`
- Lean source incomplete-proof keyword scan: no matches
- explicit `axiom` declaration scan: no matches
- all 13 vendored Lean files: byte-identical to upstream commit
- `git diff --check`: passed
