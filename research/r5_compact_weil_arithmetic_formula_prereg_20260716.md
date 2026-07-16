# R5 Compact Weil Arithmetic Formula Preregistration

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

Mode: `DISCOVERY -> PROOF_ATTEMPT_A`

## Fixed Definitions And Proposition

For a smooth compactly supported complex-valued function `f` on the additive logarithmic line,
use the already compiled reflection-symmetric weight

```lean
symmetrizedCompactLaplaceWeight f s =
  (compactLaplaceTransform f s + compactLaplaceTransform f (1 - s)) / 2
```

The physical von-Mangoldt contribution must be defined with the exact reflected branch and
Fourier normalization:

```lean
def compactSymmetrizedVonMangoldtWeight (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
    (f (Real.log n) + f (-Real.log n) / (n : ℂ))

def compactSymmetrizedXiArchimedeanIntegral
    (f : ℝ → ℂ) (c : ℝ) : ℂ :=
  ∫ y : ℝ,
    symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
      logDeriv Gammaℝ ((c : ℂ) + y * I)
```

The indivisible endpoint is equivalent to the following Lean statement:

```lean
theorem symmetrizedCompactLaplaceXi_arithmetic_explicit_formula
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfsupp : HasCompactSupport f) {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) * ∑' p : RiemannXiDivisorZeroIndex,
        symmetrizedCompactLaplaceWeight f
          (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1 +
        compactSymmetrizedXiArchimedeanIntegral f c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n
```

The formal file may use Lean Unicode and the project's existing namespace-qualified names. It
must additionally prove that `compactSymmetrizedVonMangoldtWeight f` has finite support under
`hfsupp`; a merely convergent analytic series is not a source-faithful replacement for the
compact physical prime side.

## Fixed-Gap Entry

- `node_id`: W1
- `gap_id`: G6
- `work_class`: FORMALIZATION
- `hard_gap_before`: the compact-smooth reflection class passes the full multiplicity-bearing zero
  cutoff, but its right-line arithmetic evaluation is open
- `hard_gap_after` on success: the complete zero/pole/GammaR/finite-prime explicit formula is
  compiled for the classical compact-smooth reflection class; quotient/completeness,
  distributional regularization, W2/G7, and RH remain open
- `expected_hard_gap_delta`: 1 at the fixed W1c1 compact arithmetic subedge
- `classification` on success: `BRIDGE_REDUCED`
- `assumption_frontier_before`: pole evaluation, GammaR integrability, prime inversion, prime
  interchange, and finite physical support are not discharged for the compact class
- `assumption_frontier_after` on success: all those obligations follow from only `hf`, `hfsupp`,
  and `hc`

## Five-Candidate Screen

1. **Prove the complete compact-smooth arithmetic explicit formula.** This is the direct successor
   to the publicly closed zero-side cutoff and changes the W1c1 hard-gap ledger. It is selected.
2. **Prove only one-term compact prime Fourier inversion.** This exposes the normalization but
   leaves the pole, GammaR, series interchange, and final formula open. It is rejected as a
   campaign endpoint and retained only as an internal proof-DAG node.
3. **Generalize only the pole residue or GammaR integrability lemmas.** The project already has the
   generic residue skeleton and digamma growth; these are mechanical components and are rejected
   as standalone endpoints.
4. **Prove only finite support of the physical von-Mangoldt weight.** This is source-faithful but
   structurally elementary and cannot count as a fixed-gap result by itself. It remains mandatory
   inside Candidate 1.
5. **Combine the compact separator with the formula into another RH positivity equivalence.** The
   Gaussian family already compiles the reverse-separation criterion. Repeating it for compact
   tests supplies no unconditional sign mechanism and is rejected by the anti-cycling rule.

G3/M2 remains parked by its public three-zero-delta STOP audit, and the previous local-prime
same-sign W2 branch is eliminated. Neither is silently reopened by this campaign.

## Source And Novelty Boundary

- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, Appendix B records
  the explicit formula for smooth compactly supported multiplicative tests, and Appendix C records
  the compact-support Weil criterion: https://arxiv.org/abs/2006.13771
- Compact support makes the finite-place side physically finite. This campaign requires that fact
  in Lean instead of reporting only absolute analytic convergence.
- Mathlib already contains `HasCompactSupport.toSchwartzMap` and pointwise Fourier inversion. The
  new work is the exact scaling and reflection normalization needed by the project's Laplace and
  L-series conventions, plus the complete arithmetic assembly.
- The project already contains `selectedXiPoleRectangleBoundary_eq_residues` and the compact
  zero-side endpoint. Neither states the present arithmetic formula.

This campaign formalizes a classical mechanism. No mathematical or formalization novelty claim is
allowed without a separate audit against mathlib, Isabelle AFP, external Lean repositories, and
the literature.

## Fixed Proof DAG

1. For fixed `c`, turn `x |-> exp(c*x) * f x` and `x |-> exp((1-c)*x) * f x` into Schwartz maps.
2. Relate the two compact Laplace branches on `c+iy` to mathlib's Fourier transform at the exactly
   scaled frequencies `-y/(2*pi)` and `y/(2*pi)`.
3. Apply pointwise Fourier inversion and the real-line scaling substitution. Prove that one
   positive-index L-series term integrates to
   `pi * vonMangoldt n * (f(log n) + f(-log n)/n)`. Handle `n=0` separately.
4. Use inverse-sixth-power compact decay and `c>1` L-series summability to prove individual
   integrability, summability of integral norms, exchange of `tsum` and integral, and summability
   of the explicit prime weight.
5. Derive from `HasCompactSupport f` that the explicit natural-index prime weight has finite
   support, retaining both `log n` and `-log n` branches.
6. Prove full-line integrability of the compact pole pair and top-edge vanishing. Apply the compiled
   generic two-pole rectangle residue identity and reflection to obtain
   `2*pi*symmetrizedCompactLaplaceWeight f 1`.
7. Combine inverse-sixth-power decay with the compiled digamma logarithmic bound to prove full-line
   integrability of the compact GammaR contribution.
8. On every selected finite right edge, split `logDeriv xi` into pole, GammaR, and von-Mangoldt
   terms. Pass each integrable term to the full line along the selected heights.
9. Compare the resulting arithmetic limit with
   `tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral` and use uniqueness of limits to prove
   the exact fixed proposition.

## Adversarial And Boundary Tests

- No real-valuedness or evenness premise on `f` is allowed.
- The first Fourier branch must evaluate at `log n`; the reflected branch must evaluate at
  `-log n` and carry exactly the factor `1/n`.
- The right-line parameter `c` must cancel from every explicit physical prime weight.
- Lebesgue scaling contributes exactly `2*pi` to each unsymmetrized branch and exactly `pi` after
  two-term symmetrization.
- `n=0` and `n=1` must not trigger invalid logarithm, cast, or inverse reasoning; their
  von-Mangoldt factors vanish.
- Pole residues must use `F 0 = F 1` from reflection and yield `2*pi*F 1`, not `pi*F 1`.
- Finite physical prime support must be proved from compact support, not inferred from L-series
  summability.
- The zero sum must retain the complete analytic xi divisor with multiplicity.

## Rejection Conditions

- Reject a final theorem that leaves the prime side as a right-line integral or an unevaluated
  Fourier transform.
- Reject a proof that assumes Fourier inversion, pole convergence, GammaR integrability, prime
  interchange, or finite support as new premises.
- Reject a theorem only for a fixed bump, Gaussian, real/even `f`, or finite Gaussian packet.
- Reject a formula with an unverified sign, `pi`, `2*pi`, `n^c`, or `1/n` normalization.
- Reject `sorry`, `admit`, `native_decide`, project axioms, unsafe declarations, numerical
  evaluators, or resource-limit relaxations.
- If exact prime inversion or generic pole/GammaR control fails under two independent Lean
  approaches, close as `NO_PROGRESS`; do not weaken the endpoint to one internal DAG node.

## Local Result

The exact preregistered theorem compiles in
`LeanLab/Riemann/WeilCompactLaplaceArithmeticFormula.lean`. Lean proves exact scaled Fourier
inversion for both compact branches, including the reflected `1/n` factor; absolute prime
series/integral interchange; finite natural support of the physical von-Mangoldt weight; selected
top-edge pole decay and the exact two-residue full-line integral; an integrable first absolute
moment for the compact symmetric weight; GammaR integrability; and the final arithmetic limit.

The first-moment Schwartz argument is a stronger implementation of proof-DAG item 7 than the
registered inverse-sixth tail split and uses no extra premise. All adversarial boundaries remain:
`n=0` is separate, no evenness or real-valuedness is assumed, `c` cancels from the physical prime
weight, and analytic zero multiplicity is preserved.

The 1,012-line module is diagnostic-free. Exact Targets and TargetChecks compile; the five
selected transitive axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`; all
forbidden scans and `git diff --check` pass; and the full 8,681-job build succeeds locally.

Classification is `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at the compact W1c1 arithmetic
subedge. Preregistration commit `ccebc64b1f3419636461e6fbf968fc55c4f24b8c` passed public Lean
Action CI run `29465070647`, build job `87516408926`, in `1m31s`. Implementation publication and
independent public verification were the next evidence gates; W2/G7, G3/M2, distributional
regularization, and RH remain open.

Implementation commit `55a6406f235a7548bf7f7d53ae5d30014795e9ce` passed public Lean Action CI
run `29466850965`, build job `87521708037`, in `1m51s`. Immutable evidence backfill and its own
public CI remain before campaign closure.
