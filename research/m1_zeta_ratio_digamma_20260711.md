# M1 Baez-Duarte Zeta-Ratio Bound via Digamma

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-06`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2/F2`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

### Source Problem

Baez-Duarte Lemma 2.2 states that, uniformly for `0 <= epsilon <= epsilon0 < 1/4`,

```text
|zeta(1/2-epsilon+i*tau) / zeta(1/2+epsilon+i*tau)|
  <= K(epsilon0) * (1+|tau|)^epsilon.
```

The displayed Gamma ratio in the source proof is malformed. The functional equation requires

```text
pi^(-epsilon) *
|Gamma(1/4+epsilon/2+i*tau/2) /
 Gamma(1/4-epsilon/2+i*tau/2)|.
```

### Audited Alternative

The Apache-2.0 repository `AlexKontorovich/PrimeNumberTheoremAnd`, commit
`d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, contains
`Gamma/DigammaSeries.lean`. It proves the classical digamma series and the vertical-strip estimate

```text
exists_norm_digamma_le_log:
  exists C > 0, forall z with a <= re z <= b,
    norm (digamma z) <= C * log (|im z| + 2).
```

The exact upstream file compiles unchanged against this project's pinned Lean 4.31/mathlib and has
no incomplete-proof markers. This is the same upstream commit already audited for Batch M1-02.

For fixed imaginary part, apply continuous Gronwall to

```text
u -> Gamma(z+u) / Gamma(z),
```

whose derivative is `digamma(z+u)` times itself. This gives the sufficient, slightly weaker bound

```text
|Gamma(z+delta)/Gamma(z)| <= (|im z|+2)^(C*delta).
```

The constant `C` in the exponent is harmless: choose a smaller `epsilon0 > 0` with
`C*epsilon0 < 1/2`. The resulting power majorant is still in `L2`, so the published criterion proof
goes through without requiring the sharp coefficient one in Baez-Duarte's printed lemma.

### Exact Required Lean Outputs

1. A Gamma-ratio theorem on a fixed positive real strip, derived from
   `exists_norm_digamma_le_log` and Gronwall.
2. The correct `GammaReal`/zeta functional-equation ratio identity, including conjugation symmetry
   and the zero-denominator case.
3. Constants `C, epsilon0, K` with `epsilon0 > 0`, `epsilon0 < 1/4`, and
   `C*epsilon0 < 1/2`, giving a uniform bound sufficient for `L2` domination.
4. A compiled `MemLp` majorant consequence using the existing
   `baezDuarteVerticalMajorant_memLp`.

Representative target shape:

```lean
theorem exists_baezDuarteZetaRatio_bound :
  exists C epsilon0 K : Real,
    0 < C and 0 < epsilon0 and epsilon0 < 1/4 and C*epsilon0 < 1/2 and 0 < K and
    forall epsilon tau, 0 <= epsilon -> epsilon <= epsilon0 ->
      norm (baezDuarteZetaRatio epsilon tau)
        <= K * (1 + |tau|)^ (C*epsilon)
```

The exact exponent/base may be normalized algebraically, but the final statement must expose a
single epsilon-independent `L2` majorant for the whole interval `[0,epsilon0]`.

### Assumption Frontier Before

F2 is the only missing input for the unconditional epsilon-to-zero transformed convergence. The
almost-everywhere pointwise limit, power-majorant integrability, Fourier-Mellin isometry, and
weighted-to-unweighted transfer are compiled. No complex-Gamma ratio estimate is available in the
current project.

### Expected Hard-Gap Delta

If the uniform zeta-ratio bound and its epsilon-independent `L2` majorant compile, remove F2 and
classify `HARD_GAP_REDUCED`. This does not close F1, the reverse criterion, or either direction of
Theorem 1.1.

If only the digamma import, Gamma ratio, or functional-equation identity compiles without the
uniform zeta bound and `L2` consequence, F2 remains open and the result is at most
`DEPENDENCY_GAP_IDENTIFIED` or `FORMALIZATION_ONLY`.

### External Comparison

- Current pinned mathlib has Gamma definitions, recurrence, reflection, conjugation, and zeta
  functional equations, but no digamma series growth theorem or sharp Gamma vertical ratio bound.
- `PrimeNumberTheoremAnd` supplies the Apache-2.0 digamma series/growth theorem used here.
- `CBirkbeck/AINTLIB` commit `f190f93db1b51b73a99051f358eb0b45ea45ad80` has compatible explicit
  Gamma strip bounds, but no repository license and polynomial losses too large for this use; no
  code is copied or imported from it.

### Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no
- `result_class`: `HARD_GAP_REDUCED`

## Outcome

The exact upstream `DigammaSeries.lean` file was vendored unchanged from
`PrimeNumberTheoremAnd` commit `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`. Its SHA-256 is
`815c1f1507058efbef756eb955e055267d5c78eb577d3a6a45d52da3ad6778a4`. The file and the new local
module compile against the pinned Lean 4.31/mathlib environment with no incomplete proofs.

The compiled chain in `LeanLab/Riemann/BaezDuarteZetaRatio.lean` is:

1. `exists_norm_Gamma_div_le_rpow_of_re_mem_Icc`: logarithmic digamma growth plus continuous
   Gronwall gives the ordinary Gamma quotient bound on a positive vertical strip.
2. `riemannZeta_conj`, `riemannZeta_one_sub_div`, and
   `norm_baezDuarteZetaRatio_le_norm_Gammaℝ_div`: the completed-zeta functional equation and
   conjugation reduce the source zeta ratio to the completed Gamma quotient, including the
   denominator-zero branch.
3. `norm_Gammaℝ_div_symmetric_eq` and `exists_norm_Gammaℝ_div_symmetric_le_rpow`: the correct
   symmetric Gamma ratio has the factor `pi^(-epsilon)` and satisfies a polynomial bound with
   exponent `C*epsilon`.
4. `exists_baezDuarteZetaRatio_bound`: with
   `epsilon0 = 1/(8*(C+1))` and `K = 2^(C*epsilon0)`, Lean verifies
   `0 < epsilon0 < 1/4`, `C*epsilon0 < 1/2`, and the normalized uniform zeta-ratio bound.
5. `exists_baezDuarteZetaRatioIntegrand_majorant`: the transformed quotient is pointwise bounded
   for every `epsilon` in `[0,epsilon0]` by the single function
   `5*K*baezDuarteVerticalMajorant (C*epsilon0)`, and that function is `MemLp` for exponent two.

## Assumption Frontier After

F2 is closed without an unchecked premise. The sharp printed exponent-one estimate is not needed:
the weaker exponent `C*epsilon`, obtained from the audited digamma theorem, is sufficient after
shrinking the epsilon interval. The malformed Gamma display in the source is not assumed.

G2 remains open only because the forward fixed-epsilon route still needs F1, the
Balazard-Saias Mobius partial-sum estimate and the RH-to-Lindelof growth input, and the reverse route
still needs the base Nyman-Beurling criterion/Hardy-space factorization. No implication of Theorem
1.1 or RH is claimed.

## Classification

`HARD_GAP_REDUCED`: remove G2/F2 from the fixed DAG. This batch closes a named source theorem and
its exact `L2` domination consequence, rather than adding a local wrapper.

## Verification

- `lake env lean LeanLab/Riemann/BaezDuarteZetaRatio.lean`: passed without warnings.
- `lake env lean LeanLab/Riemann/TargetChecks.lean`: passed.
- `lake env lean LeanLab/Riemann/AxiomsAudit.lean`: passed; representative theorems use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build`: passed with 8586 jobs.
- project Lean scans found no `sorry`, `admit`, explicit `axiom`, or explicit `constant`.
- `git diff --check`: passed.
- the vendored digamma file is identical to the audited upstream file.
