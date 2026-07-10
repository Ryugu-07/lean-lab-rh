# M1 Baez-Duarte Dependency Audit

Date: 2026-07-10

Audit ID: `AUDIT-20260710-M1-01`

## Classification

- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`
- M1/G1 status: open
- RH progress: none

## Sources

1. Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann
   Hypothesis*, arXiv `math/0202141`.
   - URL: `https://arxiv.org/abs/math/0202141`
   - inspected PDF SHA-256:
     `3ce4aff466443c71094affc1f8b6f5f0dd36cb4377dc5d2ceddbd2537c1d1819`
   - relevant locations: Theorem 1.1; Lemmas 2.1 and 2.2; Section 2.2.
2. Michel Balazard and Eric Saias, *The Nyman-Beurling equivalent form for the Riemann
   hypothesis* (ESI 623, 1998).
   - URL: `http://www.esi.ac.at/preprints/esi623.pdf`
   - inspected PDF SHA-256:
     `5cc11918451f92cf9cbc06941271adc41d3f550ade2ec2dae97b0d754b51c815`
   - relevant locations: Theorem 0; Theorems 1 and 2; Lemmas 1 and 2; proof of formula (3).

## Exact M1 Target

The M0 completion audit fixes the published closure side as

```text
baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure
```

M1 must prove this proposition equivalent to `Mathlib.RiemannHypothesis`. The already compiled
real-closure and finite-error forms may be used only through their Lean equivalences.

## Forward Direction

The source route from RH to natural closure has the following dependency graph:

```text
Mathlib.RiemannHypothesis
  -> zeta is zero-free on re(s) > alpha, alpha >= 1/2
  -> Balazard-Saias quantitative Mobius partial-sum estimate
  -> convergence of f_(epsilon,n) to f_epsilon in L2(0,infinity)
  -> f_epsilon belongs to the natural kernel closure
  -> unconditional f_epsilon -> -chi in L2 as epsilon -> 0
  -> complex target closure membership
```

The first arrow is now compiled as

```text
RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re
```

It exactly supplies the zero-free hypothesis in Baez-Duarte's Lemma 2.1. It does not supply the
conclusion of that lemma.

### Available Mathlib Infrastructure

| Dependency | Evidence | Status |
| --- | --- | --- |
| Exact RH definition | `Mathlib/NumberTheory/LSeries/RiemannZeta.lean`, `RiemannHypothesis` | available |
| Zeta nonvanishing on `re(s) >= 1` | `riemannZeta_ne_zero_of_one_le_re` | available |
| Mobius arithmetic function | `ArithmeticFunction.moebius` | available |
| Absolute convergence of its L-series | `LSeriesSummable_moebius_iff` | available only for `re(s) > 1` |
| Zeta times Mobius L-series equals one | `LSeries_zeta_mul_Lseries_moebius` | available only for `re(s) > 1` |
| Complex Mellin integral | `mellin`, `MellinConvergent`, `HasMellin` | available |
| Mellin/Fourier pointwise change of variables | `mellin_eq_fourier` | available |
| Fourier Plancherel on `Lp` | `MeasureTheory.Lp.fourierTransformₗᵢ`, `Lp.norm_fourier_eq` | available |
| Composition on `Lp` by measure-preserving maps | `Lp.compMeasurePreserving` and isometry lemmas | available |
| Whole-space target and natural kernels | M0 definitions in `NymanBeurling.lean` | available |

### Missing Forward Theorems

1. **Balazard-Saias estimate.** No theorem was found that, under zero-freeness on
   `re(s) > alpha`, controls

   ```text
   sum_(a <= n) mu(a) / a^s - 1 / zeta(s)
   ```

   uniformly in a vertical strip with the paper's decay in `n` and polynomial growth in
   `|im(s)|`. Current Mobius L-series results stop at absolute convergence `re(s) > 1`.
2. **Lindelof consequence of RH.** The number-theory search found no zeta Lindelof bound matching
   the bound invoked after equation (2.8).
3. **Fractional-kernel Mellin identity.** No `HasMellin` theorem was found for
   `rho(1/x)` or the positive-natural kernels. The source uses the identity relating this transform
   to `-zeta(s)/s`.
4. **Packaged Fourier-Mellin `L2` isometry.** Mathlib has the pointwise Mellin/Fourier identity and
   Fourier Plancherel separately, but no continuous linear equivalence implementing the weighted
   logarithmic pullback used by the paper.
5. **The two `L2` convergence arguments.** Generic dominated-convergence tools exist, but the
   source-specific majorants and their integrability have not been formalized.

## Reverse Direction

The natural kernel family is contained in the full Beurling family, so the paper treats the reverse
direction as the easy consequence of the base Nyman-Beurling criterion:

```text
natural target closure
  -> full Beurling target closure
  -> Mathlib.RiemannHypothesis
```

The first arrow is finite-span and closure monotonicity. The second arrow is not in mathlib or this
project.

The Balazard-Saias exposition proves the base criterion through a unitary Mellin map into a Hardy
space on a half-plane, the Mellin transform of the modified fractional-part kernels, and an
invariant-subspace/factorization theorem. The current mathlib search found no half-plane Hardy
space, Blaschke product framework, inner/outer factorization theorem, or Beurling-Lax theorem that
matches this proof.

## Dependency Boundary

The audit rejects two misleading shortcuts:

- The existing identity `zeta * L(mobius) = 1` for `re(s) > 1` cannot replace the conditional
  partial-sum theorem needed near the critical line.
- The existing `Lp` Fourier transform cannot by itself replace either the weighted logarithmic
  isometry or the source kernel's Mellin formula.

The first theorem-level dependency on the forward route is the Balazard-Saias quantitative Mobius
estimate. The first theorem-level dependency on the reverse route is the base Nyman-Beurling
criterion, with substantial Hardy-space infrastructure behind it.

## Next Decision

Remain on fixed node M1/G2. The next clean-context batch should inventory whether an external Lean
project already formalizes either the required Mobius estimate or the base Nyman-Beurling/Hardy
criterion. If neither exists, the preferred internal first block is the source fractional-kernel
Mellin identity and the weighted-log `L2` isometry, because those are literature-stable analytic
interfaces used by both criterion routes. The Balazard-Saias estimate itself should not be stated
as an assumption or bypassed by the `re(s) > 1` theorem.

## Gap Accounting

- `assumption_frontier_before`: M0 supplied an exact closure carrier, but M1 dependencies were
  described only broadly.
- `assumption_frontier_after`: RH now supplies the paper's zero-free-half-plane premise in Lean;
  every remaining source step is assigned to an available API or a named missing theorem block.
- `hard_gap_before`: G2 was a broad list of possible analytic infrastructure.
- `hard_gap_after`: G2 is narrowed to two route-critical theorem boundaries, with five explicit
  missing forward blocks and one explicit reverse block.
- `hard_gap_delta`: dependency uncertainty reduced; G1 and the RH equivalence remain unproved.

## Follow-Up

Batch `BATCH-20260710-M1-02` subsequently closed missing forward block 3. Lean now proves the exact
`HasMellin` identity for `rho(1/x)` on `0 < re(s) < 1` and its scaling to every positive-natural
Baez-Duarte kernel. The remaining forward and reverse boundaries listed above are unchanged.
