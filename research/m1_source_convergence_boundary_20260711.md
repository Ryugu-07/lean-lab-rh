# M1 Baez-Duarte Source-Convergence Boundary

Date: 2026-07-11

Batch ID: `BATCH-20260711-M1-04`

## Pre-Registration

- `node_id`: `M1`
- `gap_id`: `G2`
- `work_class`: `FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

### Exact Mathematical Statement

For a real exponent parameter `beta < 1/2`, the vertical-line majorant

```text
tau -> (1 + |tau|)^(-1 + beta)
```

belongs to complex `L2(real line)`. In particular, for `epsilon < 1/4`, the source majorant

```text
tau -> (1 + |tau|)^(-1 + 2*epsilon)
```

belongs to `L2(real line)`. This is the integrability assertion used after the source's bound on
the Fourier-Mellin transform of `X_epsilon f_(2*epsilon,n)`.

### Exact Proposed Lean Statements

```lean
def baezDuarteVerticalMajorant (beta tau : Real) : Complex :=
  ((1 + |tau|) ^ (-1 + beta) : Real)

theorem baezDuarteVerticalMajorant_memLp
    (beta : Real) (hbeta : beta < 1 / 2) :
    MemLp (baezDuarteVerticalMajorant beta) (2 : ENNReal) volume

theorem baezDuarteFirstConvergenceMajorant_memLp
    (epsilon : Real) (hepsilon : epsilon < 1 / 4) :
    MemLp (baezDuarteVerticalMajorant (2 * epsilon))
      (2 : ENNReal) volume
```

### Pre-Implementation Boundary Refinement

Primary-source inspection shows that the unconditional `epsilon -> 0` Fourier-Mellin passage is
pointwise only away from ordinates `tau` where `zeta(1/2 + i*tau) = 0`. The source needs only
almost-everywhere convergence. Mathlib exposes `isDiscrete_riemannZetaZeros`, so this batch also
includes the exact non-quantitative subedge:

```lean
def baezDuarteCriticalLineZetaZeroOrdinates : Set Real :=
  {tau | riemannZeta ((1 / 2 : Complex) + tau * Complex.I) = 0}

theorem baezDuarteCriticalLineZetaZeroOrdinates_countable :
    baezDuarteCriticalLineZetaZeroOrdinates.Countable

theorem ae_riemannZeta_criticalLine_ne_zero :
    forall_ae tau, riemannZeta ((1 / 2 : Complex) + tau * Complex.I) != 0

theorem ae_tendsto_baezDuarteZetaRatio_one :
    forall_ae tau,
      Tendsto (fun epsilon =>
        riemannZeta ((1 / 2 : Complex) - epsilon + tau * Complex.I) /
          riemannZeta ((1 / 2 : Complex) + epsilon + tau * Complex.I))
        (nhds 0) (nhds 1)
```

This refinement is source-required, not a newly invented local target. It does not include the
uniform ratio bound of Lemma 2.2.

The batch must also replace the broad phrase `source-specific convergence` in the fixed gap
ledger by a source-line-accurate list of the still missing quantitative and almost-everywhere
inputs. A generic dominated-convergence wrapper alone does not satisfy the batch target.

### Published Source

Luis Baez-Duarte, *A Strengthening of the Nyman-Beurling Criterion for the Riemann Hypothesis*,
arXiv `math/0202141v2`, Section 2.2, from equation `mfepsilonn` through the end of the proof.

URLs:

- `https://arxiv.org/abs/math/0202141`
- `https://export.arxiv.org/e-print/math/0202141`

The inspected v2 source export has SHA-256
`3bdb7d9da83314b685572aaa739b02e4d075cb3dec9ffccc6a66faee932818c0`.

### Assumption Frontier Before

The exact kernel Mellin transform, positive-natural scaling, weighted-log `L2` equivalence,
Fourier Plancherel, and frequency normalization are compiled. G2 still records
`source-specific convergence` as one broad block. No source majorant, zeta ratio estimate,
critical-line almost-everywhere limit, or weighted-to-unweighted transfer is compiled.

### Expected Hard-Gap Delta

The expected result class is `DEPENDENCY_GAP_IDENTIFIED`. If the exact `MemLp` theorems compile,
the source's majorant-integrability assertion is closed, but the whole convergence block remains
open. The ledger must identify whether each remaining step depends on:

1. the Balazard-Saias Mobius partial-sum estimate;
2. the RH-to-Lindelof bound;
3. Baez-Duarte Lemma 2.2, the zeta-ratio/Gamma vertical-strip estimate;
4. an almost-everywhere limit away from critical-line zeta zeros;
5. the source's weighted-to-unweighted `L2` transfer on `(0,1)` and `(1,infinity)`.

No full convergence claim, criterion implication, or RH implication may be recorded unless all of
its premises are Lean theorems.

### Batch Boundary

This batch includes the exact power-majorant `L2` proof and the primary-source dependency audit of
both convergence passages. It excludes the Balazard-Saias estimate, Lindelof, complex Gamma
vertical-strip asymptotics, the full `f_(epsilon,n)` construction, and either final convergence
theorem.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: no
- `result_class`: `DEPENDENCY_GAP_IDENTIFIED`

## Source-Accurate Convergence Matrix

### Fixed Epsilon, n Tends to Infinity

| source edge | status after this batch | remaining dependency |
| --- | --- | --- |
| finite Fourier-Mellin transform formula | not yet packaged | assemble the compiled kernel Mellin identity for the paper's finite `f_(2*epsilon,n)` sum |
| pointwise convergence of the transformed partial sums | missing | Balazard-Saias quantitative Mobius partial-sum estimate |
| uniform bound `K_epsilon (1+|tau|)^(-1+2*epsilon)` | missing | the same Mobius estimate together with the RH-to-Lindelof bound used by the source |
| square integrability of the displayed power majorant for `epsilon < 1/4` | **Lean-closed** | none |
| transformed `L2` convergence by domination | blocked by the preceding pointwise/uniform estimates | generic dominated-convergence APIs are already available in mathlib |
| transfer from weighted convergence to ordinary full-line `L2` convergence | missing | formalize the source's `(0,1)`/`(1,infinity)` split and its uniform tail estimate |

### Epsilon Tends to Zero

| source edge | status after this batch | remaining dependency |
| --- | --- | --- |
| critical-line zero ordinates form a null exceptional set | **Lean-closed** | none |
| zeta ratio tends pointwise to one away from that set | **Lean-closed** | none |
| almost-everywhere pointwise convergence of the zeta ratio | **Lean-closed** | none |
| a square-integrable power majorant | **Lean-closed** once the source supplies an exponent below `1/2` | none |
| uniform zeta-ratio bound in the epsilon range | missing | Baez-Duarte Lemma 2.2; current mathlib has no matching complex-Gamma vertical-strip ratio estimate |
| transformed `L2` convergence by domination | blocked by Lemma 2.2 | generic dominated-convergence APIs are already available |
| transfer from weighted convergence to ordinary full-line `L2` convergence | missing | the same source-specific split/tail argument |

## Compiled Lean Results

File: `LeanLab/Riemann/BaezDuarteConvergence.lean`

- `baezDuarteVerticalMajorant_memLp`;
- `baezDuarteFirstConvergenceMajorant_memLp`;
- `baezDuarteCriticalLineZetaZeroOrdinates_countable`;
- `baezDuarteCriticalLineZetaZeroOrdinates_measure_zero`;
- `ae_riemannZeta_criticalLine_ne_zero`;
- `tendsto_baezDuarteZetaRatio_one_of_ne_zero`;
- `ae_tendsto_baezDuarteZetaRatio_one`.

The trusted-dependency audit for the three representative final theorems reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Primary-Source Audit Notes

- The source defines its Fourier-side Hilbert space with an interval printed as
  `L2((infinity,infinity), ...)`; context requires the whole real line.
- In the displayed proof of Lemma 2.2, the TeX Gamma numerator and denominator are identical even
  though the lemma statement requires a shifted Gamma ratio. The statement can be used only after
  reconstructing and independently proving the intended ratio estimate.
- In the `x > 1` tail passage, the printed exponent appears as `1+epsilon` where the surrounding
  `f_(2*epsilon,n)` indexing suggests `1+2*epsilon`. This must be resolved from the definitions
  before formalizing the weighted-to-unweighted transfer; no exponent was silently chosen here.

## Final Delta

- `assumption_frontier_before`: both convergence passages were represented by one undifferentiated
  source-specific block.
- `assumption_frontier_after`: power-majorant `L2` membership and the almost-everywhere zeta-ratio
  limit are unconditional Lean theorems. The exact blockers are now the Balazard-Saias estimate,
  RH-to-Lindelof growth, Lemma 2.2's Gamma/zeta-ratio bound, and the source-specific tail transfer.
- `hard_gap_before`: G2 contained a broad `source-specific convergence` item.
- `hard_gap_after`: G2 remains open, with both convergence chains split into named quantitative
  dependencies and Lean-closed subedges.
- `hard_gap_delta`: dependency uncertainty was reduced, but neither full convergence theorem nor
  either implication of Baez-Duarte Theorem 1.1 was proved.
