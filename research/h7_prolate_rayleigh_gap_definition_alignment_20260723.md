# H7 Prolate Rayleigh-Gap Definition Alignment

Date: 2026-07-23

Campaign: `DISCOVERY-20260723-H7-PROLATE-RAYLEIGH-GAP-01`

Production module: `LeanLab/Riemann/WeilGroundStateRayleighGap.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Source-to-Lean object map

| Mathematical or source object | Lean object | Alignment |
| --- | --- | --- |
| Finite real Weil matrix | `A : Matrix ι ι Real` | Generic finite real matrix. The actual pole, prime, and archimedean entries are not instantiated. |
| Normalized ground vector | `xi : ι -> Real` with `xi dot xi = 1` | A selected unit eigenvector. Simplicity, evenness, and source cutoff dependence are not derived. |
| Ground eigenvalue | `mu : Real` with `A *v xi = mu • xi` | Exact finite eigen-equation. It is not identified with the lowest source eigenvalue without the gap hypothesis. |
| Positive ground-state gap | `delta : Real` and `gap_lower` | A Rayleigh lower bound by `delta` on the orthogonal complement of `xi`. It is a certificate field, not a theorem about the source matrix. |
| Prolate coefficient vector | generic `x : ι -> Real` | The consumer accepts any vector. No current declaration constructs the normalized source prolate coefficients. |
| Rayleigh excess | `weilRayleighExcess A mu x` | Exactly `x dot (A *v x) - mu * (x dot x)`. For unit `x`, this is the usual quadratic value above `mu`. |
| Projective defect | `weilProjectiveDefect xi x` | Exactly `x dot x - (xi dot x)^2`. For unit `xi`, it is the squared norm of the orthogonal remainder; for unit `x` it is `1-(xi dot x)^2`. |
| Orthogonal remainder | `weilGroundLineRemainder xi x` | Exactly `x - (xi dot x) • xi`. |
| Quantitative consumer | `WeilQuantitativeGroundStateCertificate.gap_mul_projectiveDefect_le` | Proves `delta * defect <= excess` for every finite test vector. |
| Ratio consumer | `WeilQuantitativeGroundStateCertificate.projectiveDefect_le_ratio` | Divides by the certified positive gap. It does not prove that a source ratio is small. |
| Limit consumer | `tendsto_projectiveDefect_zero_of_le_ratio` | An abstract one-parameter squeeze theorem. A source double-limit order or cofinal diagonal remains to be defined. |

## Exact finite theorem

The certificate assumes matrix symmetry, unit normalization of `xi`, the exact eigen-equation,
`0 < delta`, and the orthogonal-complement inequality

```text
delta * (y dot y) <= weilRayleighExcess A mu y
```

whenever `xi dot y = 0`. Lean proves that `x` decomposes as its ground-line component plus an
orthogonal remainder, that the Rayleigh excess is unchanged after deleting the ground-line
component, and that the remainder norm squared equals the projective defect. Therefore

```text
delta * weilProjectiveDefect xi x <= weilRayleighExcess A mu x
```

and positivity of `delta` gives the division form. This is a finite-dimensional variational
identity and does not use any unproved source assertion.

## Collapsing-gap falsification model

`weilCollapsingGapMatrix epsilon` is the exact matrix `diag(0, epsilon)` for `epsilon > 0`.
Its certified ground vector is `(1,0)` and the test vector is `(0,1)`. With
`epsilon_n = 1/(n+1)`, Lean proves:

```text
rayleighExcess epsilon_n -> 0
projectiveDefect = 1
rayleighExcess epsilon_n / epsilon_n = 1.
```

Thus absolute Rayleigh excess tending to zero cannot promote a prolate approximation to
ground-line convergence when the spectral gap may collapse. Any source proof using this
variational route must control excess relative to the gap, or prove a separate uniform positive
gap.

## Source and claim boundary

- The locked Connes sources do not state the Rayleigh-excess-to-gap conjecture. It is original and
  remains open.
- The module contains no actual prime sum, digamma term, pole block, prolate function, or
  two-parameter source matrix.
- The generic certificate does not prove source simple-even structure, identify the true ground
  state, or establish a lower bound for its gap.
- Projective convergence is convergence to a line. Choosing a coherent sign and normalization for
  function convergence requires an additional source theorem.
- The abstract `Nat` sequence does not select the Galerkin-before-prime-cutoff order used by the
  source. That limit architecture remains open.
- No transform convergence to `Xi`, real-zero persistence theorem, RH implication, or RH theorem
  is asserted here.
- The concrete ratio may not be used as a premise unless it is later instantiated and proved in
  Lean without placeholders.

## Current trust audit

- Production source compiles directly without warnings after its dedicated module build.
- One proven generic Target and one open source-ratio Target are registered.
- Twelve exact TargetChecks pass.
- Eleven selected axiom prints depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Production forbidden scan is empty for `sorry`, `admit`, `native_decide`, custom `axiom`,
  `opaque`, and `unsafe`.
- Full-project build passes all `8,750` jobs; only pre-existing replay warnings appear.
