# Route Selection after Hardy--Littlewood Finite Count Closure

Date: 2026-07-29

Status: `H1_SOURCE_NORMALIZATION_LOCAL_SUCCESS / IMPLEMENTATION_PUBLIC_CI_PENDING`

## Closed parent

Campaign `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01` is publicly closed at
receipt commit `3dda5779e156771e873485f1128446fcc1508d70`, Lean Action run `30465646740`.
The closed node proves the finite inference from two supplied square-moment estimates and a
supplied absolute-window lower estimate to many injective actual critical-line zero ordinates.
It proves none of those analytic producers.

## Selection rule

Historical coverage is an omission search. The purpose is to reconstruct decisive human
inferences closely enough to detect an overlooked weakening, normalization defect, or
cross-route repair. A route is not exhausted by inventorying its name or compiling adjacent
infrastructure.

Original conjectures, falsification, and direct RH proof attempts remain open at every
selection. They become the default main line only after the major historical families have
received source-level treatment of their decisive edges.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1 Hardy--Littlewood 1921 | Construct the actual real source coordinate and prove its eta lower estimate before the two source second moments. | The finite count consumer now compiles. H6 already contains an explicit Stirling remainder bound for the exact Gamma factor, so one formerly open H1 normalization premise has a concrete cross-route repair. | **Select one bounded normalization/eta-lower endpoint.** |
| H1 Selberg 1942 | Produce the global mollified first, absolute, and higher moments. | The local sign-change and finite count consumers compile, but the first unformalized source edge is a broad global moment theorem. | Retain as the next quantitative comparison; do not optimize H1 constants. |
| H1 Levinson--Conrey | Produce the actual auxiliary-function right-zero count and complexity-uniform mollified mean value. | Step geometry is compiled; the live producer remains global and downstream of mean-value machinery. | Retain open. |
| H2 zero density | Complete the infinite contour shift and large-value estimates for the actual detector. | The inverse-Mellin line is reconstructed through its first unavailable global contour theorem. | Retain open. |
| H7/H8 spectral | Construct the actual arithmetic operator/kernel with uniform convergence and no spectral pollution. | Finite trace, positivity, and projection mechanisms compile; the live edges are source-global producers rather than an isolated missed inference. | Retain open. |
| H10 function fields | Produce a number-field analogue of Frobenius/cohomological positivity with uniform tails. | Finite rigidity consumers compile, but no actual transfer object is available. | Retain open. |
| H11 zero statistics | Build a statistic sensitive to even one sparse off-line orbit. | Existing normalized statistics formally tolerate persistent sparse exceptions. | Retain open. |
| H12/H14 global counts | Complete the global argument-principle, indentation, and Turing analytic package. | Local contour and finite-height infrastructure exists; the first live theorem remains broad. | Retain open. |

This selection is not justified by H1 implementation momentum. It is justified by the exact
new repair `H6 explicit Stirling remainder -> H1 source normalization`, which can relocate one
named black box to the true moment frontier.

## Primary-source reconstruction

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), pages 287--291 and 296--298:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

Section 2.6 defines the real positive-height source coordinate by an exact positive scaling of
the real critical-line xi coordinate. Equation `(2.61)` then obtains a uniform comparison with
critical-line zeta from Stirling. Lemma 7 controls the eta primitive series; Lemma 11 controls
the moving source integral. Equations `(2.81)`--`(2.87)` and section 2.9 consume these estimates
in the count bridge that is already compiled.

The literal positive-height scaling contains `t^(1/4)`. Extending that same formula to all real
`t` gives a weight that vanishes at zero, so it cannot supply the global strictly positive
weight proof required by `HardyLittlewoodZeroCoordinate`. Define instead

```text
radius(t) = max |t| 1
weight(t) = radius(t)^(1/4) * exp(pi*radius(t)/4) / (t^2 + 1/4)
X(t)      = -weight(t) * hardyXi(t).
```

For `t >= 1` this is exactly the source scaling. Globally, the weight is continuous and
strictly positive, so the extension preserves exact zeros without changing any source-range
statement.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-01`.
- `node`: `H1-HARDY-LITTLEWOOD-SOURCE-NORMALIZATION-ETA-LOWER-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `fixed_endpoint`: compile the positive global extension, exact critical-line zero adapter,
  exact project-xi/Gamma/zeta norm identity, an explicit `t >= 8` zeta lower bound from the H6
  Stirling remainder, the eta factor bound, an exact eta primitive/window error, and the
  absolute-window lower estimate in the shape consumed by
  `hardyLittlewood_source_finite_count`.
- `negative_control`: compile that the unextended algebraic source weight vanishes at zero;
  do not claim a global zero adapter from it.
- `strict_boundary`: no eta primitive-series identification, eta error second moment, source
  moving-integral second moment, asymptotic parameter budget, unconditional linear count,
  positive proportion, H1, or RH.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The selected endpoint moves a premise boundary; it does not optimize a numerical constant.
The persistent RH Goal remains active.

## Selection outcome

The selected endpoint is compiled by `hardyLittlewoodSourceNormalization_endpoint`. The
674-line module constructs the positive global extension, proves exact actual-zero equivalence,
derives the project xi/Gamma/zeta norm identity, uses the H6 explicit Stirling remainder for a
concrete `t>=8` Gamma lower estimate, and obtains the eta pointwise and absolute-window lower
estimates.

This closes the source normalization and `ETA-LOWER` premise locally. It does not identify the
integral primitive with Hardy--Littlewood's Lemma 7 Dirichlet series and does not prove either
second moment. After public closure, compare the Lemma 7 series/moment edge and Lemma 11 source
window moment against Selberg's global moment producer and the leading open nodes in the other
historical families.
