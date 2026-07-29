# Route Selection after Hardy--Littlewood Finite Mean-Square Closure

Date: 2026-07-30

Status: `ETA_ABEL_TRANSFER_SELECTED / PREREGISTRATION_LOCAL`

## Closed parent

Campaign `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01` is publicly
closed at receipt commit `5ad0b8b5795820dee3766c6ca2dd816bb41acdb1`, Lean Action run
`30476269858`, build job `90658643380`. The closed node proves the finite shifted
Hardy--Littlewood polynomial mean square `O(L+N)` and the uniform `O(L)` consequence when
`N<=L`. It does not pass from the finite polynomial to the conditionally convergent source
series.

## Selection rule

Historical coverage is an omission search. A route is selected when a decisive source
inference can be reconstructed closely enough to expose a missed weakening, a hidden
normalization, or the exact first unavailable producer. Adjacency to the last campaign is not
itself a reason for selection.

Original conjectures, falsification, and direct RH proof attempts remain open at every
selection. Numerical-constant optimization is not selected unless the constant controls a
genuine logical threshold.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1 Hardy--Littlewood 1921 | Pass from the uniform eta remainder in Lemma 3 to the logarithmically weighted Theta remainder in Lemma 4. | This is a precise source inference immediately before the compiled finite mean square. The source uses a discrete Abel transform, not a crude termwise tail estimate. | **Select the exact eta-to-Theta transfer.** |
| H1 Selberg / Levinson--Conrey | Produce global mollified moments and the actual auxiliary-function right-zero count. | The consumers compile, but the next source edges are broad global mean-value theorems. | Retain open. |
| H2 zero density | Shift the actual detector through an infinite rectangle with horizontal-edge decay. | The inverse Mellin line compiles; the next edge is a full global contour theorem. | Retain open. |
| H7/H8 spectral | Construct the actual arithmetic operator, ground state, or concrete half-strip RKHS with uniform convergence. | The finite and abstract consumers compile; the missing objects are global producers. | Retain open. |
| H10 function fields | Construct a number-field Frobenius/cohomological analogue with the required positivity and tails. | Finite rigidity compiles, but no actual transfer object is available. | Retain open. |
| H11 zero statistics | Amplify a statistic so that even a sparse off-line orbit is detected. | Existing normalized statistics formally tolerate sparse persistent exceptions. | Retain open. |
| H12/H14 counts and computation | Complete the global argument-principle/Turing analytic package. | Finite consumers compile; the first missing inputs are global analytic bounds. | Retain open. |

The selected edge is materially different from the closed finite mean-square campaign. It
addresses conditional convergence and source-series truncation, not a finite kernel constant.

## Primary-source reconstruction

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), pages 286--287, Lemmas 3--4:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

Lemma 3 states, for a sufficiently small constant `A`,

```text
eta(s) = (1-2^(1-s))*zeta(s)
       = sum_(n<=x) (-1)^(n-1)*n^(-s) + O(x^(-sigma))
```

uniformly for `sigma>=sigma0>0` and `|t|<A*x`. Lemma 4 defines

```text
Theta(s) = sum_(n>=2) (-1)^(n-1)*n^(-s)/log(n)
```

and proves the same `O(x^(-sigma))` truncation order. Its proof writes the weighted tail as
reciprocal-log differences multiplied by the unweighted eta block sums. The positive
differences telescope, while the eta block sums are controlled by two applications of Lemma 3.

This source check rejects the naive proof plan based only on differentiating
`u^(-s)/log(u)`: that estimate carries an extra `|s|` factor and does not preserve
`O(x^(-sigma))` when `|t|` is proportional to `x`.

## Fixed next campaign

- `campaign`: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`.
- `node`: `H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `fixed_endpoint`: formalize the exact finite Abel identity, reciprocal-log telescope,
  bounded-block weighted-tail estimate, and the theorem that a uniform
  `K*N^(-sigma)` eta remainder with `sigma>0` implies ordered convergence of the source Theta
  series and a uniform `C*K*N^(-sigma)` Theta remainder.
- `negative_control`: record that the eta remainder is an input to this endpoint; ordinary
  bounded alternating signs or a tail estimate with an extra `|s|` factor is not silently
  promoted to Hardy--Littlewood Lemma 3.
- `strict_boundary`: no proof of Lemma 3's actual eta remainder, no identification of the
  ordered Theta value with `hardyLittlewoodEtaPrimitive`, no infinite-series second moment, no
  source-X moment, no parameter budget, no unconditional linear count, H1, or RH.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
