# Route Selection after Hardy Tangential-Theta Closure

Date: 2026-07-29

Status: `H1_HARDY_LITTLEWOOD_LINEAR_COUNT_LOCAL_SUCCESS`

## Closed parent

Campaign `LITERATURE-20260729-H1-HARDY-TANGENTIAL-THETA-01` is publicly closed at receipt
commit `af2dece69203d9f9fa83cee9dc896d5a6ec8fe76`, Lean Action run `30436760730`,
build job `90526205899`, passed in `2m44s`.

The closed node proves Hardy's qualitative 1914 theorem: infinitely many actual nontrivial
zeta zeros lie on the critical line. It proves no growth rate for their number, no positive
proportion, H1, or RH.

## Selection rule

Historical coverage is an omission search. A family is not counted as tried because its name,
equivalent statement, or local helper appears in the repository. Its decisive inference must
be reconstructed far enough to identify:

1. the exact source objects and normalization;
2. the theorem-producing implication;
3. the first analytic, arithmetic, spectral, or geometric input that is genuinely unavailable;
4. possible weakened premises or inputs supplied by another route.

Until the major historical families receive this treatment, omission-seeking coverage remains
the default main line. Original conjectures, falsification, and direct RH proof attempts remain
open at every selection.

## Cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H1 Hardy--Littlewood 1921 | Turn two second-moment estimates into a small exceptional set, pair adjacent intervals, and obtain linearly many distinct critical-line zeros. | Hardy's qualitative theorem now compiles, but the earliest quantitative transition has no production module. It is the common counting ancestor of Selberg and later proportion methods. | **Select.** |
| H1 Selberg 1942 | Prove the global first, absolute, and higher moment estimates that feed the compiled squared-mollifier local detector. | The local sign mechanism compiles; the global analytic producer remains broad. The Hardy--Littlewood count bridge is earlier and supplies shared counting logic. | Retain as the next H1 quantitative producer. |
| H1 Levinson--Conrey | Reconstruct the actual auxiliary-function argument variation, right-zero count, Littlewood lemma, and complexity-uniform mollified mean value. | Step geometry compiles, but both the count bridge and mean-value producer remain open. This is downstream of the first quantitative critical-line count. | Retain open. |
| H7 spectral/trace | Prove the uniform arithmetic scalar inequality, simple-even ground state, and compact-uniform convergence to xi without spectral pollution. | Several finite source mechanisms compile. The route has reached explicit uniform spectral and arithmetic obstacles rather than an unexamined historical hinge. | Retain open; do not repeat finite spectral infrastructure. |
| H2 density/moments | Complete the global inverse-Mellin contour shift and large-value count for the actual detector. | The classical detector is reconstructed through its first unavailable global contour theorem. | Retain open. |
| H10 function fields | Produce the actual curve/cohomological object or a number-field transfer with uniform tails. | Finite rigidity consumers compile; the transfer producer is still absent. | Retain open. |
| H11 zero statistics | Construct an absolute-sensitivity statistic that cannot lose one sparse off-line orbit. | Existing normalized statistics are formally compatible with persistent sparse exceptions. | Retain open. |
| H12/H14 global and finite counts | Complete the global argument-principle/Turing analytic package. | Local divisor and contour infrastructure exists; the global producer remains broad. | Retain open. |

## Primary-source reconstruction

Primary source:

- G. H. Hardy and J. E. Littlewood, *The zeros of Riemann's Zeta-Function on the critical
  line*, Mathematische Zeitschrift 10 (1921), 283--317:
  <https://gdz.sub.uni-goettingen.de/download/pdf/PPN266833020_0010/LOG_0029.pdf>.

The source defines, for its real critical-line coordinate `X`,

```text
I(t,H)       = integral from t to t+H of X(u) du,
absI(t,H)    = integral from t to t+H of |X(u)| du.
```

If a window contains no zero, `X` has constant sign there and therefore
`|I(t,H)| = absI(t,H)`. Equations `(2.82)`--`(2.87)` use two second-moment estimates to show
that the strict inequality `|I(t,H)| < absI(t,H)` fails only on a set `S` of measure
`epsilon_H*T`, where `epsilon_H` tends to zero as `H` grows.

Section `2.9` divides `(T,2T)` into pairs of adjacent intervals of length `H`. Unless the first
interval of a pair is entirely contained in `S`, some start in it gives a zero in that pair.
Disjointness makes the selected zeros distinct. Since each failed first interval consumes
measure `H` of `S`, sufficiently few pairs fail, yielding at least `T/(4H)` critical-line
zeros in the dyadic block.

This final measure-to-count inference is not present in the repository. The existing Selberg
module starts from a local strict integral gap and assembles a supplied finite separated family;
it does not derive many such intervals from a quantitative exceptional-set estimate.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01`.
- `node`: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `full_endpoint`: formalize the literal source chain from two L2 estimates to two bad-set
  measure bounds, the union bound, adjacent interval-pair counting, and an injective family of
  actual critical-line zero ordinates for every continuous real coordinate whose zeros agree
  with the actual critical-line zeta zeros.
- `negative_control`: prove that checking only finitely many interval left endpoints is invalid:
  a finite set has measure zero while containing every sampled endpoint. The source needs an
  entire first interval to lie in the exceptional set before charging measure `H`.
- `meaningful_partial`: the exact Chebyshev exceptional-set package and finite pair-count theorem
  compile, with the first unavailable actual-coordinate adapter or zero-witness conversion
  recorded exactly.
- `strict_boundary`: the actual Hardy `Z`/`X` normalization, the Dirichlet-eta lower estimate,
  source Lemma 7 and Lemma 11, unconditional `N_0(T) >> T`, Selberg positive proportion,
  Levinson--Conrey proportions, H1, and RH remain open.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

This campaign studies a missing proof mechanism, not optimization of a numerical constant. The
persistent RH Goal remains active.

## Selection outcome

The selected finite inference is now compiled by
`hardyLittlewood_source_finite_count`. The result preserves the literal whole-interval charge,
the `[T,2T]` restricted measure, natural-number pair counts, and injective actual-zero witnesses.
The endpoint-sampling weakening is formally rejected by a null-set countermodel.

This closes the previously missing count bridge but not the 1921 theorem's analytic producers.
After public closure, the next selection must compare source-faithful production of the
Hardy--Littlewood eta and `X/Z` moments against Selberg's global mollified moments,
Levinson--Conrey's auxiliary count, and the highest-value open nodes in other historical
families. Constant optimization is not a default successor.

The frozen implementation commit `8f3742c62a381293fa201358cf58130d2c333c48` passed public Lean
Action run `30464674314`, build job `90619318156`, in `2m52s`. Proof-source freeze is active
while the docs-only evidence chain is completed.
