# H11 Pair-Correlation Horizontal-Multiplicity Definition Alignment

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H11-PCC-HORIZONTAL-MULTIPLICITY-01`

Primary source: Goldston, Lee, Schettler, and Suriajaya,
arXiv:2503.15449v4, revised 2026-03-30.

Lean module: `LeanLab/Riemann/PairCorrelationHorizontalMultiplicity.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / IMPLEMENTATION_CI_REQUIRED`

## Count dictionary

| Source object | Lean object | Alignment |
| --- | --- | --- |
| The multiset of zeta zeros, with analytic multiplicity expanded into copies | `PccPositiveZetaZeroIndex T` | A dependent sum over distinct positive-height nontrivial zero values, with `Fin (riemannXiZeroMultiplicity s)` indexing their copies. |
| The zero value represented by a multiplicity copy | `pccPositiveZetaZeroValue T` | Forgets the copy index and returns the underlying complex zero. |
| `N(T)`, for `0 < gamma <= T` | `pccPositiveZetaZeroCount T` | Cardinality of the multiplicity-expanded index type. The lower boundary is strict and the upper boundary is inclusive, as in the source. |
| `H(gamma)`, horizontal multiplicity | `horizontalMultiplicity z i` | Number of multiplicity copies whose represented values have the same imaginary part as copy `i`. It depends only on the ordinate fiber, although it is indexed by a copy. |
| `N^circledast(T) = sum_rho H(gamma)` | `pccPositiveZetaHorizontalPairCount T` | Ordered equal-ordinate pair count, including the diagonal, implemented as `horizontalPairCount`. |
| Number of simple critical zeros | `simpleCriticalCount z` | Counts copies whose ordinate fiber has size one and whose real part is `1/2`. Under source reflection, a singleton horizontal fiber is automatically one simple critical zero. |
| `rho -> 1 - conj(rho)` at fixed positive ordinate | `pccPositiveZetaZeroIndexReflection T` | An involutive permutation of multiplicity copies preserving the cutoff and realizing the source reflection exactly. |

## Analytic multiplicity alignment

The source uses the analytic multiplicity of a zeta zero. The project already has an entire-xi
divisor API, so the finite index is built from `riemannXiZeroMultiplicity`. This is not a silent
change of multiplicity:

`burnolZetaZeroMultiplicity_eq_riemannXiZeroMultiplicity`

proves equality at every `IsNontrivialZero s`. The proof constructs the local analytic unit
`riemannXiZetaUnit`, proves it is analytic and nonzero near `s`, and proves locally
`riemannXi = riemannXiZetaUnit * riemannZeta`. Hence multiplication by the unit does not change
the analytic order.

## Source hinge and compiled statements

The source finite inequality

`N_simple_critical(T) >= 2 * N(T) - N^circledast(T)`

is represented without truncated natural subtraction as

`two_mul_card_le_simpleCriticalCount_add_horizontalPairCount`:

`2 * N(T) <= N_simple_critical(T) + N^circledast(T)`.

The exact finite localizer is
`all_critical_of_horizontalPairCount_eq_card`: if the ordered equal-ordinate pair count equals the
total multiplicity count, every horizontal fiber is a singleton and every represented point lies
on the critical line.

`riemannHypothesis_of_exactHorizontalPairCountCofinal` consumes the stronger condition
`PccExactHorizontalPairCountCofinal`: above every real bound there is a cutoff with exact equality.
This condition is not the PCC or HMH asymptotic and is not proved in the module.

## Sparse-exception falsification model

`PccExceptionalIndex n` consists of two reflected off-line points at the same ordinate and `n`
distinct simple critical points. Lean proves:

- total count `n + 2`;
- horizontal pair count `n + 4`;
- simple critical count `n`;
- both normalized pair and simple-critical counts tend to `1`;
- an off-line point exists for every `n`.

Therefore reflection plus normalized horizontal-count convergence cannot eliminate a fixed or
sufficiently sparse off-line defect. This falsifies only the attempted promotion from density one
to RH; it does not falsify the cited source theorem or PCC.

## Deliberately absent assumptions

- PCC is not a Lean premise and is not claimed proved.
- The source asymptotic `N^circledast(T) = (1 + o(1)) T L` is not replaced by exact equality.
- Riemann-von Mangoldt asymptotics are not needed for the finite hinge or countermodel.
- No arithmetic amplification of one actual off-line zeta orbit is assumed.
- The final RH theorem is explicitly conditional on exact cofinal equality.

The surviving H11 gap is to prove an arithmetic mechanism that makes every off-line orbit create
non-sparse horizontal excess, or to prove the exact cofinal condition by another route.
