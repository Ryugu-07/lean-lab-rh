# H10 Infinite Reciprocal-Trace Definition Alignment

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01`

Lean module: `LeanLab/Riemann/InfiniteReciprocalTraceAudit.lean`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / IMPLEMENTATION_CI_REQUIRED`

## Source dictionary

| Source object | Lean object | Alignment |
| --- | --- | --- |
| Finite Frobenius eigenvalue family | The existing `alpha : iota -> Complex` with `[Fintype iota]` in `FinitePowerSumRigidity.lean` | The published project theorem already handles finite aggregate power sums and reciprocal pairing. |
| Countably infinite literal transfer | `alpha : Nat -> Complex` | Generic audit model only. No zeta zero, multiplicity, height ordering, or operator eigenvalue is assigned to an index. |
| Ordinary `k`-th power trace | `infiniteSpectrumHasOrdinaryPowerTrace alpha k` | Defined as `Summable (fun n => alpha n ^ k)`. The module never uses the default value of `tsum` on a nonsummable family. |
| Reciprocal functional-equation pairing | `infiniteSpectrumHasReciprocalPairing alpha sigma q` | Exact pointwise identity `alpha(sigma n)*alpha(n)=q` for a permutation `sigma`. Involutivity is not needed for the obstruction. |
| Regularized number-field trace | Deliberately absent | Distributional, cutoff, zeta-regularized, and operator traces are outside the theorem. |

## Compiled infinite obstruction

For any positive natural `k`, ordinary summability gives

`alpha(n)^k -> 0`.

Mathlib's `Equiv.summable_iff` proves the same after reindexing by `sigma`, so

`alpha(sigma(n))^k -> 0`.

Continuity of multiplication makes their product tend to zero. The reciprocal identity rewrites
that product to the constant sequence `q^k`. Uniqueness of limits gives `q^k=0`, and positivity of
`k` gives `q=0`. Thus `q != 0` contradicts ordinary summability of every positive power trace.

No convergence rate, spectral-radius bound, phase recurrence, or power-sum cancellation estimate
is used. This is a prior admissibility obstruction to the literal infinite ordinary-trace model.

## Finite contrast

`finiteReciprocalPairingWitness` uses the one-point spectrum `alpha=1`, identity permutation, and
`q=1`. Every power family over `Fin 1` is summable and the reciprocal identity holds exactly. The
finite witness confirms that reciprocal pairing itself is not contradictory; the obstruction is
its conjunction with an ordinary summable positive-power trace on a countably infinite list.

## Source boundary

The function-field point-count formula has a fixed finite Frobenius spectrum, so its ordinary
power sums are not challenged. The Riemann zeta explicit formula is not an ordinary sum of the
Lean model's `alpha(n)^k`; it includes test functions, archimedean terms, prime terms, and a
specified limiting or distributional interpretation. Connes's trace program is recorded as an
example of a different framework, not as a premise or a target refuted here.

## Deliberately absent claims

- No function-field theorem is refuted or reproved.
- No zeta zero or off-line orbit is constructed.
- No regularized, distributional, or cutoff trace is ruled out.
- No theorem says an infinite reciprocal spectrum cannot exist without ordinary summability.
- No Hilbert-Polya, cohomological, or noncommutative-geometric construction is ruled out.
- RH remains open.

The surviving H10 gap is to construct an actual number-field spectral object and a source-valid
trace/regularization whose prime, archimedean, and spectral sides are proved equal with sufficient
uniform control to locate every nontrivial zero.
