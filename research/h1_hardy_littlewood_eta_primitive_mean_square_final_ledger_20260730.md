# H1 Hardy--Littlewood Eta Primitive Mean Square Final Ledger

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-PRIMITIVE-MEAN-SQUARE-01`

Classification:
`FULL_SUCCESS / HARDY_LITTLEWOOD_LEMMA7_CONSUMER_FORMALIZED`

## Public chain

- preregistration `ea5f2f7070acc6d6bfff10e217a47d61bb2f3568`: run `30497243022`,
  job `90728796737`, passed in `2m5s`;
- frozen implementation `6245bdbc920be5129442da9cfa8d4df586e2730d`: run `30499538237`,
  job `90735916929`, passed in `2m21s`;
- immutable evidence `b2a2b5122f0ab326b0c36e3bab614c4c95e598f5`: run `30499767836`,
  job `90736633735`, passed in `2m2s`.

The five-file frozen proof and registration diff remains empty.

## Result

Lean verifies the canonical ordered Hardy--Littlewood source series, its explicit
critical-line tail, and the exact identity

```text
etaPrimitive(t) = -Im(psi(t)-psi(0)).
```

The proof checks the literal finite coefficients and phases, the `n=1` cancellation, finite
derivative and primitive identities, and separate eta-integral and Theta ordered limit
passages. It does not differentiate the infinite series termwise.

For `T>=1`, `0<=u<=T`, and `t in [T,2T]`, the cutoff `N=ceil(3T)` is source-valid and at most
`4T`. The public finite `O(T+N)` mean square plus the explicit ordered tail therefore proves
the uniform shifted source-series `O(T)` estimate. The primitive identity then proves the
eta-window square moment and its exact restricted-measure `lintegral` form required by
`hardyLittlewood_source_finite_count`.

## Historical finding

The public Lemma 3 remainder and the weaker finite `O(L+N)` theorem suffice for the
consumer-strength Lemma 7 upper bound. Lemma 8's full asymptotic and the stronger finite
`O(N/log N)` saving are not necessary premises for this edge.

## Remaining route

The eta-error mean-square node is closed. The first open H1 successors are the actual source-X
moving-window mean square and the Hardy--Littlewood parameter budget. An unconditional linear
critical-zero count, H1, and RH remain open.

Before selecting the next dominant node, rerank these successors against Selberg--Levinson--
Conrey, H2 density, spectral, function-field, zero-statistics, and other historical families.
Original conjectures, falsification, and direct RH attacks remain open. The global RH Goal
remains active.
