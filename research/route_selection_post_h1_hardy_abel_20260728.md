# Route Selection after H1 Hardy Abel Moment

Date: 2026-07-28

Status: `RERANK_COMPLETE / H11_EXACT_BOUNDARY_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H1-HARDY-ABEL-MOMENT-01` is publicly closed at final-ledger
commit `72f13a727fd71604095c054cb0f0574436c9795a`, Lean Action run `30336884288`,
build job `90203611755`, in `2m9s`.

The frozen implementation proves Hardy's complete high-moment contradiction and infinitely many
actual critical-line zeros conditional on `HardyXiAbelMomentLaw`. Deriving that law from the
Cahen-Mellin/theta transform remains open.

## Fresh cross-family comparison

The ranking criterion is omission discovery inside historical proof mechanisms, not file count
or ease of proving another finite lemma.

| candidate | live edge | omission value | decision |
| --- | --- | --- | --- |
| H1 Hardy | Derive the Abel law from theta inversion. | Directly completes Hardy's source proof, but the preceding campaign just isolated this edge. | Rotate away; retain open. |
| H2 density | Replace finite-line rigidity by an actual-zeta bow exclusion. | High direct value; no source mechanism presently removes the bow obstruction. | Retain open. |
| H7 spectral | Prove true ground-state and compact-uniform convergence. | Strong recent omission candidate, but the next edge is an infinite-dimensional convergence theorem. | Retain open. |
| H10 function field | Build actual curve/cohomology data or a regularized number-field trace. | High analogy value; the finite abstraction layer is already saturated. | Retain open. |
| H11 pair correlation | Audit the moving-window boundary in equation (5.3) before entering Fujii's estimate. | The source suppresses a termwise mismatch inside `O(L^2)`; an exact signed remainder may preserve one-sided information. | **Select.** |
| H12 Speiser | Assemble the global indented count and `O(log T)` comparison. | Source-faithful and valuable, but already deeply reconstructed and globally broad. | Retain open. |

## Source finding

Goldston--Lee--Schettler--Suriajaya, Section 9, writes

```text
integral_0^T (Delta_U N(t))^2 dt
  = sum_{0 < gamma,gamma' <= T+U} d(gamma,gamma')
```

where `d` is the measure of window positions `t in [0,T]` for which both ordinates lie in
`(t,t+U]`. For ordinates at most `T` and above `U`, this is exactly the triangular weight
`U-|gamma-gamma'|`. Ordinates in `(T,T+U]` meet the upper integration boundary, so their exact
weight is a truncated overlap.

The subsequent displayed decomposition replaces those boundary overlaps by full triangular
weights and absorbs the resulting discrepancy into `O(L^2)`. That is sufficient for the
published asymptotic, but it is not a termwise identity. A singleton at ordinate `T+U` has
window-overlap measure zero in `[0,T]`, while its full triangular self-weight is `U`.

The omission-sensitive formulation keeps the exact overlap. It should yield

```text
window second moment
  = interior triangular mass + nonnegative top-boundary remainder,
```

and hence the one-sided inequality

```text
interior triangular mass <= window second moment
```

without charging an upper-boundary `O(L^2)` term. This does not remove Fujii's much larger
analytic error and therefore does not yet exclude one horizontal exception.

## Fixed next campaign

- `campaign`: `LITERATURE-20260728-H11-MOVING-WINDOW-BOUNDARY-01`.
- `node`: `H11-GALLAGHER-MUELLER-EXACT-BOUNDARY-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT`.
- `positive_endpoint`: exact finite short-window square integral, exact pair-overlap kernel,
  interior triangular mass plus nonnegative boundary remainder, a local boundary-count bound,
  the future-singleton counterexample to full-weight replacement, the one-sided inequality,
  and a multiplicity-preserving actual-zeta cutoff specialization.
- `negative_controls`: no claim that equation (5.3) or Proposition 1 is false; no promotion of
  the one-sided identity to an absolute sparse-exception estimate; no assumed low-height zeta
  certificate.
- `strict_boundary`: Riemann-von Mangoldt input, Fujii's second moment, PCC, absolute
  last-exception control, sparse-exception amplification, H11, and RH remain open.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public Lean
  Action CI.

