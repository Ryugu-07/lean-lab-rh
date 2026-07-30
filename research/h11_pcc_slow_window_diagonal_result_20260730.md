# H11 PCC Slow-Window Diagonal Result

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H11-PCC-SLOW-WINDOW-DIAGONAL-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN`

## Result

`LeanLab/Riemann/PCCSlowWindowDiagonal.lean` is a 173-line no-sorry implementation of the
preregistered moving-window endpoint.

For an error array `e(n,k)` and an external cap `cap(n)`, Lean defines a positive stage `k` to be
admissible at `n` when:

- `k<=n`;
- `k<=cap(n)`;
- `abs(e(n,k))<1/k`.

The selected window is the greatest admissible stage below `n`. If `cap` tends to infinity and
`e(n,k)` tends to zero for every fixed positive `k`, then every fixed positive stage eventually
becomes admissible. Lean therefore proves:

- the selected natural-number window tends to infinity;
- it is eventually positive and stays below `cap`;
- its moving-stage error tends to zero;
- its reciprocal real lower endpoint tends to zero;
- its real upper endpoint tends to infinity.

No uniform convergence over an expanding parameter interval is assumed.

## Source cap

Taking `cap(n)=Nat.sqrt(L(n))` gives an explicit source-shaped corollary. Whenever this square-root
cap tends to infinity, Lean constructs a moving window with

`window(n)^2 <= L(n)`

eventually, while retaining both moving-window limits and error convergence.

## Negative control

Lean defines `pccFastDiagonalError(n,k)` to be zero when `k<=n` and one otherwise. For every fixed
`k`, this error tends to zero. Along the fast diagonal `k=n+1`, however, the error is identically
one and does not tend to zero.

Thus fixed-parameter convergence licenses a sufficiently slow diagonal selection, not an
arbitrary moving parameter.

## Audit

- warning-as-error compilation passes for the module, `Targets.lean`, `TargetChecks.lean`, and
  `AxiomsAudit.lean`;
- eight exact campaign TargetChecks pass;
- seven selected transitive axiom prints depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- placeholder, custom declaration, and resource-relaxation scans are empty;
- full `lake build` passes `8813/8813`, with only inherited warnings outside the new module.

## Classification

- `result=PCC_SLOW_WINDOW_DIAGONAL_JUSTIFIED`;
- `historical_route_coverage_delta=1`;
- `source_quantifier_bridge_delta=1`;
- `arbitrary_fast_diagonal_delta=0`;
- `pcc_delta=0`;
- `hmh_delta=0`;
- `sparse_exception_delta=0`;
- `rh_frontier_delta=0`.

## Remaining frontier

This result closes the abstract quantifier passage behind the slow choice in
Goldston--Lee--Schettler--Suriajaya Remark 1 and Section 8. The next source-facing task is to
represent the actual fixed-compact PCC remainder as the error array, prove the required
fixed-stage convergence from the source hypothesis, and compose the selected moving window
through the Fejer-kernel and Fujii calculations.

PCC itself, the relevant analytic asymptotics, HMH, density one of simple critical zeros,
elimination of the last sparse off-line exception, H11, and RH remain open.

## Public implementation receipt

Frozen implementation commit `bea2f6bbe1106a5c728408fdfdf45d5f49ebd49e` passed Lean Action
run `30520277721`, build job `90798883929`, in `2m21s`. Immutable evidence is recorded in
`research/h11_pcc_slow_window_diagonal_evidence_20260730.md`.
