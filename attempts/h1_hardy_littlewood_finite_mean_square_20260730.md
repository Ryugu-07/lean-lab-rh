# H1 Hardy--Littlewood Finite Mean-Square Attempts

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Node: `H1-HARDY-LITTLEWOOD-FINITE-MEAN-SQUARE-01`

Status: `LOCAL_AUDIT_GREEN / PUBLIC_IMPLEMENTATION_CI_PENDING`

## Fixed question

Does the finite Hardy--Littlewood mean-square step require the source's
`O(N/log N)` off-diagonal estimate, or does a universal `O(N)` estimate suffice?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `CROSS_FAMILY_SELECTION` | H2, H7/H8, H10, H11, H12, and H14 remain at broad global producers; Hardy--Littlewood Lemmas 6--8 expose a precise finite hinge between compiled source normalization and the count consumer. | Select the finite hinge without claiming H1 adjacency as sufficient reason. |
| 2 | `PRIMARY_SOURCE` | Lemma 6 bounds the distinct-pair logarithmic kernel by `O(N/log N)`; Lemmas 7--8 only consume a finite mean square of order `O(N)`. | Preregister the weaker universal linear target and exclude constant optimization. |
| 3 | `PUBLIC_PREREGISTRATION` | Docs-only commit `3f421a88fb077d3584744cb626ecbd98cb359273` passed Lean Action run `30471529594`, build job `90642717272`, in `1m31s`. | Open the production gate. |
| 4 | `DIAGONAL` | The explicit telescope `1/(n log(n)^2)<=6*(1/log n-1/log(n+1))` gives a truncation-independent diagonal bound. | Promote the probe to production and prove full summability. |
| 5 | `NEAR_DIAGONAL` | With `m=n+r`, `log(1+r/n)>=r/(n+r)`; for `r<=n`, the pair kernel is bounded by `2/(r log(n)^2)`. | Sum by the harmonic estimate `H_n<=1+log n`. |
| 6 | `FAR_DIAGONAL` | For `r>n`, `log(1+r/n)>=log 2`; a shifted finite-set injection and Cauchy--Schwarz control the coefficient product sum. | Obtain the universal linear far contribution without the source's extra `1/log N` saving. |
| 7 | `INTERVAL_INTEGRAL` | Every cross term is a cosine of frequency `log m-log n`; translation changes only phase. | Prove an endpoint-independent `2/|frequency|` bound and retain uniformity in the shift. |
| 8 | `FINITE_COMBINATORICS` | The ordered double sum is exactly the diagonal plus two upper triangles; `m=n+r` bijects each upper triangle with the compiled kernel domain. | Derive the exact finite expansion and the structural factor four. |
| 9 | `IMPLEMENTATION` | The no-sorry module compiles the diagonal, linear kernel, exact expansion, `O(L+N)`, `N<=L` corollary, and aggregate certificate under warning-as-error. | Register one proven Target, exact checks, and selected axiom prints. |
| 10 | `LOCAL_AUDIT` | Five warning-as-error compiles pass; six selected axiom prints are standard only; forbidden/resource scans and patch check are empty; full build passes `8800/8800`. | Freeze and publish the implementation, then require independent public CI. |

## Current frontier

- `closed_edge`: finite Hardy--Littlewood shifted mean square.
- `premise_minimized`: `O(N)` replaces the stronger source `O(N/log N)` for this finite step.
- `first_open_after_result`: uniform conditional-series truncation from Lemmas 3--4.
- `strict_boundary`: no infinite eta-series moment, source-X moment, count budget, unconditional
  linear count, H1, or RH.
- `global_goal`: active.
