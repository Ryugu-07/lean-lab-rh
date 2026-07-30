# H11 PCC Slow-Window Diagonal

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H11-PCC-SLOW-WINDOW-DIAGONAL-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN`

## Attempt log

| step | mode | result | next action |
| --- | --- | --- | --- |
| 1 | `H10_PUBLIC_CLOSURE` | H10 rational-polar implementation and immutable evidence passed independent public CI; the actual `K(t)` node is closed. | Rerank across historical families. |
| 2 | `CROSS_FAMILY_SELECTION` | H11 has a precise source quantifier bridge immediately upstream of the PCC-to-HMH asymptotic; general H10 geometry and H12 counting remain broader stacks. | Audit PCC v4 Sections 4, 6, and 8. |
| 3 | `PRIMARY_SOURCE_AUDIT` | PCC is uniform on each fixed compact parameter interval. Remark 1 and Section 8 then require lower and upper parameters moving slowly to zero and infinity while respecting `lambda^2<=L`. | Isolate the diagonal theorem. |
| 4 | `FALSIFICATION_DESIGN` | Fixed-stage convergence does not control an arbitrary moving stage; `e(n,k)=1` when `k>n` and zero otherwise defeats `k=n+1`. | Require a slow-choice theorem and the fast-choice counterexample. |
| 5 | `PREREGISTRATION` | The exact positive, cap, reciprocal-window, negative, audit, and claim boundaries are frozen. | Publish docs-only preregistration before Lean edits. |
| 6 | `PREREG_PUBLIC_GATE` | Commit `3ab1ad271ccd4ea61b99097774d2607fb777b5df` passed Lean Action run `30519421563`, job `90796328588`, in `2m3s`. | Begin production implementation. |
| 7 | `INITIAL_THRESHOLD_DESIGN` | A recursively increasing cutoff sequence would prove the theorem but would add unnecessary bookkeeping. | Search for a selector whose own admissibility carries the error bound. |
| 8 | `GREATEST_ADMISSIBLE_SELECTOR` | At index `n`, select the greatest positive `k<=n` satisfying `k<=cap(n)` and `abs(e(n,k))<1/k`. Every fixed positive `k` eventually becomes a candidate, so the selector tends to infinity. | Compile cap, reciprocal, and error consequences. |
| 9 | `LEAN_INTERFACE_REPAIR` | The first compile exposed only explicit classical decidability and a norm-limit import issue; direct use of the fixed candidate `1` supplied the `findGreatest` specification. | Recompile without changing the mathematical construction. |
| 10 | `POSITIVE_ENDPOINT` | Lean proves divergence, eventual positivity, eventual cap preservation, moving-stage error convergence, reciprocal lower-window convergence, and real-cast upper-window divergence. | Specialize to the square cap. |
| 11 | `SOURCE_CAP_SPECIALIZATION` | With `cap(n)=Nat.sqrt(L(n))`, Lean retains `window(n)^2<=L(n)` eventually. | Compile the arbitrary-fast negative control. |
| 12 | `NEGATIVE_CONTROL` | `pccFastDiagonalError(n,k)=0` for `k<=n` and one otherwise tends to zero for every fixed `k`, while the diagonal `k=n+1` is identically one and does not tend to zero. | Register and audit. |
| 13 | `LOCAL_AUDIT` | The 173-line no-sorry module, target ledger, eight exact checks, seven selected axiom prints, three forbidden scans, and full `8813/8813` build pass. Every selected declaration uses only standard project axioms. | Publish the implementation and freeze immutable evidence. |
| 14 | `IMPLEMENTATION_PUBLIC_GATE` | Commit `bea2f6bbe1106a5c728408fdfdf45d5f49ebd49e` passed Lean Action run `30520277721`, job `90798883929`, in `2m21s`. | Freeze the five Lean blobs and publish docs-only immutable evidence. |

## Boundary

The campaign concerns only the moving-parameter quantifier passage. PCC, Fujii's theorem,
Fejer-kernel asymptotics, HMH, density-one conclusions, the last sparse exception, H11, and RH
remain open.
