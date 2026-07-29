# H1 Hardy--Littlewood Linear Count Attempts

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01`

Node: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

## Fixed question

Can the exact Hardy--Littlewood 1921 transition from L2 exceptional-set estimates to linearly
many distinct critical-line zeros be compiled without assuming the actual Hardy `Z` moment
producers, weakening interval measure to sampled points, or double-counting overlapping windows?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION` | Hardy's qualitative theorem is publicly closed. H7 has reached explicit uniform spectral/arithmetic obstacles, while the earliest quantitative H1 count mechanism has no production module. | Compare the 1921 count bridge against Selberg global moments and Levinson--Conrey counting before selecting. |
| 2 | `PRIMARY_SOURCE` | The Goettingen facsimile, pages 296--298, shows the decisive chain: `I=integral X`, `absI=integral |X|`; two L2 bounds produce bad sets `U,V`; outside `S=U union V`, `|I|<absI`; paired length-`H` intervals then produce distinct zeros unless an entire first interval lies in `S`. | Lock equations `(2.82)`--`(2.87)` and section `2.9`, not a generic count partition. |
| 3 | `OVERLAP_AUDIT` | `SelbergLocalSignChange.lean` proves that a supplied strict local integral gap gives one actual zero and that a supplied separated finite family gives injective witnesses. It does not derive many gaps from an exceptional-set measure. | Reuse the strict-gap consumer where source-aligned; add the missing L2-to-measure and measure-to-cardinality layers. |
| 4 | `NORMALIZATION_AUDIT` | The compiled `hardyXi` coordinate is real and zero-equivalent but carries a gamma factor and is not Hardy--Littlewood's `X`/Hardy `Z` normalization. Moment estimates cannot be transferred silently. | Parameterize the count theorem by a continuous exact zero-equivalent coordinate; leave the actual source coordinate and moments as explicit successor obstacles. |
| 5 | `FALSIFICATION_DESIGN` | A finite set of all interval left endpoints has measure zero while hitting every sampled endpoint. | Compile this negative control so the source's whole-interval measure charge cannot be weakened to grid sampling. |
| 6 | `PREREGISTRATION` | The fixed endpoint includes exact Chebyshev bounds, union strict gap, adjacent-pair cardinality, injective actual zeros, a positive-fraction corollary, and the endpoint-sampling countermodel. | Publish docs only and require public CI before any `LeanLab/` edit. |
| 7 | `PUBLIC_GATE` | Preregistration commit `d36f9d0c8005691e9043165c062bf60a9e311722` passed Lean Action run `30438867401`. | Freeze the endpoint and begin production edits. |
| 8 | `MARKOV` | Mathlib's `mul_meas_ge_le_lintegral` proves both strict and non-strict square-threshold bounds directly in denominator-free `ENNReal` form. | Keep the exact threshold `(A*H/2)^2`; do not introduce division side conditions. |
| 9 | `MEASURE_TO_CARD` | A finite disjoint union of failed `Ico` first blocks has measure exactly `failed.card * H`; containment in the bad set gives the source charge. | Define good and failed `Fin n` sets by whole-block inclusion, not sampled endpoints. |
| 10 | `SOURCE_RANGE` | If `2*n*H <= T`, every first block lies in `[T,2T]`, so restriction of Lebesgue measure to the source dyadic range preserves exact block measure `H`. | Instantiate the abstract charge theorem with the literal source range. |
| 11 | `ACTUAL_ZERO_SELECTION` | A continuous coordinate with exact zero equivalence turns each good start into a zero inside its open `2H` pair block; pair-block disjointness makes the selected ordinates injective. | Retain the coordinate normalization and moment estimates as explicit producer hypotheses. |
| 12 | `NEGATIVE_CONTROL` | The finite set of all pair left endpoints has Lebesgue measure zero while containing every sampled endpoint. | Reject endpoint sampling as a replacement for whole-interval inclusion. |
| 13 | `PREMISE_MINIMIZATION` | The first compiled draft asked for the absolute-integral lower estimate at every real non-bad start, although the proof selects starts only inside the first blocks and the source proves its estimate on `[T,2T]`. | Weaken the generic consumer to first-block-local lower estimates and the source theorem to `[T,2T]`; keep the conclusion unchanged. |
| 14 | `LOCAL_AUDIT` | The 867-line module, exact checks, root import, and selected axiom prints compile with warning-as-error. Axiom output is exactly standard foundations; three forbidden scans and patch check are empty; full build passes `8798/8798`. | Publish the frozen implementation and require independent public CI before immutable evidence and closure. |
| 15 | `PUBLIC_IMPLEMENTATION` | Frozen commit `8f3742c62a381293fa201358cf58130d2c333c48` passed Lean Action run `30464674314`, build job `90619318156`, in `2m52s`. | Freeze the five proof/registration files and publish docs-only immutable evidence. |

## Current frontier

- `closed_parent`: unconditional Hardy 1914 critical-line infinitude.
- `selected_edge`: Hardy--Littlewood equations `(2.82)`--`(2.87)` and section `2.9`.
- `first_open_analytic_producers`: actual Dirichlet-eta lower estimate/error moment, actual Hardy
  `X`/`Z` second moment, and their normalization adapter.
- `compiled_consumer`: `hardyLittlewood_source_finite_count` closes the finite
  moment-to-bad-measure-to-injective-zero-count implication.
- `strict_boundary`: no unconditional linear critical-zero count, no Selberg positive
  proportion, no Levinson--Conrey proportion, no H1, and no RH.
- `protected_files`: six inherited modified/untracked files remain untouched and unstaged.
- `global_goal`: active.

## Local outcome

`classification`: `FULL_SUCCESS / FINITE_HARDY_LITTLEWOOD_COUNT_BRIDGE_FORMALIZED`.

All nine preregistered endpoint items compile. The exact remaining source frontier is no longer
the exceptional-set/count inference. It is the production, in one source-faithful normalization,
of:

1. the eta-based lower estimate for `absI`;
2. its error second moment;
3. the moving integral second moment for the actual Hardy coordinate;
4. the asymptotic parameter budget needed to instantiate the finite theorem for arbitrarily
   large `T`.

This outcome increases historical route and source-logic coverage, but it does not move the RH
frontier and does not justify optimizing the constants.

## Loop metadata

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota; serving budget not exposed.
- `compaction`: inherited summary detected; canonical governance, Goal, active ledger, source
  registry, H1 route card, hard-gap DAG, source facsimile, and relevant production modules were
  rechecked.
