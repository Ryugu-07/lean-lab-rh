# H1 Hardy--Littlewood Linear Count Attempts

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H1-HARDY-LITTLEWOOD-LINEAR-COUNT-01`

Node: `H1-HARDY-LITTLEWOOD-EXCEPTIONAL-SET-COUNT-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

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

## Current frontier

- `closed_parent`: unconditional Hardy 1914 critical-line infinitude.
- `selected_edge`: Hardy--Littlewood equations `(2.82)`--`(2.87)` and section `2.9`.
- `first_open_analytic_producers`: actual Dirichlet-eta lower estimate/error moment, actual Hardy
  `X`/`Z` second moment, and their normalization adapter.
- `strict_boundary`: no unconditional linear critical-zero count, no Selberg positive
  proportion, no Levinson--Conrey proportion, no H1, and no RH.
- `protected_files`: six inherited modified/untracked files remain untouched and unstaged.
- `global_goal`: active.

## Loop metadata

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota; serving budget not exposed.
- `compaction`: inherited summary detected; canonical governance, Goal, active ledger, source
  registry, H1 route card, hard-gap DAG, source facsimile, and relevant production modules were
  rechecked.
