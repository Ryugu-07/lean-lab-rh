# H1 Hardy--Littlewood Eta-to-Theta Abel Transfer Attempts

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Status: `PREREGISTRATION_PUBLIC_CI_PENDING`

## Fixed question

Is Hardy--Littlewood Lemma 4 a lossless discrete Abel consequence of Lemma 3, and can Lean
localize the remaining analytic difficulty entirely in Lemma 3's uniform eta remainder?

## Attempt ledger

| round | mode | observation | decision |
| --- | --- | --- | --- |
| 1 | `CROSS_FAMILY_SELECTION` | H2, H7/H8, H10, H11, H12, and H14 remain at broad global producers; Lemma 4 is a precise source inference between an open eta remainder and the compiled finite Theta mean square. | Select only the eta-to-Theta transfer; retain the actual eta remainder as an explicit input. |
| 2 | `PRIMARY_SOURCE` | Pages 286--287 state the same `O(x^(-sigma))` order for eta and Theta under `sigma>=sigma0>0`, `abs(t)<A*x`. The proof uses reciprocal-log differences times eta block sums. | Lock the source indexing and uniformity; reject a crude termwise derivative proof carrying an extra `abs(s)` loss. |
| 3 | `LEAN_SURVEY` | Mathlib has `Finset.sum_Ico_by_parts`; the project has ordered Dirichlet partial sums and the finite Hardy--Littlewood logarithmic coefficients. No theorem currently identifies the source eta remainder or Theta ordered value. | Reuse the finite Abel primitive and keep both identifications outside the endpoint. |
| 4 | `PREREGISTRATION` | Route selection, exact endpoint, negative controls, and obstruction map are written before any `LeanLab/` edit. | Publish the docs-only commit and require public CI before implementation. |

## Current frontier

- `selected_edge`: uniform eta remainder `->` ordered Theta convergence and remainder.
- `exact_input`: a single `K*N^(-sigma)` eta remainder for every `N` after the source cutoff.
- `expected_output`: a universal-constant `K*N^(-sigma)` Theta remainder.
- `first_open_after_result`: prove the actual Lemma 3 eta remainder without an extra
  `1+abs(s)` loss.
- `strict_boundary`: no primitive identification, infinite mean square, source-X moment,
  parameter budget, unconditional linear count, H1, or RH.
- `global_goal`: active.
