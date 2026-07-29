# H1 Hardy--Littlewood Eta-to-Theta Abel Transfer Attempts

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Node: `H1-HARDY-LITTLEWOOD-ETA-ABEL-TRANSFER-01`

Status: `FULL_SUCCESS / FINAL_LEDGER_PUBLIC_GREEN / CLOSURE_RECEIPT_CI_PENDING`

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
| 5 | `PUBLIC_PREREGISTRATION` | Docs-only commit `e770d76f85ab9d363b50c606fc195a2401b93390` passed Lean Action run `30477686788`, build job `90663405809`, in `1m33s`. | Open the production gate. |
| 6 | `FINITE_ABEL` | Mathlib's range summation-by-parts theorem matches a shifted block after making the endpoint convention explicit. | Compile both the raw and decreasing-weight forms before using analytic hypotheses. |
| 7 | `ETA_BLOCK` | A block after `N` is the difference of the eta remainders at `N` and `N+K`; negative exponent monotonicity gives `2*Ceta*N^(-sigma)`. | Localize every oscillatory input in the stated eta remainder hypothesis. |
| 8 | `THETA_BLOCK` | Reciprocal-log differences are nonnegative and telescope exactly. | Derive the finite weighted-block bound with explicit universal factor `2/log 2`. |
| 9 | `CAUCHY_LIMIT` | The finite block bound tends to zero for every `sigma>0`, and `Complex` is complete. | Construct the ordered Theta value and pass the closed norm bound to the limit. |
| 10 | `UNIFORMITY` | The proof uses no property of a parameter beyond the common eta remainder constant. | Compile an arbitrary-family theorem preserving one uniform constant. |
| 11 | `REGISTRATION` | One proven Target, five exact TargetChecks, six selected axiom prints, and the root import compile under warning-as-error. | Run the complete mechanical audit and full build. |
| 12 | `LOCAL_AUDIT` | The 488-line module has empty forbidden/resource scans and patch check; selected axioms are standard only; full build passes `8801/8801`. | Freeze and publish the implementation, then require independent public CI. |
| 13 | `IMPLEMENTATION_PUBLIC_CI` | Frozen commit `f03c6a8f5d35945d34407d0627b7a5f4f629cb9e` passed Lean Action run `30479693865`, build job `90670228283`, in `2m17s`; the frozen five-file diff is empty. | Publish docs-only immutable evidence and require a second public CI. |
| 14 | `IMMUTABLE_EVIDENCE_PUBLIC_CI` | Docs-only evidence commit `6b151d4cbecd963ea4be9d208c9dff3d20ac47ac` passed Lean Action run `30480041592`, build job `90671423054`, in `2m22s`; the frozen five-file diff remains empty. | Publish the final ledger and require public CI before a closure receipt. |
| 15 | `FINAL_LEDGER_PUBLIC_CI` | Docs-only final-ledger commit `0341cb75df491de2642cdaeb02ef5b8e3041b140` passed Lean Action run `30480335673`, build job `90672503333`, in `2m8s`; the frozen five-file diff remains empty. | Publish one closure receipt and require public CI, then stop only this campaign. |

## Current frontier

- `closed_edge_public`: uniform eta remainder `->` ordered Theta convergence and remainder.
- `exact_input`: a single `K*N^(-sigma)` eta remainder for every `N` after the source cutoff.
- `compiled_output`: `(2/log 2)*K*N^(-sigma)` Theta remainder, uniform over arbitrary
  parameter families.
- `first_open_after_result`: prove the actual Lemma 3 eta remainder without an extra
  `1+abs(s)` loss.
- `strict_boundary`: no primitive identification, infinite mean square, source-X moment,
  parameter budget, unconditional linear count, H1, or RH.
- `global_goal`: active.
