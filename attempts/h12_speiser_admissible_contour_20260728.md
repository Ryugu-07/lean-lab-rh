# H12 Speiser Admissible-Contour Attempt

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Node: `H12-SPEISER-ADMISSIBLE-CONTOUR-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTRATION_PUBLIC_CI_PENDING`

## Fixed target

Replace Levinson--Montgomery's low-zero-table bottom sign with a fixed common zero-free
horizontal segment, construct cofinal admissible top segments, and attempt the actual indented
argument-principle proof of their Theorem 1 for the project's multiplicity-bearing counts.

Full and meaningful-partial criteria are fixed in
`research/h12_speiser_admissible_contour_prereg_20260728.md`.

## Attempt log

| phase | action | compiled result | decision |
| --- | --- | --- | --- |
| `ROUTE_SELECTION` | Compared H1 mollifiers, H2 density, H7 spectral, H10 function fields, H11 statistics, H12 Speiser, and H13 transfer after the H1 Hardy closure. | H12 has a source-exact global count theorem, four compiled local inputs, and an untested weakening of the source's numerical bottom premise. | Select H12. |
| `SOURCE_ALIGNMENT` | Rechecked Levinson--Montgomery 1974 Theorem 1 and section 2 against the project count predicates. | The source uses `t=10` plus low-zero information to obtain a signed lower boundary; the asymptotic contour comparison can instead test a fixed common zero-free bottom contribution. | Preregister the replacement; no production edit before public CI. |

## Result boundary

No new Lean theorem, count bound, Speiser equivalence, derivative-zero exclusion, or RH result is
claimed at preregistration.

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary during the parent H1 campaign; governing
  files and actual source/count definitions were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
