# H7 Berry--Keating Naive Half-Line Attempt

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H7-BERRY-KEATING-HALFLINE-01`

Node: `H7-BERRY-KEATING-NAIVE-HALFLINE-01`

Mode: `LITERATURE / OMISSION_AUDIT / FALSIFICATION`

Status: `PUBLICLY_CLOSED_FULL_SUCCESS`

## Fixed target

Kernel-check the standard Berry--Keating half-line generalized eigenmode: prove its formal
eigenvalue equation and prove that the same mode is not an element of
`L^2((0,+infinity), dx)`.

The exact endpoint, controls, and claim boundary are fixed in
`research/h7_berry_keating_halfline_prereg_20260729.md`.

## Attempt log

| phase | action | result | decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed H8 Conrey--Li half-strip consumer. | Closure receipt `67a12f4d80e0d5246f7d1a2173f6972346a1c78d` passed run `30406973119`, job `90434479242`, in `1m34s`. | Return to fresh cross-family selection. |
| `COVERAGE_RECHECK` | Compared H7, H10, H11, and H13 open nodes and re-read the historical census. | Every named family has at least one campaign, but H7 coverage is concentrated on finite-prime Weil ground states; Berry--Keating has no route card or Lean endpoint. | Treat subroute breadth, not family label, as the coverage unit. |
| `PRIMARY_SOURCE_AUDIT` | Read Endres--Steiner's half-line and compact-graph analysis and Connes--Consani's scaling-Hamiltonian comparison. | The naive half-line mode is explicit and non-`L^2`; compact fixed graphs have a separate Weyl-growth obstruction. | Freeze the half-line mode as the first exact node; retain the compact-graph theorem as a successor. |
| `MATHLIB_SURVEY` | Checked complex powers, derivatives, improper-integral criteria, and `MemLp` square-norm APIs. | Mathlib contains the exact ingredients for a restricted-measure `L^2` proof; no custom spectral axiom is needed. | Preregister a real no-sorry theorem, not a prose-only audit. |
| `PREREGISTRATION_LOCAL` | Fixed the formal operator, eigenmode, norm-square law, restricted `MemLp` obstruction, controls, and successor question. | Docs only; no `LeanLab/` source changed. | Publish and require public CI before proof editing. |
| `PREREGISTRATION_PUBLIC` | Published the docs-only preregistration. | Commit `5ec1e2b9b5e8028517934b986f407f2a210748e6`; run `30407563102`, job `90436305353`, passed in `1m40s`. | Open the production gate. |
| `DERIVATIVE_API` | First stated the complex-power derivative through `HasDerivAt`. | Lean selected two definitionally different real-module instances on `Complex`, so the source theorem did not elaborate against the wrapped definition. | Retain the exact mathematical derivative as a `deriv` equality, which is the statement consumed by `H_BK`. |
| `FORMAL_EIGENVALUE` | Expanded the complex power derivative inside `-i(x*d/dx+1/2)`. | Field normalization closed `x*x^-1`; a separate explicit `i^2=-1` rewrite closed the energy term. | Record the exact pointwise eigenvalue equation for every `x>0`. |
| `NORM_SQUARE` | Reduced the norm of `x^(-1/2+iE)` to a real power. | The imaginary energy disappears and the square is exactly `x^-1`. | Use the energy-independent density for the `L^2` obstruction. |
| `RESTRICTED_MEMLP` | Assumed membership in `MemLp 2` for Lebesgue measure restricted to `(0,+infinity)`. | The square-norm API makes `x^-1` integrable on that set, contradicting the improper-integral theorem. | Close the standard-mode obstruction without replacing it by `L^1` or a truncated interval. |
| `LOCAL_AUDIT` | Registered one proven Target, five exact TargetChecks, five selected axiom prints, forbidden scans, warning-as-error module compile, and full build. | 93-line no-sorry module; selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`; full build `8791/8791`. | Classify `FULL_SUCCESS / LOCAL_AUDIT_GREEN` and publish the frozen implementation. |
| `IMPLEMENTATION_PUBLIC` | Published the frozen proof and registration sources. | Commit `56ec4c84d894899afb132b50aece303cb40f7cd7`; run `30408034816`, job `90437803648`, passed in `2m11s`. | Freeze five proof/registration files and publish docs-only immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC` | Published the frozen-file receipt and exact claim boundary without changing proof sources. | Commit `d3cb2713740581d40027748f345389899bc8c2a5`; run `30408221987`, job `90438382124`, passed in `1m56s`. | Publish one docs-only final ledger and require its own public CI. |
| `FINAL_LEDGER_PUBLIC` | Published the exact closed node, open spectral successors, and zero hard-gap/RH-frontier deltas. | Commit `403510b919884e23226c3b051ae8e1f0d7cfd1c4`; run `30408401817`, job `90438937042`, passed in `1m46s`. | Publish the closure receipt and stop this campaign. |

## Current frontier

- `compiled_predecessor`: none for the Berry--Keating subroute; existing H7 modules concern the
  distinct finite-prime Weil ground-state program.
- `closed_edge`: standard generalized mode, formal eigenvalue identity, exact inverse-`x`
  norm-square law, and failure of half-line `L^2` membership.
- `proven_target`: `H7.berry-keating.naive-halfline-mode-obstruction`.
- `first_open_source_theorem`: full operator-domain proof that the self-adjoint half-line
  realization has purely continuous spectrum.
- `second_open_source_theorem`: fixed compact quantum graphs have the wrong Weyl asymptotics for
  the Riemann zero spectrum.
- `omission_successor`: identify a source-valid noncompact/global arithmetic confinement
  mechanism and test whether it evades both no-go boundaries.
- `rh_frontier_delta`: `0`.
- `global_goal`: active.
- `protected_files`: inherited six files remain untouched and unstaged.
- `local_stop`: close only the standard half-line mode obstruction after final-ledger and
  closure-receipt CI; return to fresh cross-family historical selection.
