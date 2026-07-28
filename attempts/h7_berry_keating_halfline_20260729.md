# H7 Berry--Keating Naive Half-Line Attempt

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H7-BERRY-KEATING-HALFLINE-01`

Node: `H7-BERRY-KEATING-NAIVE-HALFLINE-01`

Mode: `LITERATURE / OMISSION_AUDIT / FALSIFICATION`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

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

## Current frontier

- `compiled_predecessor`: none for the Berry--Keating subroute; existing H7 modules concern the
  distinct finite-prime Weil ground-state program.
- `fixed_edge`: standard generalized mode, formal eigenvalue identity, exact inverse-`x`
  norm-square law, and failure of half-line `L^2` membership.
- `first_open_source_theorem`: full operator-domain proof that the self-adjoint half-line
  realization has purely continuous spectrum.
- `second_open_source_theorem`: fixed compact quantum graphs have the wrong Weyl asymptotics for
  the Riemann zero spectrum.
- `omission_successor`: identify a source-valid noncompact/global arithmetic confinement
  mechanism and test whether it evades both no-go boundaries.
- `rh_frontier_delta`: `0`.
- `global_goal`: active.
- `protected_files`: inherited six files remain untouched and unstaged.

