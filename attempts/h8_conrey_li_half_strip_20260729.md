# H8 Conrey--Li Hardy-RKHS Half-Strip Attempt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`

Node: `H8-CONREY-LI-HALF-STRIP-EXTENSION-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Fixed target

Kernel-check the second stage of Conrey--Li Theorem 2 from the source half-strip Hardy kernel
through restricted-center density, contractive multiplier extension, the adjoint continuation,
and the pointwise half-strip Cayley bound.

The full target, meaningful-partial threshold, controls, and claim boundary are fixed in
`research/h8_conrey_li_half_strip_prereg_20260729.md`.

## Attempt log

| phase | action | result | decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed H12 left-half-plane winding. | Closure receipt `5861e2fcc0eacaef93db3a665cb29df7ca79d790` passed run `30404007167`, job `90425190201`, in `1m35s`. | Return to cross-family selection. |
| `CROSS_FAMILY_AUDIT` | Compared H8 half-strip continuation with H1 global moments, H2 inversion, H7 infinite operators, H10 curve geometry, H11 sparse amplification, and H12 global counting. | H8 has a bounded unformalized printed inference with the preceding stage already compiled; the alternatives currently require broader new global producers. | Select H8 half-strip continuation. |
| `PRIMARY_SOURCE_RECHECK` | Read Conrey--Li 1998 Theorem 2 from the upper Cayley bound through the second Hardy RKHS and adjoint argument. | The proof has seven exact density, well-definedness, conjugation, denominator, and continuation hinges. | Freeze all seven as mandatory checks. |
| `MATHLIB_SURVEY` | Checked generic RKHS, adjoint, and dense operator-extension APIs. | Generic kernel-center density and adjoints exist; a concrete shifted-half-plane Hardy space does not. | Permit a meaningful partial only after the abstract analytic-RKHS continuation consumer compiles. |
| `PREREGISTRATION_LOCAL` | Recorded full and partial theorem shapes, first expected infrastructure gap, and negative controls. | Docs only; no `LeanLab/` source changed. | Publish and require public CI before proof editing. |

## Current frontier

- `compiled_predecessor`: upper-half-plane shifted-kernel positivity, ratio nonnegativity, and
  Cayley contraction.
- `fixed_source_edge`: second Hardy RKHS, restricted-center density, contractive multiplier,
  adjoint continuation, and half-strip contraction.
- `first_expected_infrastructure_gap`: concrete Hardy RKHS and positive-kernel multiplier
  construction.
- `actual_xi_edge`: concrete `F(W)` and positive shift for `W=1/xi(1-i*z)`.
- `rh_frontier_delta`: `0`.
- `global_goal`: active.
- `protected_files`: inherited six files remain untouched and unstaged.
