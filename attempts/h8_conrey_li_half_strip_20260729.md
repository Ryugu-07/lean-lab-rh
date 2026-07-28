# H8 Conrey--Li Hardy-RKHS Half-Strip Attempt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`

Node: `H8-CONREY-LI-HALF-STRIP-EXTENSION-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `MEANINGFUL_PARTIAL_LOCAL / PUBLIC_IMPLEMENTATION_REQUIRED`

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
| `PREREGISTRATION_PUBLIC` | Published the docs-only preregistration. | Commit `e7aa9a11f39b478e54d4c061898e27804b277b3e`; run `30404566877`, job `90427003191`, passed in `1m47s`. | Open the production gate. |
| `M0_KERNEL_ALIGNMENT` | Defined `Im z>-1/2`, the exact source Hardy kernel, and its anchor and diagonal nonvanishing identities. | All identities compile with the source's `2*pi*i*(conj(w)-z-i)` normalization. | Proceed to RKHS density. |
| `RESTRICTED_CENTER_DENSITY` | Proved that upper-half-plane kernel centers have dense span in any half-strip analytic RKHS satisfying uniqueness. | The proof uses RKHS orthogonality plus analytic identity on the connected half-strip. | Use the dense family as the multiplier domain. |
| `DENSE_OPERATOR_EXTENSION` | Defined the multiplier on arbitrary finite kernel combinations and extended it to the whole Hilbert space. | A generic no-sorry theorem proves well-definedness through quotient-by-kernel and norm-controlled extension; no linear independence is assumed. | Proceed to the adjoint. |
| `SOURCE_POSITIVE_KERNEL_BRIDGE` | Compared the preceding shifted kernel with the source Hardy defect kernel and rescaled finite coefficients. | The exact factorization and nonzero multiplier sums compile; shifted-kernel positivity now produces defect positivity directly. | Remove the independent contraction premise from the aggregate endpoint. |
| `ADJOINT_CONTINUATION` | Applied the adjoint to the anchor kernel, checked the conjugation convention, continued the multiplier identity analytically, and bounded the extension using a nonzero diagonal kernel. | The extension agrees with the actual upper Cayley transform and has norm at most one at every half-strip point. | Register the abstract consumer as proven. |
| `LOCAL_AUDIT` | Ran warning-as-error compiles, exact checks, selected axiom prints, forbidden scans, `git diff --check`, and the full build. | 740-line module; five new exact checks; eleven standard-only axiom prints; empty scans; full build `8790/8790`. | Classify as meaningful partial and publish the frozen implementation. |

## Current frontier

- `compiled_predecessor`: upper-half-plane shifted-kernel positivity, ratio nonnegativity, and
  Cayley contraction.
- `fixed_source_edge`: second Hardy RKHS, restricted-center density, contractive multiplier,
  adjoint continuation, and half-strip contraction.
- `closed_source_jump`: shifted-kernel positivity to Hardy defect positivity, dense
  multiplier construction, adjoint continuation, and half-strip Cayley contraction.
- `first_unavailable_object`: concrete Hardy RKHS on `Im z>-1/2` with its normed function
  space, completeness, evaluation continuity, exact reproducing kernel, and analytic
  uniqueness interface.
- `second_open_source_jump`: strict maximum modulus, Cayley inversion, and reconstruction of
  the paper's continuation of `W` and `W(z)/W(z+i)`.
- `actual_xi_edge`: concrete `F(W)` and positive shift for `W=1/xi(1-i*z)`.
- `rh_frontier_delta`: `0`.
- `global_goal`: active.
- `protected_files`: inherited six files remain untouched and unstaged.
