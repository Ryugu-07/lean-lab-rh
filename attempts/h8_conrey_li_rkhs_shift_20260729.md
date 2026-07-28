# H8 Conrey--Li RKHS-Shift Attempt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-RKHS-SHIFT-01`

Node: `H8-CONREY-LI-RKHS-SHIFT-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Fixed target

Kernel-check the first stage of Conrey--Li Theorem 2: derive symmetrized shifted-kernel
positivity, upper-half-plane shifted-ratio nonnegativity, and the Cayley contraction from a
source-aligned scalar RKHS and a positive kernel-shift operator.

The complete criteria and claim boundary are fixed in
`research/h8_conrey_li_rkhs_shift_prereg_20260729.md`.

## Attempt log

| phase | action | result | decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed H10 Weil surface/Hodge lattice at its registered full numerical endpoint. | Final ledger `bb3cb3ee20339e71930ac4fc7b667bf161364648` passed run `30385243402`, job `90362773315`, in `2m22s`. | Return to cross-family selection. |
| `CROSS_FAMILY_AUDIT` | Compared H1 mollifiers, H2/H11 sparse-exception detection, H7 infinite spectral objects, H8 de Branges geometry, H10 transfer, and H12 global contours. | Conrey--Li's RKHS producer is an exact historical edge left open by the existing phase-obstruction campaign, and Mathlib now supplies a real RKHS API. | Select H8 RKHS production rather than another numerical optimization. |
| `SOURCE_ALIGNMENT` | Read Conrey--Li Theorem 2 from the explicit kernel through the second Hardy-RKHS extension argument. | The upper-half-plane producer and the half-strip continuation are separate stages. The source operator assumption is semipositive, not strictly positive. | Fix stage 1 and preserve stage 2 as an exact open edge. |
| `REENTRY_DIFFERENCE` | Compared the proposed endpoint with `ConreyLiPhaseObstruction.lean`. | The old module consumes ratio nonnegativity and conditionally refutes it; it does not derive the ratio from RKHS data. | Re-entry is materially distinct. |
| `API_SURVEY` | Checked `RKHS.kerFun`, `RKHS.kernel`, reproducing identities, kernel density, positive-semidefinite kernels, and `UpperHalfPlane`. | The source's scalar kernel and the shift map have a direct no-sorry Lean surface. Inner-product orientation and finite-sum expansion require explicit proofs. | Publish docs-only preregistration before proof editing. |
| `NEGATIVE_CONTROL_DESIGN` | Audited zero vectors, totalized division, shift orientation, denominator sign, and half-strip promotion. | The zero-vector issue disappears under the source's actual `>= 0` premise; nonvanishing and the second RKHS remain genuine boundaries. | Register controls without claiming a source defect. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary after H10 public closure; governing files,
  source text, existing D9 module, Mathlib RKHS APIs, and current repository state were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.

## Current boundary

This is a preregistered proof attempt, not a result. No new production theorem exists yet.

The fixed output concerns only the source's upper-half-plane RKHS producer. Construction and
analytic characterization of the concrete space `F(W)`, existence and positivity of the shift
operator for actual xi, the second Hardy-RKHS multiplier argument, half-strip continuation,
the unconditional Conrey--Li obstruction, H8, and RH remain open.
