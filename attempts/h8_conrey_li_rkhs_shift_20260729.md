# H8 Conrey--Li RKHS-Shift Attempt

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-RKHS-SHIFT-01`

Node: `H8-CONREY-LI-RKHS-SHIFT-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `FULL_UPPER_HALF_PLANE_PRODUCER_SUCCESS /
IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_PENDING`

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
| `PREREGISTRATION_PUBLIC_CI` | Published docs-only preregistration `7b0517b0a3b2784191fa020e4bdc07249bc1455b`. | Run `30386443326`, job `90366815958`, passed in `1m45s`. | Open production editing for the fixed endpoint. |
| `KERNEL_ALGEBRA` | Defined the upper shift and source-normalized kernel, then simplified its shifted diagonal denominator. | The denominator is the positive real scalar `2*pi*(2*Im(w)+1)`; the kernel diagonal real part is a positive factor times the shifted-ratio real part. | Connect the algebra to the RKHS reproducing identity. |
| `FINITE_RKHS_POSITIVITY` | Expanded an arbitrary finite kernel-vector combination under the shift operator, tracking Mathlib's conjugate-linear first slot. | The source symmetrized quadratic is `S+conj(S)`, its imaginary part is zero, and the RKHS inner product is `conj(S)`. Operator semipositivity therefore proves the complete source finite-combination inequality. | Specialize to one kernel vector. |
| `RATIO_AND_CAYLEY` | Used nonvanishing at `w+i` to divide out the positive diagonal factor, then proved the generic right-half-plane Cayley norm bound. | `Re(W(w)/W(w+i)) >= 0` and the source Cayley transform has norm at most one throughout the original upper half-plane. | Assemble the registered certificate. |
| `DEPENDENCY_AUDIT` | Traced every used hypothesis in the compiled stage. | Analyticity of `W` is absent from the finite producer after RKHS/kernel alignment; it belongs to concrete-space construction and the second continuation stage. | Record the half-strip Hardy-RKHS edge separately. |
| `REGISTRATION` | Added one proven Target, one open successor Target, eight exact TargetChecks, and eight selected axiom prints. | Every selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. | Run local mechanical gates. |
| `LOCAL_AUDIT` | Ran warning-as-error production and registry compiles, three forbidden scans, `git diff --check`, and the full build. | Scans are empty; patch check passes; full build passes `8784/8784`. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC_CI` | Froze and pushed implementation `462c88ad1f80772e9485ce224e16e63c9fd39e8e`. | Run `30387979402`, job `90371989593`, passed in `2m2s`. | Keep proof sources frozen and publish docs-only immutable evidence. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a generated summary after H10 public closure; governing files,
  source text, existing D9 module, Mathlib RKHS APIs, and current repository state were rechecked.
- `global_goal`: active.
- `protected_files`: the six inherited protected files remain untouched and unstaged.
- `preregistration`: `7b0517b0a3b2784191fa020e4bdc07249bc1455b`, public-green on run
  `30386443326`, job `90366815958`, in `1m45s`.
- `production_module`: `LeanLab/Riemann/ConreyLiRKHSShift.lean`, 312 lines.
- `local_build`: `8784/8784`.
- `frozen_implementation`: `462c88ad1f80772e9485ce224e16e63c9fd39e8e`, public-green on
  run `30387979402`, job `90371989593`, in `2m2s`.
- `proof_freeze`: the `LeanLab/` diff from the frozen implementation is empty.

## Current boundary

Local result: `FULL_UPPER_HALF_PLANE_PRODUCER_SUCCESS`.

The fixed output proves the complete finite-combination and diagonal conclusions in the
source's original upper half-plane. It also isolates analyticity as unnecessary for this
finite producer after an RKHS with the explicit kernel is supplied.

Construction and analytic characterization of the concrete space `F(W)`, existence and
positivity of the shift operator for actual xi, the second Hardy-RKHS multiplier argument,
half-strip continuation, the unconditional Conrey--Li obstruction, H8, and RH remain open.

Result accounting:

- `historical_route_coverage_delta=1`;
- `rkhs_source_bridge_delta=1`;
- `finite_shifted_kernel_positivity_delta=1`;
- `upper_half_plane_ratio_delta=1`;
- `half_strip_extension_delta=0`;
- `actual_xi_operator_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

Frozen implementation is public-green. Docs-only immutable evidence is the next gate.
