# Route Selection after H10 Weil Surface/Hodge

Date: 2026-07-29

Status: `RERANK_COMPLETE / H8_CONREY_LI_RKHS_SHIFT_SELECTED`

## Closed parent

Campaign `LITERATURE-20260728-H10-WEIL-HODGE-LATTICE-01` is publicly closed at
`FULL_SOURCE_NUMERICAL_HINGE_SUCCESS`. Its final-ledger commit
`bb3cb3ee20339e71930ac4fc7b667bf161364648` passed Lean Action run `30385243402`, build job
`90362773315`, in `2m22s`.

The campaign closes the integer-lattice-to-real semipositivity, exact Hasse--Weil numerical
bound, and finite spectral-composition edges. Actual curve intersections, Hodge index,
Frobenius point-count identities, number-field transfer, H10, and RH remain open. Fresh
cross-family selection is required.

## Cross-family comparison

| family | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H8 de Branges/entire-function geometry | Reconstruct the RKHS producer in Conrey--Li Theorem 2 from kernel shift and operator positivity to shifted-ratio positivity. | The closed phase-obstruction campaign consumes and refutes ratio positivity under explicit phase data. It does not compile the theorem that produces this ratio condition from the proposed Hilbert-space positivity. Mathlib now has a scalar/vector RKHS API. | **Select.** |
| H1 Levinson--Conrey | Construct the actual long mollified mean value and proportion-count consumer. | High value, but the decisive twisted/off-diagonal mean value remains an open global input. Another finite variational constant is not selected. | Retain open. |
| H2/H11 density and statistics | Build an actual exceptional-zero amplifier that detects a finite or sparse off-line orbit. | Existing density-scale and pair-statistical errors can absorb sparse exceptions. No source-backed amplifier is presently available. | Retain open. |
| H7 Hilbert--Polya/trace | Construct an infinite arithmetic operator with a proved trace identity and controlled tails. | Finite certificates and several obstructions compile, but the infinite object is still the first missing producer. | Retain open. |
| H10 function fields | Formalize actual curve intersection theory or build a number-field transfer. | The numerical consumer has just closed. Immediate continuation would be route inertia and needs unavailable geometric infrastructure. | Retain open. |
| H12 Speiser | Complete the global indented argument-principle count and strict base orientation. | The local boundary and admissible-height pieces compile; the remaining edge is a global contour package. | Retain open. |

## Materially new re-entry

The older campaign `LITERATURE-20260726-D9-CONREY-LI-PHASE-OBSTRUCTION-01` proved the conditional
logic

```text
dense logarithmic phase data
  -> a point where Re(W(z)/W(z+i)) < 0
  -> failure of the proposed shifted-ratio nonnegativity.
```

It explicitly left the RKHS theorem as an input boundary. The selected campaign attacks the
opposite, theorem-producing direction:

```text
actual scalar RKHS + T(kernel at w) = kernel at w+i
  + Re <F,T F> >= 0
  -> positive-definite symmetrized shifted kernel
  -> Re(W(z)/W(z+i)) >= 0 in the upper half-plane
  -> Cayley transform bounded by one there.
```

This is not a repetition of the phase obstruction. It connects that obstruction to the
historical Hilbert-space premise and audits the exact source dependency.

## Source lock and correction

The fixed primary source is J. Brian Conrey and Xian-Jin Li,
*A note on some positivity conditions related to zeta- and L-functions* (1998), Theorem 2 and
its proof:

`https://arxiv.org/abs/math/9812166`

The source kernel is

```text
K(w,z) = W(z) * conj(W(w)) / (2*pi*i*(conj(w)-z)).
```

The source assumption is the non-strict inequality

```text
Re <F,T F> >= 0
```

for every `F`. It is compatible with `F=0`. An earlier working note misread this as strict
positivity; no zero-vector defect is claimed.

The source proof has two distinct stages:

1. the original RKHS and shift operator produce upper-half-plane ratio positivity and a Cayley
   contraction;
2. a second Hardy RKHS on `Im z > -1/2`, a contractive multiplier, its adjoint, and analytic
   continuation extend the result to the larger half-plane.

The selected campaign fixes stage 1 as its full endpoint and preserves stage 2 as an exact
open theorem-shaped edge.

## Omission probe

The campaign asks whether every orientation, conjugation, denominator sign, and nonvanishing
hypothesis in stage 1 is sufficient exactly as written when translated to Mathlib's inner
product convention. A successful formalization may reveal a missing premise or normalization
even if the paper-level argument is correct.

The current expectation is that the stage-1 implication is valid. A failure to derive it under
the source-aligned hypotheses is a falsification result and must identify the first invalid
algebraic or functional-analytic edge rather than silently strengthening the premise.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H8-CONREY-LI-RKHS-SHIFT-01`.
- `node`: `H8-CONREY-LI-RKHS-SHIFT-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: scalar RKHS kernel alignment and shift positivity imply finite-combination
  positivity of the symmetrized shifted kernel, upper-half-plane nonnegativity of
  `Re(W(z)/W(z+i))`, and contraction of the source Cayley transform.
- `meaningful_partial`: the single-kernel ratio theorem and Cayley contraction compile, while
  the first missing finite-combination or half-strip step is stated exactly.
- `negative_controls`: inner-product convention, shift direction, denominator positivity,
  nonvanishing of `W`, non-strict versus strict conclusions, and no promotion from the original
  upper half-plane to `Im z > -1/2` without the second RKHS argument.
- `strict_boundary`: no construction of the concrete space `F(W)`, no proof that the shift
  operator exists or is positive for `W=1/xi(1-i*z)`, no source value-distribution theorem, no
  half-strip analytic continuation, no H8 result, and no RH result.
- `production_gate`: no `LeanLab/` edit before docs-only preregistration passes public CI.

The persistent RH Goal remains active.
