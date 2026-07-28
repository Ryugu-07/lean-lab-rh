# H8 Conrey--Li Hardy-RKHS Half-Strip Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`

Node: `H8-CONREY-LI-HALF-STRIP-EXTENSION-01`

Classification: `MEANINGFUL_PARTIAL / IMPLEMENTATION_PUBLIC_GREEN`

Evidence status: `PUBLIC_CHAIN_GREEN / PARTIAL_NODE_CLOSED`

## Compiled result

The new 740-line no-sorry module
`LeanLab/Riemann/ConreyLiHalfStrip.lean` compiles the functional-analytic consumer in the
second stage of Conrey--Li 1998, Theorem 2:

```text
upper RKHS shift semipositivity
  -> shifted-kernel positivity
  -> exact Hardy defect-kernel positivity
half-strip analytic RKHS + exact Hardy kernel
  -> upper-center kernel span is dense
  -> finite defect positivity gives a global contractive multiplier
  -> the adjoint gives an analytic Cayley continuation
  -> the continuation agrees on the upper half-plane and has norm <= 1.
```

The registered proven target is
`H8.de-branges.conrey-li-half-strip-adjoint-consumer`, implemented by
`conreyLiHalfStrip_endpoint_of_rkhs_shift`.

The full target `H8.de-branges.conrey-li-half-strip-extension` remains open because the module
assumes a half-strip RKHS with the exact source kernel and analytic uniqueness rather than
constructing that concrete Hardy space.

## Source jump resolved

For upper-half-plane points `w,z`, the module proves the exact source factorization

```text
K(w,z+i) + K(w+i,z)
  = ((W(z)+W(z+i))*conj(W(w)+W(w+i))/2)
      * (1-B(z)*conj(B(w))) * L(w,z).
```

The sums `W(w)+W(w+i)` are nonzero because
`Re(W(w)/W(w+i)) >= 0` and `W(w+i) != 0`. Rescaling a finite coefficient family by
`c(w)/conj(W(w)+W(w+i))` then turns the preceding shifted-kernel quadratic form into one half
of the Hardy defect quadratic form. This compiles the paper's printed implication from the
first positive kernel to the second one; no independent defect-positivity premise survives in
the aggregate endpoint.

The module also proves a generic theorem that any norm-decreasing rule on finite combinations
of a dense vector family extends to a global continuous linear contraction. This discharges
well-definedness on linearly dependent kernel families rather than assuming it.

## Mechanical audit

- standalone warning-as-error compile: passed
- module build: `2671/2671` passed
- `Targets.lean`: warning-as-error passed
- `TargetChecks.lean`: five new exact checks passed
- `AxiomsAudit.lean`: eleven selected declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`
- three forbidden scans: empty
- `git diff --check`: passed
- full build: `8790/8790` passed
- frozen implementation:
  `c8605da897d423a7bdab4e4bd49426c482b8f7a5`
- public Lean Action: run `30406353073`, build job `90432548843`, passed in `2m9s`
- proof-source diff from the frozen implementation at evidence creation: empty
- immutable evidence:
  `a7765584e7078486c1c873a8283368061d5724e4`
- evidence Lean Action: run `30406546097`, build job `90433156392`, passed in `2m22s`
- final ledger:
  `bfd75580e589ae0e5261ff9257624bdfdcb7c0ab`
- final-ledger Lean Action: run `30406760896`, build job `90433821644`, passed in `2m19s`

## Claim boundary

This result does not construct the concrete Hardy RKHS on `Im z > -1/2`, prove its
completeness/evaluation continuity/reproducing formula, or instantiate its analytic interface.
It does not construct the source space `F(W)`, prove the required shift positivity for
`W=1/xi(1-i*z)`, or obtain an unconditional actual-xi premise.

The compiled certificate continues the Cayley transform `B`. The paper's final passage from
that continuation to a continuation of `W` and of `W(z)/W(z+i)` still needs a strict
maximum-modulus/nonvanishing argument and a source-faithful reconstruction formula. Neither is
claimed here.

Therefore H8 and RH remain open. `rh_frontier_delta=0`.

## First open successors

1. Construct the concrete half-strip Hardy RKHS and prove its exact kernel and analytic
   uniqueness interface.
2. Formalize the strict maximum-modulus/Cayley-inverse step and reconstruct the source
   continuation of `W`.
3. Construct the actual source `F(W)` and test the shift-semipositivity premise for the
   actual xi reciprocal.

Fresh route selection after public closure must compare these against the other historical
families rather than continuing H8 automatically.
