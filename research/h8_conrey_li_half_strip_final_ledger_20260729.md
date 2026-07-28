# H8 Conrey--Li Hardy-RKHS Half-Strip Final Ledger

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`

Classification: `MEANINGFUL_PARTIAL`

Status: `PUBLIC_FINAL_LEDGER_PASS`

## Public chain

1. Docs-only preregistration:
   - commit `e7aa9a11f39b478e54d4c061898e27804b277b3e`;
   - Lean Action run `30404566877`;
   - build job `90427003191`;
   - `1m47s`, success.
2. Frozen implementation:
   - commit `c8605da897d423a7bdab4e4bd49426c482b8f7a5`;
   - Lean Action run `30406353073`;
   - build job `90432548843`;
   - `2m9s`, success.
3. Immutable evidence:
   - commit `a7765584e7078486c1c873a8283368061d5724e4`;
   - Lean Action run `30406546097`;
   - build job `90433156392`;
   - `2m22s`, success.

The proof-source diff from the frozen implementation through immutable evidence is empty.

## Compiled endpoint

Lean proves:

- the exact source half-strip and Hardy-kernel denominator identities;
- the pointwise shifted-kernel/Hardy-defect factorization;
- nonvanishing of the diagonal coefficient multipliers from upper ratio positivity;
- finite defect positivity from the preceding RKHS shift producer;
- density of upper kernel centers under half-strip analytic uniqueness;
- well-defined extension of a norm-decreasing finite-combination rule to a global
  contraction, without assuming kernel-vector linear independence;
- the exact conjugated adjoint multiplier convention;
- analytic continuation of the Cayley transform and norm at most one throughout the
  half-strip;
- aggregate partial Target
  `H8.de-branges.conrey-li-half-strip-adjoint-consumer`.

## Audit receipt

- 740-line no-sorry production module;
- one new proven partial Target and one retained open full Target;
- five new exact TargetChecks;
- eleven selected axiom prints with only `propext`, `Classical.choice`, and `Quot.sound`;
- three empty forbidden scans;
- warning-as-error production and registry compiles;
- local full build `8790/8790`;
- public implementation and immutable-evidence CI green.

## Claim boundary

The endpoint assumes a scalar RKHS on `Im z>-1/2` with the exact source Hardy kernel and
analytic uniqueness. It does not construct this concrete Hardy space. It also does not finish
the strict maximum-modulus/Cayley-inverse passage to a continuation of `W`, construct the
source space `F(W)`, or prove the actual-xi shift-semipositivity premise.

H8 and RH remain open.
`historical_route_coverage_delta=1`, `source_positive_kernel_bridge_delta=1`, and
`rh_frontier_delta=0`.

## Successor rule

Close only the abstract consumer node
`H8.de-branges.conrey-li-half-strip-adjoint-consumer`. Retain the full target
`H8.de-branges.conrey-li-half-strip-extension`, the concrete half-strip Hardy RKHS, the
Cayley-to-`W` continuation, and the actual `F(W)`/xi shift premise as open candidates.

Return the persistent RH Goal to fresh cross-family historical omission selection after
final-ledger CI. Conjecture generation and direct RH proof attempts remain open.

## Public final-ledger receipt

Final ledger commit `bfd75580e589ae0e5261ff9257624bdfdcb7c0ab` passed Lean Action run
`30406760896`, build job `90433821644`, in `2m19s`. The proof-source diff from frozen
implementation through final ledger is empty. The local partial node is ready for a docs-only
closure receipt.
