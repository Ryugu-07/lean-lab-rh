# H8 Conrey--Li Hardy-RKHS Half-Strip Immutable Evidence

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-HALF-STRIP-01`

Classification: `MEANINGFUL_PARTIAL`

Status: `PUBLIC_EVIDENCE_PASS / FINAL_LEDGER_PASS`

## Frozen implementation

- commit: `c8605da897d423a7bdab4e4bd49426c482b8f7a5`
- public workflow: `Lean Action CI`
- run: `30406353073`
- build job: `90432548843`
- duration: `2m9s`
- conclusion: `success`

The frozen implementation contains:

- the 740-line no-sorry `ConreyLiHalfStrip.lean` module;
- exact half-strip and source Hardy-kernel algebra;
- the shifted-kernel to defect-kernel positivity transfer;
- restricted upper-center density under analytic uniqueness;
- the quotient and dense-extension construction of the global contraction;
- the adjoint analytic continuation and pointwise norm bound;
- one new proven partial Target, five new exact checks, and eleven selected axiom prints.

## Mechanical evidence

- Warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles: pass.
- Selected transitive axioms: only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden scans for `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`, declared
  `axiom/constant`, and relaxed resource/trace options: empty.
- `git diff --check`: pass.
- Local full build: `8790/8790`.
- Public frozen implementation build: pass.

## Immutability check

At creation of this evidence record:

```text
git diff c8605da897d423a7bdab4e4bd49426c482b8f7a5 --
  LeanLab.lean
  LeanLab/Riemann/ConreyLiHalfStrip.lean
  LeanLab/Riemann/Targets.lean
  LeanLab/Riemann/TargetChecks.lean
  LeanLab/Riemann/AxiomsAudit.lean
```

is empty. This evidence commit is documentation-only with respect to all frozen proof and
registration sources.

## Claim boundary

The compiled result closes the abstract functional-analytic consumer and the positive-kernel
transfer printed in Conrey--Li Theorem 2. It assumes rather than constructs the concrete
half-strip Hardy RKHS. It also does not formalize the final Cayley-to-`W` continuation, the
actual `F(W)` space, or the actual-xi shift-semipositivity premise.

H8 and RH remain open. `rh_frontier_delta=0`.

Immutable evidence commit `a7765584e7078486c1c873a8283368061d5724e4` passed Lean Action run
`30406546097`, build job `90433156392`, in `2m22s`. The proof-source diff from the frozen
implementation through this commit is empty.

Final ledger `bfd75580e589ae0e5261ff9257624bdfdcb7c0ab` passed Lean Action run
`30406760896`, build job `90433821644`, in `2m19s`.
