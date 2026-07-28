# H12 Levinson--Montgomery Left-Half-Plane Winding Immutable Evidence

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H12-LEFT-HALF-PLANE-WINDING-01`

Classification: `FULL_SUCCESS`

Status: `PUBLIC_EVIDENCE_PASS / FINAL_LEDGER_PASS`

## Frozen implementation

- commit: `0a1248f2a02fec9d3cf0e774bc6eb4fe8959e0ec`
- public workflow: `Lean Action CI`
- run: `30403264392`
- build job: `90422806378`
- duration: `3m4s`
- conclusion: `success`

The frozen implementation contains:

- `LeanLab/Riemann/LevinsonMontgomeryLeftHalfPlaneWinding.lean`;
- the generic strict-left principal-log and closed-path theorems;
- the actual `zeta'/zeta` complex derivative, horizontal derivative, and endpoint theorem;
- one proven Target;
- seven exact TargetChecks;
- seven selected transitive axiom prints;
- the aggregate import and local result records.

## Mechanical evidence

- Production module: 223 lines, no `sorry`.
- Warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles: pass.
- Selected transitive axioms: only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden scans for `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`, declared
  `axiom/constant`, and relaxed resource/trace options: empty.
- `git diff --check`: pass.
- Local full build: `8789/8789`.
- Public frozen implementation build: pass.

## Immutability check

At creation of this evidence record:

```text
git diff 0a1248f2a02fec9d3cf0e774bc6eb4fe8959e0ec --
  LeanLab.lean
  LeanLab/Riemann/LevinsonMontgomeryLeftHalfPlaneWinding.lean
  LeanLab/Riemann/Targets.lean
  LeanLab/Riemann/TargetChecks.lean
  LeanLab/Riemann/AxiomsAudit.lean
```

is empty. This evidence commit is documentation-only with respect to all frozen proof and
registration sources.

## Claim boundary

The compiled result closes the source inference from strict left-half-plane containment to
zero closed-path logarithmic winding and instantiates the horizontal endpoint formula on the
actual ratio under `SpeiserStrictNegativeHorizontal`.

It does not prove existence of such a height, the global indented argument principle, Jensen
top variation, either Levinson--Montgomery count theorem, Speiser equivalence, H12, or RH.

This immutable evidence commit
`016f0b50f552ee42126ecf5bf3e93be8edd15e3a` passed Lean Action run `30403576041`,
build job `90423807382`, in `2m11s`. The proof-source diff from the frozen implementation
through this commit is empty. One docs-only final ledger and closure receipt remain.

Final ledger `b3fdeb26b8aa077c0d0db68c379b4433a3feeba6` passed Lean Action run
`30403814535`, build job `90424563153`, in `1m35s`. Only the closure receipt remains.
