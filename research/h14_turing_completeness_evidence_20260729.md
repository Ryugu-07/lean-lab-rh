# H14 Turing Completeness Consumer Immutable Evidence

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H14-TURING-COMPLETENESS-CONSUMER-01`

Classification: `FULL_TURING_COMPLETENESS_CONSUMER_SUCCESS`

Status: `PUBLIC_EVIDENCE_PASS / FINAL_LEDGER_PASS`

## Frozen implementation

- commit: `258a9ac8ce69f6dffe6beb4a6a7579845ca2a457`
- public workflow: `Lean Action CI`
- run: `30397348488`
- build job: `90403505298`
- duration: `2m6s`
- conclusion: `success`

The frozen implementation contains:

- `LeanLab/Riemann/TuringCompletenessConsumer.lean`;
- the proven and open successor Targets;
- eight exact TargetChecks;
- seven selected transitive axiom prints;
- the aggregate import;
- the result, attempt, route, census, obstacle, and handoff records.

## Mechanical evidence

- Production module: 281 lines, no `sorry`.
- Warning-as-error production, Targets, and TargetChecks compiles: pass.
- Selected transitive axioms: only `propext`, `Classical.choice`, and `Quot.sound`.
- Three forbidden scans: empty.
- `git diff --check`: pass.
- Local full build: `8787/8787`.
- Public frozen implementation build: pass.

## Immutability check

At creation of this evidence record:

```text
git diff 258a9ac8ce69f6dffe6beb4a6a7579845ca2a457 --
  LeanLab.lean
  LeanLab/Riemann/TuringCompletenessConsumer.lean
  LeanLab/Riemann/Targets.lean
  LeanLab/Riemann/TargetChecks.lean
  LeanLab/Riemann/AxiomsAudit.lean
```

is empty. This evidence commit is documentation-only with respect to all frozen proof and
registration sources.

## Claim boundary

The compiled theorem is the finite Turing-style completeness consumer. Concrete root isolation,
boundary nonvanishing, numerical counting, every certified height, the global tail reduction,
H14-to-RH promotion, and RH remain open.

This immutable evidence commit
`c0b16dce7d8f70a4cc704276713ad824bd37ff3b` passed Lean Action run
`30397611979`, build job `90404368803`, in `1m57s`. The proof-source diff from the frozen
implementation through this commit is empty.
