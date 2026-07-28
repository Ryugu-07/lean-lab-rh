# H9 Conrey Actual Seven Flat-Interval Immutable Evidence

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01`

Classification: `FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS`

Status: `IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Frozen implementation

- commit: `e259b79773d290435b332c119ad5c81ff0ac16dc`
- public workflow: `Lean Action CI`
- run: `30400822025`
- build job: `90414919121`
- duration: `2m55s`
- conclusion: `success`

The frozen implementation contains:

- `LeanLab/Riemann/ConreySevenFlatInterval.lean`;
- one proven Target and one exact open successor;
- eight exact TargetChecks;
- eight selected transitive axiom prints;
- the aggregate import;
- the result, attempt, route, census, source, obstacle, and handoff records.

## Mechanical evidence

- Production module: 428 lines, no `sorry`.
- Warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles: pass.
- Selected transitive axioms: only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden scan for `sorry`, `admit`, `native_decide`, `unsafe`, and declared axioms: empty.
- `git diff --check`: pass.
- Local full build: `8788/8788`.
- Public frozen implementation build: pass.

## Immutability check

At creation of this evidence record:

```text
git diff e259b79773d290435b332c119ad5c81ff0ac16dc --
  LeanLab.lean
  LeanLab/Riemann/ConreySevenFlatInterval.lean
  LeanLab/Riemann/Targets.lean
  LeanLab/Riemann/TargetChecks.lean
  LeanLab/Riemann/AxiomsAudit.lean
```

is empty. This evidence commit is documentation-only with respect to all frozen proof and
registration sources.

## Claim boundary

The compiled theorem is an actual flat interval for the genuine character modulo seven. Its
scope certificate proves that seven is `7 mod 8`, outside the paper's `3 mod 8` RH-imitation
family. No permitted-family flat interval or exclusion theorem, source refutation, Conjecture 1,
Theorem 3, H9, or RH is claimed.

This evidence record requires one public Lean Action CI before the final ledger.
