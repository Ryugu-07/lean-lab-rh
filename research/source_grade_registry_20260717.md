# RH Source-Grade Registry

Date: 2026-07-17

Status: canonical synthesis. The original Sol literature registry is now imported as
[`literature_source_registry.csv`](literature_source_registry.csv). Its `S0-S4` literature grades
are authoritative; Lean kernel evidence uses the separate `K0` label below.

## Grades

| grade | source class | permitted use |
| --- | --- | --- |
| S0 | Canonical primary source, established theorem, or authoritative problem description with durable independent use | Anchor a route card and a known-theorem formalization after statement alignment. |
| S1 | Peer-reviewed or independently developed specialist work in an established route, with precise assumptions and conclusions | Motivate a literature campaign after statement alignment. |
| S2 | Specialist preprint or recent result with a precise checkable mechanism but incomplete independent uptake | Motivate proof or falsification reconnaissance; cannot certify novelty or progress alone. |
| S3 | Isolated, unreviewed, or self-declared proof claim, unclear provenance, or an unchecked decisive step | Low-confidence candidate input; never a premise without Lean verification. |
| S4 | Withdrawn, contradicted, or formally falsified mechanism | Negative evidence and regression tests. |

## Mechanical grade

`K0` means the exact Lean declaration compiles, has an exact TargetChecks witness where required,
and its transitive `#print axioms` output uses only the accepted Lean/mathlib trust base. `K0` says
what the formal source proves; it does not by itself establish source alignment or novelty.

## Admission rules

- New criterion definitions require S0/S1 statement alignment and K0 Lean verification.
- A theorem imported or reconstructed from another Lean repository requires license, version,
  source commit, dependency closure, proof-placeholder scan, and transitive axiom audit.
- Numerical output can reject a candidate or motivate a bound; exact claims must be re-proved at
  K0 before downstream use.
- A negative novelty search is always scope-bounded. It does not establish global priority.
- Model-original conjectures have no literature grade; they remain `UNVERIFIED` until K0, and
  surviving conjecture CI does not upgrade them.
- Author or community feedback is preserved verbatim with provenance but does not override Lean.

## Current pinned sources

- mathlib `v4.31.0`, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `AlexKontorovich/PrimeNumberTheoremAnd`, commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, vendored under Apache-2.0 with local provenance.
- Primary papers and exact search scope listed in
  [`exposure_novelty_audit_20260716.md`](exposure_novelty_audit_20260716.md).
