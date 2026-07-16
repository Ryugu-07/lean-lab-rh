# RH Source-Grade Registry

Date: 2026-07-17

Status: reconstructed governance artifact. The separate Sol registry named by the V4 combined
review was not available locally; this file records the source policy implied by the available
review and current user ruling.

## Grades

| grade | source class | permitted use |
| --- | --- | --- |
| S0 | Lean kernel output, exact theorem statement witness, and `#print axioms` audit | Certify what the repository proves and which axioms it uses. |
| S1 | Original paper, authoritative monograph, official problem description, or official proof-assistant source | Define mathematical statements, route history, and documented obstacles. |
| S2 | Peer-reviewed survey or expert exposition with traceable references | Route discovery and interpretation; technical claims are checked against S1 before becoming premises. |
| S3 | Formal repository, preprint, issue, author correspondence, or community review | Candidate statements, implementation comparisons, and external feedback; trust and licensing are audited separately. |
| S4 | Search result, model synthesis, numerical experiment, blog, forum post, or unattributed summary | Leads and falsification only; never a mathematical premise. |

## Admission rules

- New criterion definitions require S1 statement alignment and S0 Lean verification.
- A theorem imported or reconstructed from another Lean repository requires license, version,
  source commit, dependency closure, proof-placeholder scan, and transitive axiom audit.
- Numerical output can reject a candidate or motivate a bound; exact claims must be re-proved at
  S0 before downstream use.
- A negative novelty search is always scope-bounded. It does not establish global priority.
- Model-original conjectures are S4 until proved; surviving conjecture CI does not upgrade them.
- Author or community feedback is preserved verbatim with provenance but does not override Lean.

## Current pinned sources

- mathlib `v4.31.0`, commit `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- `AlexKontorovich/PrimeNumberTheoremAnd`, commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`, vendored under Apache-2.0 with local provenance.
- Primary papers and exact search scope listed in
  [`exposure_novelty_audit_20260716.md`](exposure_novelty_audit_20260716.md).
