# H6 General Strip-Contraction Campaign

Campaign: `CAMPAIGN-20260717-H6-GENERAL-STRIP-CONTRACTION-01`

Date: 2026-07-17

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes; route selection resumed from the preserved summary,
  canonical governance, HANDOFF, Targets, attempts, hard-gap DAG, and route portfolio

## Normalized Tuple

- `statement`: arbitrary-base de Bruijn squared-strip contraction and the exact
  `t+y^2/2` all-real endpoint
- `assumptions`: the compiled source-normalized heat family and standard Mathlib analysis only
- `strategy`: parameterize the existing conjugate-factor vertical-average proof, finite cosh
  iteration, compact-uniform heat limit, and Jensen zero persistence
- `unresolved_frontier`: expose the generic internal strip theorem and verify that the arbitrary
  base-time compact limit has all required bounds without adding `0<=t`

## Loop Ledger

| Loop | Mode | Result | Decision |
| --- | --- | --- | --- |
| 1 | `ROUTE_SELECTION -> LITERATURE` | Primary-source review corrected the audited unconditional frontier from `Lambda<=0.22` to Platt--Trudgian's `Lambda<=0.2`. W2 and M2 had no new mechanism; strict improvement below `0.2` lacked fixed certificates. The generic de Bruijn strip theorem is the highest-value current exposure edge and is supported by compiled analytic machinery. | Preregister both exact arbitrary-base endpoints; require public CI before Lean proof edits. |
| 2 | `PUBLIC_PREREGISTRATION_GATE -> LEAN_IMPLEMENTATION` | Preregistration commit `2685003e8f6617add0701a2b1680328ca8c4943f` passed public CI run `29571892273`, job `87857388857`, in `2m2s`. The standalone module now compiles the finite arbitrary-strip invariant, arbitrary-base Jensen zero persistence, exact `muSq-2*delta` contraction, and `t+y^2/2` all-real endpoint without warnings. | Register exact Targets, TargetChecks, and axiom prints; begin independent local audit. |
| 3 | `INDEPENDENT_LOCAL_AUDIT` | The exact module, both TargetChecks, Target registration, and total import compile. All five selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Placeholder, custom-declaration, unsafe, native-decision, and resource-relaxation scans are empty; `git diff --check` and the full 8,701-job build pass. | Classify locally as `KNOWN_THEOREM_FORMALIZED`; publish the implementation and require independent public CI before evidence backfill and closure. |
| 4 | `PUBLIC_IMPLEMENTATION_GATE` | Implementation commit `9ddee42657933ccd94533affa25f83a75392a1ea` passed public Lean Action CI run `29572752471`, build job `87860124993`, in `2m11s`. The public runner independently rebuilt the exact endpoints, Targets, TargetChecks, and axiom audit. | Backfill immutable implementation evidence; require the evidence commit's own public CI before closure. |

## Current Accounting

- `hard_gap_before`: unconditional Polymath canopy/barrier certification, H6-E/G8, and RH open
- `hard_gap_after`: unchanged
- `hard_gap_delta`: 0
- `classification`: `KNOWN_THEOREM_FORMALIZED_LOCAL`
- `route_infrastructure_delta`: 1
- `next_gate`: immutable evidence-backfill commit and public Lean Action CI

## Local Result

- `exact_quantitative_endpoint`: `deBruijnNewmanH_zero_im_sq_le_sub_two_mul` proves that a
  squared zero strip of width budget `muSq` at arbitrary real time `t` contracts to
  `muSq-2*delta` after every admissible `delta>=0`.
- `exact_all_real_endpoint`: `deBruijnNewmanAllZerosReal_add_half_sq` proves that a strip of
  half-width `y` becomes all-real after exactly `y^2/2` additional heat time.
- `proof_architecture`: finite vertical-average contraction, arbitrary-base compact-uniform heat
  approximation, multiplicity-free Jensen zero persistence, and an isolating closed ball.
- `axiom_status`: all five selected transitive audits contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`.
- `sorry_or_unchecked_declaration_used`: no.
- `claim_boundary`: known de Bruijn source infrastructure only. This does not prove
  `Lambda<=0.2`, any strict improvement below `0.2`, H6-E/G8, or RH.
- `persistent_goal`: active.

## Public Implementation Result

Implementation commit `9ddee42657933ccd94533affa25f83a75392a1ea` passed public Lean Action CI
run `29572752471`, build job `87860124993`, in `2m11s`. Campaign status is
`PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`; this backfill and its own public CI remain
before closure.
