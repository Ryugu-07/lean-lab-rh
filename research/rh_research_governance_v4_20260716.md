# RH Research Governance V4 (Historical Source, V4.1-Adapted)

Date: 2026-07-16

Status: `SUPERSEDED_IN_PART`

This is the imported Sol V4 governance source. Its route-before-paper method, source tiers,
historical census, independent-audit semantics, and three-ledger accounting remain useful. The user
V4.1 ruling supersedes its proof freezes, route cooldowns, numerical allocations, and campaign
admission gates. Current authority is [`rh_governance_current.md`](rh_governance_current.md).

## Operating State

- `PERSISTENT_GOAL`: `ACTIVE`
- `PROOF_CAMPAIGN_ADMISSION`: `OPEN_WITH_PREREGISTRATION`
- `OPEN_DIRECT_TARGETS`: `RH / W2-G7 / M2-G3 / ALL_UNRESOLVED_PROPOSITIONS`
- `CLAIM_AUDIT_MODE`: `MECHANICAL_OUTPUT_GATES`
- `SOURCE_REGISTRY`: `research/literature_source_registry.csv`
- `NEXT_DECISION`: value-ranked route selection while the census proceeds in parallel

Existing Lean files remain valid evidence. Do not delete or weaken them. Any mathematical proof
campaign may start after its exact endpoint, success/falsification criteria, and known obstacle are
preregistered.

## Route Before Paper

Research selection is not limited to 2025-2026, arXiv recency, or papers found by broad web search.
For a problem with a 165-year history, the unit of exploration is a mathematical route family, not
an isolated paper.

For every route family:

1. begin with an authoritative overview and the route's original or canonical primary sources;
2. trace important predecessor and successor work across decades;
3. identify the strongest unconditional theorem, not the strongest claim;
4. state the first unproved edge to RH and known negative or saturation results;
5. only then inspect recent papers that make that edge more precise.

Author age, seniority, affiliation, and fame are not admissibility criteria. Source quality,
mathematical specificity, independent uptake, and checkability are.

## Source Tiers

Every source used for route selection receives exactly one provisional tier. The tier may be raised
or lowered only with recorded evidence.

| tier | meaning | allowed use |
| --- | --- | --- |
| S0 | Canonical primary source, established theorem, or authoritative problem description with durable independent use. | May anchor a route card and a known-theorem formalization. |
| S1 | Peer-reviewed or independently developed specialist work in an established route, with precise assumptions and conclusions. | May motivate a campaign after statement alignment. |
| S2 | Specialist preprint or recent result with a precise checkable mechanism but incomplete independent uptake. | May motivate reconnaissance; cannot alone certify novelty or progress. |
| S3 | Isolated, unreviewed, or self-declared proof claim; unclear provenance; or a paper whose decisive step has not been independently checked. | Low-confidence input for proof or falsification attempts; never a premise without Lean verification. |
| S4 | Withdrawn, contradicted, or formally falsified mechanism. | Negative evidence and regression tests only. |

The registry must distinguish a source's publication status from the status of the specific theorem
being used. Publication is evidence, not a proof of correctness; a preprint is not false merely
because it is new.

These `S0-S4` labels grade literature only. `K0` mechanical Lean evidence is defined separately in
[`source_grade_registry_20260717.md`](source_grade_registry_20260717.md).

## Historical Route Census Workstream

`research/historical_route_census.md` is the fixed route-level map. As the workstream proceeds:

- every `CANONICAL` route must have a route card;
- every card must contain at least one primary-source anchor and one later audit or development;
- exact RH strength must be classified as `EQUIVALENT`, `RH_IMPLIED`, `PARTIAL_PROGRESS`,
  `STRUCTURAL_ANALOGY`, or `HEURISTIC_ONLY`;
- the strongest unconditional result and first unproved edge must be explicit;
- known dead ends, insufficiency results, and common false-progress patterns must be recorded;
- project coverage must be marked `NONE`, `DEFINITION_ONLY`, `PARTIAL`, `SOURCE_ALIGNED`, or
  `DEEP_FORMALIZATION`;
- a clean-context reviewer should audit a cross-route shortlist of mathematically distinct
  candidates.

"Explore a route" means map and stress-test it. It does not mean formalize every theorem in the
route. Breadth improves selection quality, but incomplete breadth does not block a direct attempt.

## Three Progress Ledgers

Do not use one integer `hard_gap_delta` for three different kinds of work.

1. `rh_frontier_delta`: changes a canonical edge whose completion would strictly shorten
   a path to `Mathlib.RiemannHypothesis`.
2. `route_infrastructure_delta`: formalizes a published theorem, exact criterion, test class, or
   source-faithful bridge while the same RH-hard assumption remains.
3. `engineering_delta`: closes a helper or a subedge introduced to implement the current campaign.

Rules:

- A campaign cannot create or rename a child edge and count its closure as `rh_frontier_delta`.
- If the parent canonical gap remains open with the same assumption frontier, then
  `rh_frontier_delta = 0`.
- `BRIDGE_REDUCED` is reserved for positive `rh_frontier_delta` supported by a compiled theorem,
  exact witness, axiom audit, and independent claim review.
- Known explicit formulas, equivalent criteria, parameter compressions, and finite test families
  normally have positive `route_infrastructure_delta` and zero `rh_frontier_delta`.
- Branch falsification is recorded separately and never converted into positive RH progress.

The historical `BRIDGE_REDUCED` labels on W1 child edges are retained as chronology. Under V4 they
are interpreted as route-infrastructure progress unless the top-level W1/G6 frontier itself changes.

## Global Anti-Cycling And Route Selection

Anti-cycling state is global across campaigns, files, target names, and compactions.

- Repeating a failed route requires a materially new preregistered attack angle.
- Splitting a theorem into a Gaussian case, translate family, finite packet, fixed width, compact
  cutoff, and arithmetic evaluation does not turn infrastructure into RH progress.
- A new internal child edge does not by itself justify a positive `rh_frontier_delta`.
- `NO_PROGRESS` triggers value-ranked `ROUTE_SELECTION`; it does not impose a timed or counted
  cooldown.

R5 has a long recorded run and multiple exact obstructions, but remains open under V4.1.

## Independent Audit Semantics

An `INDEPENDENT_AUDIT` must be performed from a clean context by a different model/agent role, or
by an external human reviewer. It must read the exact source, theorem statements, assumptions,
axiom prints, and diff. The same model continuing in the same accumulated context records
`SELF_AUDIT`; that is useful but is not independent evidence for a public progress claim.

An audit verdict is one of:

- `CONTINUE`
- `PIVOT`
- `BATCH`
- `ROUTE_SELECTION`
- `STOP_BRANCH`
- `REQUEST_EXTERNAL_REVIEW`

## Original Conjecture Forge

The historical census does not reduce the project to replaying old papers. Once a route card is
source-aligned, the model should generate candidate new statements at its actual first unproved
edge. For each selected route, generate at least:

- one minimal bridge lemma;
- one quantitative statement with explicit constants or asymptotics;
- one cross-route transfer statement connecting two independently mapped mechanisms.

Each candidate must be falsifiable and accompanied by boundary tests and a closest-known-result
audit. It may be equivalent to, stronger than, or directly equal to RH when that strength is stated
explicitly. A failed candidate is useful negative evidence. A vague analogy is not a conjecture.

## Work Selection

There are no numerical allocations. Rank canonical route mapping, source alignment, original
conjecture testing, recent claims, and direct proof attacks by expected mathematical value,
information gained on failure, and leverage from checked infrastructure. Exposure remains the
current first priority and may proceed in parallel.

## Output Classification Checklist

Before a campaign reports progress, record:

1. the exact selected endpoint and its canonical DAG or route position;
2. source tiers for literature actually used;
3. exact compiled theorem and TargetChecks witness, when the result is mathematical;
4. transitive axiom audit and witness/definition alignment;
5. separate `rh_frontier_delta`, `route_infrastructure_delta`, and `engineering_delta`;
6. the attempt log and OBS node for a failed attack.

This checklist gates claims, not attempts.
