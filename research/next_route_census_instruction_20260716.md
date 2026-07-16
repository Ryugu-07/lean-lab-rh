# Historical Route Census Batch A

Date: 2026-07-16

Do not stop or complete the persistent RH Goal. This route-census and conjecture-generation batch
is a first-priority standing workstream under `research/rh_governance_current.md`; proof attempts,
including R5 re-entry with a materially new angle, may proceed in parallel.

Read, in order:

1. `research/rh_governance_current.md`
2. `HANDOFF.md`
3. `research/latest_progress_audit_20260716.md`
4. `research/rh_research_governance_v4_20260716.md`
5. `research/historical_route_census.md`
6. `research/literature_source_registry.csv`

Then perform `CENSUS-BATCH-A` for H1, H2, and H6:

- H1 classical critical-line, mollifier, and zero-proportion methods;
- H2 zero-density, mean-value, moment, subconvexity, and Lindelof-type methods;
- H6 de Bruijn-Newman heat flow and zero dynamics.

For each route create one source-faithful route card containing every field required by the census.
The search horizon is the full historical record, not 2025-2026. Begin from canonical primary
sources and trace major later developments. Record exact theorem strength, strongest unconditional
result, first unproved RH edge, known saturation or insufficiency results, and false-progress
patterns. Do not promote surveys to proof premises, and do not select papers by author seniority.

For each route generate exactly three original candidate statements:

1. one minimal bridge lemma;
2. one quantitative conjecture with explicit parameters;
3. one cross-route transfer conjecture involving an already mapped project route.

Adversarially test the candidates on paper. Do not add them as Lean premises and do not begin their
formalization. Label each `REJECTED`, `OPEN_CANDIDATE`, or `SHORTLIST_CANDIDATE` with reasons.

Update `research/literature_source_registry.csv` with every source actually used. Assign source
tiers from evidence. Unreviewed proof claims are evaluated by information value and never promoted
to premises without Lean verification.

Return:

- the three route-card paths;
- the source-registry diff;
- a coverage update to `research/historical_route_census.md`;
- the nine conjecture verdicts;
- one recommendation for Batch B.

Classification is `ROUTE_CENSUS`. Set `rh_frontier_delta=0`,
`route_infrastructure_delta=0`, and `engineering_delta=0`. The census itself does not advance RH.
Any proof candidate arising from it is preregistered as a separate `PROOF-ATTEMPT` before Lean
source edits.
