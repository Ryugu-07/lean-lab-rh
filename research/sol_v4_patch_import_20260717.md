# Sol V4 Patch Import Record

Date: 2026-07-17

## Source

- Archive: `/Users/karasuakamatsu/Downloads/RH_GOVERNANCE_V4_PATCH.zip`
- Archive SHA-256: `95820ea9624685c1e272889b159a49e98adc67844219bbaf3083b77b5e59550d`
- Mail patch: `0001-Add-historical-RH-route-governance.patch`
- Patch SHA-256: `0614df14a0c47421aa72bac45a40939ec67516665b5d73e5fffde661ed7bba8c`
- Patch base: `f4eea7a9c91c4b30864f02369912ad87d0b0d1b2`
- Original no-conflict commit identity: `54282ec5643288f2a2cc599b2c0f9883f74f424f`

## Imported artifacts

- `historical_route_census.md`
- `latest_progress_audit_20260716.md`
- `literature_source_registry.csv`
- `next_route_census_instruction_20260716.md`
- `rh_research_governance_v4_20260716.md`

The patch also modified HANDOFF, the loop/discovery protocols, the hard-gap DAG, and the route
portfolio. Those older diffs were not applied wholesale because the current branch already
contains later V4.1 governance and exposure work. Their durable facts were merged into the current
files instead.

## V4.1 adaptation

The imported route identifiers, source rows, audit counts, three-ledger distinction, route history,
and H1/H2/H6 Batch A deliverables are retained. The following V4 clauses have no current force and
were removed from the imported working documents:

- proof-campaign freeze and census admission gate;
- R5 route cooldown;
- route/campaign count limits;
- percentage work allocations and recent-paper quota;
- the requirement that conjectures be weaker than RH;
- independent-review approval as a prerequisite for attempting a theorem.

Current authority is [`rh_governance_current.md`](rh_governance_current.md), with the user ruling
preserved verbatim in [`rh_directive_v4_1_20260717.md`](rh_directive_v4_1_20260717.md).

The source registry's `S0-S4` labels retain their imported literature meaning. Lean mechanical
evidence is recorded separately as `K0` in
[`source_grade_registry_20260717.md`](source_grade_registry_20260717.md), avoiding an overloaded
`S0` label.
