# H6 Polymath Table-Row Certificates Attempt Log

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Status: `PREREGISTERED_PENDING_PUBLIC_CI`

## Target

- `mode`: `LITERATURE`
- `node_id`: H6-Q1
- `exact_mathematical_statement`: prove the specialized initial, final, and barrier zero-free
  predicates at `(t0,X,y0)=(93/500,5*10^12+194858,16733/100000)` and then
  `deBruijnNewmanAllZerosReal (1/5)` without hypotheses
- `relation_to_RH`: weaker than RH; reconstructs the known unconditional `Lambda<=0.2` frontier
- `success_criterion`: all four exact theorems compile, pass statement witnesses, standard-only
  axiom audit, full build, and public implementation/evidence CI
- `falsification_criterion`: a kernel-checked counterexample or a precise failure of source
  coverage, normalization, interval enclosure, winding implication, or finite-zero completeness

## Prior state

- `assumption_frontier_before`: the exact conditional Polymath criterion is publicly K0; its
  three region hypotheses remain unproved
- `hard_gap_before`: Table 1 initial/final/barrier certificates, H6-E/G8, and RH open
- `known_obstacles`: finite RH completeness through `3*10^12`; source-aligned effective
  Riemann--Siegel error bounds; large proof-producing transcendental interval certificates;
  compact barrier winding and mesh coverage
- `nearest_primary_source`: Polymath arXiv `1904.12438`, Theorems 1.2/1.3, Corollary 1.4,
  Sections 7--8, Table 1; Platt--Trudgian arXiv `2004.09765`
- `nearest_project_attempt`: `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`, publicly
  closed at the three explicit region predicates
- `new_attack_angle`: consume the now exact region interfaces and reconstruct the numerical proof
  as kernel-checkable rational certificates, starting with a source-aligned finite-RH transport
  that fixes the coordinate and height boundary

## Source reconnaissance

External repository `km-git-acc/dbn_upper_bound` was inspected at
`5fde84e11ba80adad5c225a4eaa0a28b68dc925d`. It contains Arb source, stored sums, and the exact
row's winding summary. The repository grants no software license, and none of its code or decimal
output is imported. Every numerical fact must be independently re-proved in Lean.

## Attempt log

| loop | mode | result | next decision |
| --- | --- | --- | --- |
| 0 | `ROUTE_SELECTION / LITERATURE` | Fixed the full hypothesis-free Table 1 endpoint after source and external-artifact audit. Identified the three independent certificate layers and the exact first subedge from finite-height RH to the initial region. No proof source edited. | Commit and publicly build the preregistration. Only after green CI, begin Loop 1 on the exact finite-height transport; do not assert the external computation. |

## Mechanical audit

- exact module compilation: pending proof-source phase
- `Targets.lean`: pending
- `TargetChecks.lean` exact witness: pending
- `AxiomsAudit.lean` and printed axioms: pending
- forbidden token/declaration/resource scan: pending
- witness audit: external numerical outputs rejected as witnesses
- definition/source alignment: preregistered against Polymath and Platt--Trudgian
- full `lake build`: pending preregistration commit CI

## Runtime record

- `model`: GPT-5 Codex; exact deployment identifier not exposed
- `reasoning_effort`: not exposed
- `budget`: persistent Goal has no token budget; no per-loop budget exposed
- `compaction_state`: inherited a compaction summary, then re-read canonical governance,
  `HANDOFF.md`, hard-gap DAG, route atlas, current attempt, exact Lean predicates, and primary
  source text before selection
- `persistent_goal`: active
