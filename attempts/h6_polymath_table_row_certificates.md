# H6 Polymath Table-Row Certificates Attempt Log

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Status: `ACTIVE_LOOP_1_PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

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
| 1 | `LITERATURE` | Compiled `riemannHypothesisUpTo`, the general finite-height-RH transport, and the exact Table 1 specialization through height `3*10^12`. The `x=0` boundary uses `deBruijnNewmanH_mul_I_ne_zero`; the positive branch derives the exact `x/2` zeta ordinate and contradicts the positive lower `y` boundary. Standalone checks, exact witnesses, standard-only axiom prints, forbidden scans, and the full 8,704-job build pass locally. This is conditional on `riemannHypothesisUpTo (3*10^12)` and proves no unconditional region. | Keep the campaign active. Loop 2 should attack the source-normalized effective Riemann--Siegel approximation and error consumer needed by the final and barrier certificates; do not build interval infrastructure detached from an exact `H_t` statement. The finite RH computation, final region, and barrier remain open. |

## Mechanical audit

- exact module compilation: passed for `DeBruijnNewmanTableRowCertificates.lean`
- `Targets.lean`: passed with one in-progress campaign target and one proven conditional subedge
- `TargetChecks.lean` exact witness: four exact witnesses passed
- `AxiomsAudit.lean` and printed axioms: the three new theorem prints contain only
  `propext`, `Classical.choice`, and `Quot.sound`
- forbidden token/declaration/resource scan: empty
- witness audit: external numerical outputs rejected as witnesses
- definition/source alignment: exact `H_0`/xi coordinate, positive ordinate, and Table 1 height
  arithmetic compiled; Platt--Trudgian remains an unproved external computational theorem
- full `lake build`: passed locally, 8,704 jobs

## Loop 1 accounting

- `compiled_theorems`:
  `RiemannHypothesis.riemannHypothesisUpTo`,
  `deBruijnNewmanPolymathInitialRegionZeroFree_of_riemannHypothesisUpTo`, and
  `deBruijnNewmanPolymathInitialRegionZeroFree_table_row_of_rh_up_to_three_trillion`
- `assumption_frontier_after`: the transport from finite RH through `3*10^12` to the Table 1
  initial predicate is K0; the finite RH premise itself is not K0
- `hard_gap_after`: all three unconditional Table 1 certificates, H6-E/G8, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `obstacle_record`: no finite-zero certificate or Turing completeness proof was obtained; the
  final-region approximation and compact barrier certificate were not attacked in Loop 1

## Public evidence

- preregistration commit `652c816cca25c6517fee9654511335ce912ac132` passed public Lean Action CI
  run `29629630395`, build job `88040634155`, in `2m16s`
- implementation commit `ac96523034b36e2bfafdb007d6dcd95d8e89b625` passed public Lean Action CI
  run `29630082237`, build job `88041893271`, in `1m52s`
- immutable evidence-backfill CI: pending

## Runtime record

- `model`: GPT-5 Codex; exact deployment identifier not exposed
- `reasoning_effort`: not exposed
- `budget`: persistent Goal has no token budget; no per-loop budget exposed
- `compaction_state`: inherited a compaction summary, then re-read canonical governance,
  `HANDOFF.md`, hard-gap DAG, route atlas, current attempt, exact Lean predicates, and primary
  source text before selection
- `persistent_goal`: active
