# Historical Route Census Batch A

Campaign: `CENSUS-BATCH-A-20260717-H1-H2-H6`

Mode: `LITERATURE`

Status: `COMPLETE_ROUTE_SELECTION_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; recovered from the V4.1 governance and exposure summary
- `global_goal`: active

## Preregistered endpoint

Produce source-aligned route cards for H1, H2, and H6; generate exactly one bridge, one explicit
quantitative, and one cross-route candidate per card; adversarially classify all nine without
using any as a proof premise.

Success required three cards, a source-registry update, census coverage updates, nine exact
verdicts, and one Batch B recommendation. Falsification required rejection of any candidate whose
claimed implication fails in a finite or sparse symmetric-zero model.

## Loop 1: Sol V4 patch import under V4.1

- Read `/Users/karasuakamatsu/Downloads/RH_GOVERNANCE_V4_PATCH.zip` and verified archive SHA-256
  `95820ea9624685c1e272889b159a49e98adc67844219bbaf3083b77b5e59550d`.
- Imported the H0-H14 census, progress audit, source registry, Batch A instruction, and V4 source.
- Removed the superseded proof freeze, route cooldown, numerical allocations, recent-paper quota,
  and theorem-admission gates while retaining route history and three-ledger accounting.
- Preserved Sol's literature tiers `S0-S4`; the distinct Lean mechanical evidence label is `K0`.
- `result`: `V4_SOURCE_ASSETS_IMPORTED_V4_1_PRECEDENCE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Loop 2: H1/H2/H6 source census

- H1: traced Levinson-Conrey to Pratt-Robles-Zaharescu-Zeindler and fixed the audited frontier at
  slightly above `5/12` of zeros on the critical line.
- H2: separated zero-free, zero-density, moment, and pointwise-value claims; recorded Bourgain's
  `13/84` critical-line subconvexity exponent and Guth-Maynard's
  `30*(1-sigma)/13 + o(1)` zero-density exponent.
- H6: aligned `H_0(z) = (1/8) xi((1+iz)/2)`, the backward heat equation convention, the
  Rodgers-Tao lower bound, and the Polymath upper bound `0.22`; the exact RH edge is `Lambda = 0`.
- Added three exact candidate statements per route. Density-to-Li transfers H1-X and H2-X were
  rejected because one finite or sparse off-line orbit survives the density premise but is caught
  by the Li dominant-transform mechanism.
- `result`: `ROUTE_CENSUS_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Outputs

- `research/route_card_H1_critical_line_mollifiers_20260717.md`
- `research/route_card_H2_density_moments_20260717.md`
- `research/route_card_H6_de_bruijn_newman_20260717.md`
- `research/census_batch_A_conjecture_audit_20260717.md`
- `research/literature_source_registry.csv`

## Verification and next decision

No Lean source was edited and no mathematical theorem is claimed.

- The source CSV has 24 unique rows and the expected 11-column schema.
- Relative Markdown links and `git diff --check` pass.
- The active-governance conflict scan finds no restored proof freeze, quota, cooldown, or
  preapproval rule.
- `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` compile.
- Every printed dependency is among `propext`, `Classical.choice`, and `Quot.sound`.
- Scans for `sorry`, `admit`, `native_decide`, `sorryAx`, project `axiom`/`constant`,
  `unsafe`/`opaque`, and resource-limit relaxations are empty.
- Full `lake build` succeeds with 8,682 jobs; existing linter warnings do not affect compilation.

Next enter `ROUTE_SELECTION`. H6-B is the best bounded Batch A formalization candidate, but it must
be compared with direct RH, W2/G7, and M2/G3 attacks. Batch B recommendation is the required H10
Bombieri-Stepanov/function-field transfer-gap card.
