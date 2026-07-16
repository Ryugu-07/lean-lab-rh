# RH Current Governance

Date: 2026-07-17

Status: **canonical and active**. This file is the single operational source of truth. Earlier
protocols and attempt records remain historical evidence but cannot reintroduce superseded gates.

> RH 是你的目标。你可以直接攻击它，也可以攻击通往它的任何未决命题。你的每一次尝试——成功编译的定理、失败后记录的障碍——都是这个项目的正资产。唯一的规则是：让编译器替你说话。

## Authority and merged sources

- User ruling: [`rh_directive_v4_1_20260717.md`](rh_directive_v4_1_20260717.md), preserved
  verbatim from `/Users/karasuakamatsu/Downloads/rh_directive_v4_1_20260717.md`.
- Adapted dual-audit record:
  [`rh_governance_sol_claude_audit_20260717.md`](rh_governance_sol_claude_audit_20260717.md).
- Current route source:
  [`rh_route_atlas_and_conjecture_factory_20260717.md`](rh_route_atlas_and_conjecture_factory_20260717.md).
- Source policy: [`source_grade_registry_20260717.md`](source_grade_registry_20260717.md).
- Public/upstream queue: [`mathlib_upstream_queue_20260717.md`](mathlib_upstream_queue_20260717.md).

V4.1 overrides every V4 clause that imposed an input-side restriction, including proof freezes,
preapproval for W2 or RH, route/week or paper-review quotas, commit/line fuses, and the former
status of M2/G3. The later user Goal refines V4.1's three labels into the four operating modes
below: `LITERATURE` includes known-mathematics formalization.

## Persistent goal

The global Goal is to advance Lean-checked research on `Mathlib.RiemannHypothesis` in this
repository. It remains active until the user explicitly pauses it or Lean proves or disproves
`Mathlib.RiemannHypothesis` without newly introduced nonstandard axioms.

RH, W2/G7, and M2/G3 are open targets. Any of them may be attacked directly. No research attempt
requires user, Sol, Claude, or other preapproval.

## Four operating modes

Every research campaign has one primary mode:

- `LITERATURE`: audit, reconstruct, and formalize a human proof route; identify its exact frontier
  and documented obstruction.
- `DISCOVERY`: propose a new identity, bound, approximation family, operator structure, positivity
  mechanism, spectral interpretation, or bridge lemma and attempt to prove it.
- `PROOF-ATTEMPT`: directly attack an open proposition, including RH or an unconditional side of
  an equivalent criterion.
- `FALSIFICATION`: search for counterexamples, edge cases, finite models, numerical failures, or
  Lean refutations of a proposed statement.

Exposure and upstreaming are standing duties, not a fifth mode. The current exposure sprint is the
first priority and may proceed in parallel with proof work.

Mode selection must be active rather than ceremonial. After a campaign ends, `ROUTE_SELECTION`
chooses the next target by mathematical value from the hard-gap DAG, route atlas, obstruction map,
and conjecture pool. Ease of manufacturing a local lemma is not a selection criterion.

## Campaign preregistration

Before proof edits, every campaign records:

- exact mathematical statement;
- proposed Lean statement, or the exact definition/inventory question when no statement exists;
- success and falsification criteria;
- known obstacles and the nearest prior attempt;
- closest primary literature or explicit originality rationale;
- position in the hard-gap DAG;
- assumption frontier before the attempt;
- what is materially new about the attack angle.

Use [`attempts/PROOF_ATTEMPT_TEMPLATE.md`](../attempts/PROOF_ATTEMPT_TEMPLATE.md) for direct
attacks. Failure is recorded in `attempts/` and as an `OBS` obstruction node. A failed campaign
does not pause the global Goal.

## Conjecture admission and CI

A model-original conjecture cannot become a premise. Before it enters the conjecture pool, record:

1. its exact mathematical proposition and proposed Lean statement;
2. its DAG location and whether it is equivalent to, stronger than, or implies RH;
3. counterexample, boundary-case, finite-model, and numerical falsification attempts;
4. the closest known result found through source-grade search;
5. the node unlocked if the conjecture is proved.

The conjecture then passes three gates: numerical falsification, consistency with compiled Lean
facts, and implication value. Surviving a gate is not a proof and never licenses downstream use.

## Mechanical truth gates

A theorem may become a downstream premise only after all of the following hold:

- the exact Lean declaration compiles without `sorry`, `admit`, `native_decide`, custom axioms,
  `opaque`, `unsafe`, or relaxed resource options;
- `LeanLab/Riemann/TargetChecks.lean` contains both name resolution and an exact statement witness
  for a completed spine;
- `LeanLab/Riemann/AxiomsAudit.lean` records the declaration and `#print axioms` shows only the
  accepted Lean/mathlib trust base;
- witness/counterexample objects used by the argument are kernel-checked rather than merely
  numerical;
- new criterion definitions receive an M0-style item-by-item alignment against primary sources;
- the claim is classified honestly as infrastructure, known theorem formalized, obstruction,
  falsification, conjecture, or research progress.

Numerical evidence and prose reasoning can select a target, but they cannot become mathematical
premises unless replaced by checked theorems.

## Output and publication gates

Research input is open; claims are gated. Any statement of RH progress must point to a compiled
theorem, its exact statement witness, its axiom audit, and its definition-alignment record.
Infrastructure is labeled infrastructure.

README, Zulip, papers, release notes, or any priority/"first" claim require user + audit model +
Claude signoff. This is an output rule only. Under current mathlib contribution policy, public
GitHub/Zulip prose must be written by the human author in their own words; the repository may
provide factual theorem names, links, and audit evidence, but no AI-authored message is posted.

## Historical route atlas and exposure priority

The fixed route atlas, not an endless stream of recent manuscripts, is the default source of
candidate routes. H1, H2, and H6 route cards and the nine-candidate audit remain required, and the
function-field Bombieri-Stepanov line should receive an early source card. These research tasks do
not restrict direct attacks on other open nodes.

Exposure remains the current first priority: maintain the README, complete bounded novelty and
definition review, split mathlib-ready components, and assemble human-owned publication evidence.
P1/P2/P3 describe release readiness; none blocks proof campaigns.

## Local stopping and global persistence

A local campaign stops or pivots when its preregistered endpoint is proved, falsified, or reduced
to a precisely recorded external obstruction; when the same failed mechanism has no materially
new attack angle; or when continued work would only manufacture bookkeeping lemmas. `NO_PROGRESS`
is valid output and triggers `ROUTE_SELECTION`.

There are no numerical loop, commit, line, route/week, or literature quotas. Local `STOP` never
stops the global Goal. Re-entry into a prior route is allowed when the preregistration states the
substantive difference from the last failure.

## Loop record and compaction recovery

At the end of every loop, update the relevant attempt log with mode, target, result, assumption
frontier, theorem names, compiler and axiom-audit results, obstacles, next route decision, model,
reasoning effort when exposed, budget when exposed, compaction state, and commit/CI evidence.

After compaction or an inherited summary, re-read this file, `HANDOFF.md`,
`LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`, the current attempt log,
`research/hard_gap_dag.md`, and the relevant route preregistration before selecting or proving the
next target. A summary is navigation evidence, not authority over repository source files.
