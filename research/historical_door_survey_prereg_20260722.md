# Historical Door Survey Preregistration

Date: 2026-07-22

Campaign: `LITERATURE-20260722-HISTORICAL-DOOR-SURVEY-01`

Mode: `LITERATURE`

Status: `PREREGISTERED / SURVEY_CONTENT_PENDING_PUBLIC_CI`

## Baseline and route decision

- `parent_commit`: `b0695dbede5d931631639f235d4b83d1a5562f7e`.
- `baseline_public_ci`: Lean Action run `29916917447`, build job `88912843208`, passed in `1m45s`.
- `previous_campaign`: Loop 31 publicly closed the Stieltjes/Boyd equation `(15)` subroute.
- `route_decision`: park the numerical H6/Polymath upper-bound successor and survey the full
  historical route portfolio before selecting another main proof route.
- `material_difference`: earlier census work built source cards for H1, H2, H6, and H10 and
  classified nine candidates. This campaign compares every admitted historical family under one
  omission-seeking schema, audits whether old obstacles remain valid, and ranks openings across
  routes rather than selecting the first locally tractable lemma.
- `current_ruling`: [`historical_door_survey_current_20260722.md`](historical_door_survey_current_20260722.md).
- `persistent_goal`: RH remains the target; the global Goal remains active.

## Exact inventory target

Produce `research/door_atlas_ranked_20260722.md` with:

1. a source-backed coverage table distinguishing deep formalization, source-aligned cards,
   mention-only routes, and unmapped routes;
2. complete cards for every admitted door;
3. the exact last proved node and exact missing object for each route;
4. documented failures and an audit of whether each failure is still operative;
5. mature domain machinery not yet aimed at the exact RH edge;
6. unconditional RH-frontier progress, if any, separated from criteria and infrastructure;
7. formalization fit and machine-task fit;
8. overlooked-opening hypotheses, cross-route combinations, and evidence against them;
9. at most three precise future probes per door;
10. a ranked comparison, one recommendation, one runner-up, and explicit ranking-reversal
    evidence.

The initial census has twelve comparison families:

- criteria/positivity;
- heat flow/zero dynamics;
- critical-line proportions/mollifiers;
- density/moments/subconvexity;
- zero statistics/random matrices;
- spectral/trace/noncommutative geometry;
- function fields/cohomology/weights;
- Laguerre--Polya/Jensen;
- de Branges/canonical systems;
- arithmetic/classical analytic/Speiser criteria;
- generalized/automorphic L-functions and Iwasawa analogies;
- countermodels and falsified mechanisms.

Distinct mechanisms discovered through citations must be added rather than forced into this list.

## Source and comparison method

- Begin from Bombieri's Clay problem description, Conrey's RH survey, Sarnak's problem notes,
  Titchmarsh, Iwaniec--Kowalski, and the existing H0--H14 census.
- Trace decisive positive and negative claims to primary papers wherever available.
- Record bibliographic metadata and stable URLs in the source registry or atlas.
- Treat numerical agreement, analogy, and sociological popularity as navigation evidence only.
- Distinguish a theorem-level obstruction from failure of one implementation, a missing estimate,
  and absence of a published attempt.
- Search explicitly for later work that weakens, repairs, or bypasses the recorded obstacle.
- Compare cross-route interfaces, especially positivity/spectral, density/Li, function-field/
  explicit-formula, and entire-function/canonical-system connections.

## Success and falsification criteria

- `success`: every admitted family has a complete card and primary-source anchor; all old project
  status claims are reconciled; the ranked recommendation is justified by obstacle validity,
  exact missing object, available unused machinery, and omission evidence rather than ease.
- `meaningful_partial`: a bounded source frontier proves that a claimed route or obstruction was
  materially misclassified, or a distinct missing family is added with a complete card, while
  unresolved cards are named explicitly.
- `falsification`: a supposed overlooked opening is already closed by a counterexample,
  impossibility theorem, RH-equivalent assumption, or circular dependency. Record that result as
  an obstruction asset rather than quietly deleting the candidate.
- `no_progress`: sources do not distinguish a real opening from an old restatement; record the
  uncertainty and continue to the next door.

## Conjecture and probe lane

The survey does not close conjecture generation. A precise conjecture may be proposed, screened,
or Lean-tested at any time under the standing conjecture gates. It may not enter the atlas as a
proved bridge or displace unfinished high-value cards merely because the probe is easy. Any
survey-triggered proof or falsification campaign receives its own preregistration and returns to
this campaign afterward.

## Anti-substitution and output discipline

- Do not replace a failed RH edge with a finite prefix, fixed test, improved constant, or
  conditional implication and call the route promising.
- Do not rank by mathlib convenience, number of immediate lemmas, recentness, or theorem count.
- Do not claim that humans overlooked an opening without a source-backed account of what was and
  was not attempted.
- Do not claim exhaustiveness beyond the stated source boundary.
- Internal atlas prose may classify evidence; any external priority or novelty claim still needs
  the standing three-party signoff.

## Publication sequence

This preregistration, current-ruling record, H6 park status, and handoff update must be committed
and pass public CI before substantive atlas cards or ranking are written. The completed atlas then
receives implementation, closure-evidence, and final-ledger commits with public CI, following the
existing research-log pattern.

## Runtime disclosure

- `compaction_state`: no inherited compaction in this survey campaign at preregistration.
- `model`: Codex, GPT-5 family; exact serving variant and reasoning effort are not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `global_goal`: active.

