# H9 Conrey Rationality-Gap Preregistration

Date: 2026-07-23

Campaign: `FALSIFICATION-20260723-H9-CONREY-RATIONALITY-GAP-01`

Mode: `FALSIFICATION`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Baseline and route selection

- `parent_commit`: `02e8f746a1afacf87d74196883e909f0053a8618`.
- `parent_public_ci`: Lean Action run `29937476151`, build job `88982651332`, passed in `2m9s`.
- `previous_campaign`: H1 short-mollifier variational sufficiency is publicly closed. Its
  long-mean-value and sparse-exception barriers remain open, but further optimization of that
  functional is not automatic.
- `selected_node`: `H9-CONREY-RATIONALITY-FLAT-INTERVAL-01`, inside ranked door D10 (arithmetic
  criteria, character sums, and Speiser derivatives).
- `route_comparison`: H10 function-field finite spectral rigidity is already compiled and its
  remaining transfer lacks a number-field trace object and uniform infinite tail. H2 density and
  H11 statistics still cannot localize one exceptional off-line zero. D10 is the highest-ranked
  atlas door not yet tested by a theorem-producing campaign.
- `material_difference`: this campaign does not optimize a character-sum bound. It checks a
  specific algebraic inference in a published RH route and isolates the exact branch that the
  source calls unlikely but does not exclude.
- `global_goal`: active; this finite rationality audit does not prove or disprove RH.

## Primary source and exact audit point

Primary source: Brian Conrey,
[*Character sums and the Riemann Hypothesis*](https://doi.org/10.4064/aa230530-13-11), Acta
Arithmetica 214 (2024), 327-342, registered as S1.

For squarefree `q congruent to 3 mod 8`, the source defines

```text
S_q(y) = sum_{n <= y} chi_q(n) * (1 - n/y)
```

and proves that `f_q(x)` is a positive factor times `S_q(q/2)-S_q(qx)`. Proposition 1 states
that `f_q(x)=0` implies that `x` is rational. For a fixed prefix `m=floor(qx)`, write

```text
A_m = sum_{n <= m} chi_q(n),
B_m = sum_{n <= m} n*chi_q(n),
H   = S_q(q/2).
```

The displayed calculation gives `A_m-B_m/(q*x)=H`. The printed rationality inference requires
`B_m != 0`. If `B_m=0`, the equation only forces `A_m=H` and is independent of `x` throughout
that prefix interval. Later in the same paper the source explicitly records the alternatives

```text
A_m = H and B_m = 0,
or q*x = B_m/(A_m-H),
```

but describes the first as unlikely rather than proving it impossible. This campaign audits that
unclosed branch. It does not classify Proposition 1 itself as false unless an actual
quadratic-character flat interval is kernel-certified.

## Exact mathematical target

For an arbitrary integer-valued prefix `chi(1),...,chi(m)`, first prove

```text
sum_{n=1}^m chi(n)*(1-n/y) = A_m-B_m/y.
```

Then prove: if `q != 0`, `x != 0`, and `A-B/(q*x)=H`, then

```text
(B=0 and A=H)
or
(B!=0 and A!=H and x=B/(q*(A-H))).
```

When `q,A,B,H` are rational or integral, the second branch makes `x` rational. Finally give a
kernel-checked countermodel to the omitted generic inference by taking `B=0`, `A=H`, and
`x=sqrt(2)`: the affine-fraction equation holds while `x` is irrational.

## Proposed Lean spine

The intended module is `LeanLab/Riemann/ConreyCharacterSumRationality.lean`:

1. `conreyPrefixMass`;
2. `conreyPrefixMoment`;
3. `conreyWeightedPrefix`;
4. `conreyWeightedPrefix_eq_mass_sub_moment_div`;
5. `conreyAffineFraction_eq_dichotomy`;
6. `conreyAffineFraction_eq_rat_or_flat`;
7. `conreyAffineRationalityInference_counterexample`.

The finite identity, exact dichotomy, rational-or-flat corollary, and irrational countermodel
receive exact TargetChecks and selected `#print axioms` entries.

## Success, falsification, and stopping criteria

- `success`: all proposed declarations compile and pass the mechanical gates and public CI.
- `stronger_falsification`: an actual squarefree `q congruent to 3 mod 8` and prefix interval are
  kernel-certified with `A_m=H` and `B_m=0`, refuting the published Proposition 1. No such witness
  is currently claimed.
- `source_repair`: if a missing source lemma proves `B_m!=0` for every relevant prefix, compile
  the repaired implication instead.
- `no_progress`: record any exact rational-cast API obstruction; do not substitute floating-point
  evidence.
- `local_stop`: stop after the corrected branch structure and countermodel are publicly closed,
  or after a checked nonzero-moment repair. The global positivity conjecture, Theorem 3, and
  Speiser's equivalence are separate campaigns.

## Falsification reconnaissance

- Exact arithmetic checked Theorem 5's `test_a(p,q)` sign against Corollary 1 for every permitted
  `a` and prime pair `p<q<300`, `p congruent to q congruent to 3 mod 8`: 120 pairs, no mismatch or
  nonpositive value.
- Exact scans covered 1,453 composite squarefree `q congruent to 3 mod 8` below 20,000 and found
  no negative value.
- A second exact scan covered all 2,024 squarefree `q congruent to 3 mod 8` below 20,000 and found
  no zero or flat interval.
- These computations are navigation only and will not become Lean premises.

## Assumption and implication audit

- `assumption_frontier_before`: the proof treats `B_m/(q*x)` as determining `x` without
  separating `B_m=0`.
- `assumption_frontier_after_on_success`: rationality follows only on the nonflat branch; the flat
  branch becomes an explicit source obligation.
- `rh_boundary`: Conrey's global positivity condition implies RH through separate Mellin/Landau
  arguments. This campaign imports none of them.
- `expected_deltas`: `rh_frontier_delta=0`, `hard_gap_delta=0`,
  `source_proof_gap_delta=1`, `obstruction_map_delta=1` on success.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: one inherited-summary recovery after local preregistration; canonical
  governance, current attempt, preregistration, handoff, hard-gap DAG, and worktree state were
  re-read before proceeding.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit only this preregistration, its attempt record, the H1 final-CI backfill, source-registry
upgrade, and synchronized ledgers first. Public Lean Action CI must pass before proof-source,
Targets, TargetChecks, AxiomsAudit, or aggregate imports are edited.

## Implementation backfill

- `preregistration_commit`: `7e682226d4ac7965ba0f02265578d1c71dc0d9ad`.
- `preregistration_public_ci`: Lean Action run `29939270138`, build job `88988711235`, passed in
  `2m3s`.
- `local_result`:
  `PROVED / SOURCE_GENERIC_INFERENCE_FALSIFIED / ACTUAL_CHARACTER_PROPOSITION_OPEN`.
- `compiled_spine`: all seven proposed declarations plus the explicit flat-prefix constancy
  theorem compile; five exact TargetChecks and selected axiom audits pass.
- `full_build`: `8,741` jobs, passed locally.
- `implementation_commit`: `4c9939496e6a508c2f5e631ad3fa5ede9f5a69aa`.
- `implementation_public_ci`: Lean Action run `29940099631`, build job `88991480954`, passed in
  `1m56s`.
- `proof_source_state`: frozen.
- `next_gate`: immutable evidence commit and public CI.
