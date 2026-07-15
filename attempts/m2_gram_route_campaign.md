# Exact Baez-Duarte Gram Route Campaign

Campaign: `CAMPAIGN-20260715-GRAM-01`

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget; campaign capped at six admitted loops
- `compaction_since_previous_campaign`: yes

## Route Selection

- Read the current worktree, HANDOFF, fixed DAG, Targets, prior projection/frequency audits, Loop
  Protocol V2, and the external Discovery Protocol V3 review.
- Preserved commit `5d75abc` as the stop of the recent-literature screening campaign only.
- Did not reopen Wong or Carvill.
- Compared five route families in `research/route_portfolio.md` and selected exact Baez-Duarte
  Gram/projection geometry.

## Candidate Screening

- Registered five precise mechanisms in `research/m2_gram_route_prereg_20260715.md`.
- Closest exact source found: Werner Ehm, arXiv `2405.06349`, which makes normalized scale geometry
  known mathematics rather than a novelty claim.
- Numerical weighted-log tests were used only to attack candidates and choose a proof target.
- Selected one candidate: an explicit `1/40` lower frame bound for normalized kernels at indices
  `(2^24)^j`.
- No numerical result and no unproved candidate has been admitted as a premise.

## Frontier Before Proof

- `hard_gap_before`: M2/G3 parked
- `hard_gap_after`: unchanged during route selection
- `hard_gap_delta`: zero
- `assumption_frontier_before`: no unconditional exact target-closure membership
- `assumption_frontier_after`: unchanged
- `activity_result`: `ROUTE_SELECTION_COMPLETE`
- `research_progress`: none yet

## Next Proof Attempt

One indivisible Lean batch may define the normalized exact kernels and sparse indices, prove the
physical diagonal lower bound and off-diagonal envelope, assemble the finite lower frame bound, and
add the finite-dimensional falsification witness for Gram positivity. Partial helpers do not close
the campaign and do not count as RH progress.

## Proof Attempt Result

- `result`: `AUXILIARY_PROPERTY_PROVED`
- `proof_file`: `LeanLab/Riemann/M2GramGeometry.lean`
- `selected_candidate`: C4
- `candidate_statement_changed`: no
- `numerical_premise_used`: no
- `sorry_or_unchecked_declaration_used`: no

The single admitted attempt succeeded. Lean verifies:

1. the exact physical Gram integral and normalized complex inner-product alignment;
2. the uniform diagonal lower bound `1/24`;
3. the three-region off-diagonal integral envelope;
4. the sparse distance envelope `(2+24*d)/4096^d` and a summable geometric relaxation;
5. the uniform off-diagonal row bound `4/297`;
6. the finite complex Gram-form estimate
   `(1/40) * sum |c_i|^2 <= ||sum c_i*u_((2^24)^i)||^2`;
7. a typed positive-definite finite Gram family with a nonzero orthogonal target, rejecting C5 as a
   target-closure mechanism.

## Progress Accounting

- `activity_result`: `LEAN_PROOF_ATTEMPT_COMPLETE`
- `research_progress`: exact auxiliary sparse-frame property proved
- `hard_gap_after`: M2/G3 remains parked
- `hard_gap_delta`: zero
- `assumption_frontier_after`: unchanged; no unconditional exact target-closure membership
- `novelty_after`: `NOVELTY_UNCHECKED`
- `next_state`: `ROUTE_SELECTION`

This is useful geometry but not an RH bridge. The lower-frame theorem controls coefficient
stability inside one sparse closed span; it gives no approximation of
`baezDuarteComplexTargetL2` by that span. A successor campaign must propose and falsify a precise
target-coupling mechanism rather than extend constants or add generic Gram wrappers.

## Verification

- new module: passed standalone Lean compilation and Lake module build
- `TargetChecks.lean`: exact statement witnesses pass
- `AxiomsAudit.lean`: key declarations use only `propext`, `Classical.choice`, and `Quot.sound`
- full `lake build`: passed with 8618 jobs
- forbidden placeholder, explicit declaration, `native_decide`, and resource-relaxation scans:
  empty
- `git diff --check`: passed
- commit, push, and public CI: pending at this checkpoint
