# RH public exposure sprint

Sprint: `EXPOSURE-20260716-RH-SPINES-01`

Status: `PUBLIC_ENGINEERING_COMPLETE_P2_HUMAN_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_campaign`: yes; continued from the compact Weil closure checkpoint

## Loop 1: entry-point and provenance audit

- Read the external audit prescription and confirmed that the root README was still a generated
  placeholder.
- Confirmed the public repository, default branch, public CI workflow, Lean/mathlib pins, selected
  axiom audit, and the existing uncommitted auditor change in `HANDOFF.md`.
- Fixed the PNT+ source provenance at upstream commit
  `d963a6e694a05cd82e5f9b9ae7f4d94123e85393`; the snapshot entered this repository on 2026-07-10
  and was expanded through 2026-07-15.
- `result`: `EXPOSURE_SCOPE_FIXED`
- `hard_gap_before`: W1 full class, W2/G7 unconditional positivity, G3/M2, and RH open
- `hard_gap_after`: unchanged
- `hard_gap_delta`: zero; this sprint is review governance, not a proof campaign

## Loop 2: public spine and bounded novelty audit

- Replaced the placeholder README with four exact RH-equivalent criterion surfaces, explicit trust
  metadata, reproduction commands, and the remaining mathematical gaps.
- Searched the pinned mathlib tree, PNT+ source, official AFP catalog, selected external Lean
  repositories, and primary literature under a published fixed protocol.
- Found known mathematical sources for every criterion but no exact prior formal counterpart in
  the bounded source set. Recorded this only as a bounded negative result and made no
  first-formalization claim.
- `result`: `P3_BOUNDED_SCOPE_COMPLETE`
- `hard_gap_delta`: zero

## Loop 3: external review attempts

- Completed a clean-context read-only `gpt-5.6-sol` max audit of `LiReverseCriterion`,
  `LiWeilGram`, `WeilTestAlgebra`, `WeilCompactPositivityCriterion`, and the actual convolution
  companion. It found no P0-P2 issue and two P3 wording/attribution corrections; the older P1a
  result is not reused for this surface.
- Two in-app browser attempts failed before the Zulip page loaded; no login state was inspected
  and no message was sent. The generated announcement draft was removed after confirming that
  current mathlib policy requires public GitHub/Zulip prose to be human-authored.
- `result`: `P1B_COMPLETE_P2_HUMAN_PUBLICATION_PENDING`
- `hard_gap_delta`: zero
- `next_state`: publish the factual exposure materials and governance commit; the user may later
  write and send a review request from a working signed-in Zulip session

## Loop 4: V4.1 governance and review integration

- Integrated the clean-context review as `research/li_weil_sol_max_review_20260717.md`.
- Removed the old proof-admission interpretation of P1/P2/P3. They now govern external wording
  only, while exposure remains first priority in parallel with open proof attempts.
- Added a reusable mathlib upstream queue with the generic weighted-log `L2` equivalence ranked
  first for extraction.
- `result`: `EXPOSURE_PACKAGE_UPDATED`
- `hard_gap_delta`: zero
- `next_state`: finish repository verification and publication; P2 remains a human action

## Loop 5: local closure verification

- Verified the repository copy of `rh_directive_v4_1_20260717.md` is byte-for-byte identical to
  the user source in Downloads.
- The current-governance conflict scan finds no active RH/M2/G3/W2 prohibition; restricted wording
  remains only inside the verbatim V4.1 text that declares it abolished.
- Markdown relative links and `git diff --check` pass.
- `Targets.lean`, `TargetChecks.lean`, and `AxiomsAudit.lean` compile. Every printed dependency is
  among `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden proof-token, custom declaration, unsafe/opaque, and resource-relaxation scans are
  empty.
- Full `lake build` succeeds with 8,682 jobs; existing linter warnings do not affect compilation.
- `result`: `LOCAL_GOVERNANCE_AND_EXPOSURE_CLOSURE`
- `hard_gap_delta`: zero; no mathematical frontier is claimed changed
- `next_state`: publish the governance commit, then enter value-ranked route selection while P2
  remains a human-authored external action

## Loop 6: public closure evidence

- Governance commit `5c0a3eec14afbd02767e6b67fd4f7ba5c183a782` is public on `origin/main`.
- GitHub Lean Action CI run `29491764123`, build job `87599314511`, completed successfully in
  `2m10s`.
- `result`: `PUBLIC_EXPOSURE_ENGINEERING_COMPLETE`
- `hard_gap_delta`: zero; the result is governance, review, and publication infrastructure
- `next_state`: `ROUTE_SELECTION`; P2 stays pending as a human-authored external action and does
  not block research
