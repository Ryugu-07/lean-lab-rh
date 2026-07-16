# R5 Compact Weil Zero-Cutoff Campaign

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-ZERO-CUTOFF-01`

Date: 2026-07-16

Status: `LOCALLY_COMPLETE`

Mode: `LITERATURE -> PROOF_ATTEMPT_A`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap; campaign bounded by the fixed
  generic compact-smooth zero-cutoff endpoint
- `compaction_since_previous_campaign`: yes; route selection re-read the preserved task summary,
  repository HANDOFF, compiled Targets, attempts, route portfolio, hard-gap DAG, and protocol

## Fixed-Gap Record

- `node_id`: W1
- `gap_id`: G6
- `work_class`: FORMALIZATION
- `result_class`: `BRIDGE_REDUCED`
- `assumption_frontier_before`: the generic contour theorem takes transform differentiability,
  reflection symmetry, complete divisor summability, and top-edge decay as hypotheses
- `assumption_frontier_after`: for every reflection-symmetrized `ContDiff R infinity`
  compactly supported Laplace weight, all four generic zero-cutoff premises are now derived from
  smoothness and compact support
- `hard_gap_before`: generic source-faithful W1c1 rectangle/zero cutoff is open
- `hard_gap_after`: the compact-smooth zero-side cutoff is complete; the generic compact
  arithmetic prime, pole, and archimedean evaluation, W2/G7, and RH remain open
- `expected_hard_gap_delta`: 1 at the W1c1 compact zero-side subedge
- `preregistration_commit_sha`: `e70201cb71b0909ae3f7b798336931e0bd9f32ee`
- `commit_sha`: pending publication

## Normalized Tuple

- `statement`: every smooth compactly supported log-line function, after explicit Laplace
  reflection symmetrization, satisfies the selected-height xi zero-side limit
- `assumptions`: `ContDiff R infinity f`, `HasCompactSupport f`, and `1<c`
- `strategy`: dominated complex differentiation, divisor reflection, sixfold integration by parts,
  `R^(-6)` compact-transform decay, and absorption of the compiled `R^4` xi top-edge bound
- `unresolved_frontier`: arithmetic evaluation of the resulting compact-weight right-line
  integral, including normalized prime Fourier inversion and the generic archimedean term

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `INDEPENDENT_AUDIT -> ROUTE_SELECTION` | Re-read the fixed W1/W2 frontier after compaction. W1c1 and W2/G7 remain open; the previous local-prime sign audit is publicly closed and cannot be continued as a same-sign assembly route. | Rotate to LITERATURE and audit the classical compact-support explicit formula against current Lean interfaces. |
| 2 | `LITERATURE_AND_INTERFACE_AUDIT` | Connes--Consani Appendix B/C confirms the smooth compact-support test class and finite-prime arithmetic side. The project already has a generic selected-height contour theorem, compact reciprocal-square divisor summability, and a selected-edge `O(R^4)` log-derivative bound. The existing twofold compact decay is quantitatively insufficient. | Screen fixed endpoints centered on sixfold compact decay and the generic zero cutoff. |
| 3 | `FIVE_CANDIDATE_ADVERSARIAL_SCREEN` | Full arithmetic evaluation is a larger successor; prime inversion alone and pole/Gamma helpers are incomplete endpoints; another compact reverse criterion repeats the Gaussian route. Reflection symmetrization avoids an evenness premise, while six integrations by parts should leave an `O(R^(-2))` top integral. | Admit the quantified compact-smooth zero-side endpoint and preregister it before Lean proof edits. |
| 4 | `LEAN_PROOF_ATTEMPT_A` | `WeilCompactLaplaceZeroCutoff.lean` proves whole-plane differentiability by dominated complex differentiation, exact reflection, multiplicity-bearing divisor summability through the xi reflection equivalence, arbitrary iterated compact-support integration by parts, a fixed-strip inverse-sixth-power estimate, and an `O(R^(-2))` selected top-edge integral. The generic contour theorem then proves the exact preregistered limit. | Accept the exact endpoint without weakening or extra premises and advance to independent local audit. |
| 5 | `INDEPENDENT_LOCAL_AUDIT` | The 373-line module is diagnostic-free. Exact Targets and TargetChecks compile; five selected transitive axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden declaration, proof-placeholder, resource-option, and scratch scans are empty; `git diff --check` passes; the full 8,680-job build succeeds. | Classify as `BRIDGE_REDUCED`, with `hard_gap_delta=1` only at the fixed W1c1 compact zero-side subedge. Publish implementation and require independent public CI before immutable evidence closure. |

## Preregistration

The exact statement, five-candidate screen, source boundary, proof DAG, adversarial tests, and
rejection conditions are fixed in
`research/r5_compact_weil_zero_cutoff_prereg_20260716.md`.

No Lean proof file was edited for this campaign at preregistration time. Preregistration commit
`e70201cb71b0909ae3f7b798336931e0bd9f32ee` passed public Lean Action CI run `29463597042`, build
job `87511970349`.

## Local Result

The exact endpoint now compiles as
`tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral` in
`LeanLab/Riemann/WeilCompactLaplaceZeroCutoff.lean`. The proof discharges every premise of
`tendsto_selectedXiRightVerticalIntegralFor` from `hf`, `hfsupp`, and `hc`; it assumes no evenness,
top-edge limit, transform differentiability, or divisor summability.

The module, exact target witness, selected axiom audit, empty forbidden scans, aggregate import,
`git diff --check`, and the full 8,680-job build pass locally. This closes the compact-smooth
zero-side cutoff only. The full compact arithmetic explicit formula, W2/G7, and RH remain open.
Implementation publication and public CI remain before campaign closure.
