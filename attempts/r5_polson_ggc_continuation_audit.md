# R5 Polson GGC Continuation Audit

Audit: `AUDIT-20260716-R5-POLSON-GGC-CONTINUATION-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: no

## Normalized Tuple

- `statement`: a single Levy-Frullani exponential component evaluated at `s=i*y` is not
  integrable on `(1,infinity)` once `y^2>2*gamma^2`
- `assumptions`: `gamma>0` and `y^2>2*gamma^2`
- `strategy`: exact complex specialization followed by real exponential-growth nonintegrability
- `unresolved_frontier`: construct a warning-free Lean proof of the tail divergence

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `LITERATURE_ROUTE_MAP` | Compared the 2018 arXiv source with the 2026 SSRN abstracts. The newer formulation makes critical-line Thorin positivity RH-equivalent and claims unconditional positivity only in the right-half-plane region. No peer-reviewed correction of the 2018 continuation argument was found. | Audit the exact 2018 integral-domain passage without attributing the result to the revised 2026 framework. |
| 2 | `FALSIFICATION_CANDIDATE_SCREEN` | Four broad continuation/positivity mechanisms fail before admission. The single-component imaginary-axis tail has an exact positive exponential growth rate when `y^2>2*gamma^2` and survives boundary/sign checks. | Pre-register that one endpoint and begin Falsification Attempt A. |
| 3 | `FALSIFICATION_PROOF` | `PolsonGGCContinuationAudit.lean` identifies the exact complex component at `s=i*y` with the real source integrand and proves that both the real integrand and complex component are not integrable on `(1,infinity)` when `gamma>0` and `y^2>2*gamma^2`. | The fixed source-specific endpoint is Lean-checked without placeholders; proceed to independent audit. |
| 4 | `INDEPENDENT_AUDIT` | Exact Targets and TargetChecks compile. The three selected transitive axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`; forbidden-token, declaration, resource-relaxation, and scratch-name scans are empty. | Accept the theorem only as an audit of retention of the 2018 defining integral. Do not transfer it to analytic continuation or the revised 2026 framework. |
| 5 | `LOCAL_VERIFICATION` | Standalone compilation, the dedicated module build, `Targets.lean`, `TargetChecks.lean`, `AxiomsAudit.lean`, `git diff --check`, and the full 8,675-job build pass. | Classify locally as `BRANCH_ELIMINATED`; publish implementation and require public CI. |
| 6 | `PUBLIC_IMPLEMENTATION_VERIFICATION` | Implementation commit `0c174e82713c18be16ae9ea3afd5197b77ab4347` passed public Lean Action CI run `29455171888`, build job `87486632024`, in `1m50s`. | Backfill immutable evidence and require that evidence commit's own public CI before closure. |
| 7 | `PUBLIC_EVIDENCE_VERIFICATION` | Evidence commit `d277252fa21de89e228a2d1db6addd727d975d99` passed public Lean Action CI run `29455360041`, build job `87487225276`, in `2m2s`. | Close the audit as `BRANCH_ELIMINATED`; do not reopen this exact 2018 integral-retention mechanism without new source evidence. |

## Current Accounting

- `hard_gap_before`: G6/W1 and G7/W2 open; G3/M2 historically unselected (open under V4.1)
- `hard_gap_after`: unchanged
- `hard_gap_delta`: 0
- `assumption_frontier_before`: unchecked retention of the 2018 integral outside its convergence
  region
- `assumption_frontier_after`: the original 2018 integral representation is rejected in the tested
  imaginary regime `y^2>2*gamma^2`; analytic continuation and the revised 2026 framework remain
  outside this theorem
- `classification`: `BRANCH_ELIMINATED`
- `next_gate`: fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION` under the active RH Goal
