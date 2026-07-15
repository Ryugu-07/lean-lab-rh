# R5 Gaussian-Weil Reverse Criterion Campaign

Campaign: `CAMPAIGN-20260716-R5-GAUSSIAN-WEIL-REVERSE-CRITERION-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes; work continued from the preserved task summary,
  repository state, and external ACTIVE checkpoints

## Normalized Tuple

- `statement`: RH iff every positive-width finite real Gaussian-Weil arithmetic quadratic has
  nonnegative real part
- `assumptions`: existing xi divisor, finite Gaussian packet explicit formula, and standard
  Mathlib analysis only
- `strategy`: isolate an arbitrary off-line Gaussian decay layer by a finite real exponential
  separator, phase-lock its surviving contribution negative, and dominate the higher-layer tail
- `unresolved_frontier`: mathematical endpoint locally closed; implementation publication,
  public CI, and conservative novelty review remain

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP_AND_LITERATURE` | Compared the restricted Gaussian converse with full Weil positivity, Suzuki screw criteria, Arias de Reyna temperedness, and a recent unreviewed Polson SSRN claim. No density theorem is needed by the extremal-layer mechanism. | Audit the exact reverse proposition directly; treat possible literature overlap conservatively. |
| 2 | `CONJECTURE_GENERATION` | Fixed `q_p=-Re((rho_p-1/2)^2)`. A minimal off-line layer is finite, and a finite real exponential polynomial can kill every lower/same unwanted square class. | Test collisions, conjugates, real zeros, multiplicities, and infinite-tail cancellation before admission. |
| 3 | `ADVERSARIAL_TEST` | A synthetic finite zero model produces the predicted strict negative scaled sum. Independent checks show conjugate multiplicity matching is unnecessary, square-class collisions are harmless, and the real-zero branch is handled by `P^2*(X-1)`. | Proceed to Lean scratch; numerical output remains non-evidence. |
| 4 | `SCRATCH_ADMISSION` | Lean compiles exact packet factorization, finite sublevels, minimal off-line selection, finite collision-free exponential separation, real protected separator, width-one dominated convergence for the complete higher-layer `tsum`, phase-locked negativity, and real-axis negativity, all without `sorry`. | Admit the fixed iff endpoint and begin Proof Attempt A. Helper-only closure is forbidden. |
| 5 | `DISCOVERY_FORMAL_PROOF` | Lean constructs the actual finite unwanted `q≤q_0` divisor layer for an arbitrary selected off-line zero, annihilates every non-target square class, proves the surviving scaled low sum has negative real part, and combines it with the vanishing higher tail. The earlier global-minimality selection is unnecessary. | Continue to the direct arithmetic contradiction; do not weaken to zero-side negativity. |
| 6 | `DISCOVERY_EXPLICIT_FORMULA` | The existing Gaussian packet explicit formula converts the negative zero `tsum` into a finite real arithmetic quadratic at `c=2` with negative real part. Positivity for all finite `Type` index families therefore excludes every off-line nontrivial zero and implies RH. The exact iff compiles. | Promote the endpoint to the formal module and begin independent evidence checks. |
| 7 | `INDEPENDENT_AUDIT` | The 1,476-line formal module cold-compiles without warnings or placeholders. Exact Targets and TargetChecks compile. Six selected declarations, spanning separator, infinite tail, zero-side negativity, arithmetic negativity, reverse implication, and iff, use only `propext`, `Classical.choice`, and `Quot.sound`. | Run forbidden scans, diff validation, and the full project build. |
| 8 | `LOCAL_VERIFICATION` | Forbidden placeholder/declaration/resource scans are empty, `git diff --check` passes, and the full 8,674-job Lake build succeeds. | Classify conservatively as `KNOWN_THEOREM_FORMALIZED` pending independent novelty review; publish implementation and require public CI. |
| 9 | `PUBLIC_IMPLEMENTATION_CI` | Implementation commit `b2d2ce18ff1491f684098b04c7a5be73e0ebdc98` passed Lean Action CI run `29453270303`, build job `87480595744`, in `2m14s`. | Publish this immutable evidence backfill and require its own public CI before closure. |
| 10 | `PUBLIC_EVIDENCE_CI` | Evidence-backfill commit `68e96525f3f89562ae47e1da9e074911701a6c2e` passed Lean Action CI run `29453470463`, build job `87481233198`, in `1m24s`. | Publicly close the fixed campaign and return to fresh `INDEPENDENT_AUDIT -> ROUTE_SELECTION`; keep the persistent RH Goal active. |

## Current Accounting

- `hard_gap_before`: W2g0 is RH-forward only
- `hard_gap_after`: the restricted finite Gaussian arithmetic family is now an exact RH criterion;
  unconditional positivity and RH remain open
- `hard_gap_delta`: 0 for unconditional RH, W2, and G7
- `assumption_frontier_before`: no reverse theorem for the restricted family
- `assumption_frontier_after`: the reverse restricted-family implication is closed without density,
  temperedness, zero simplicity, zero enumeration, or a new premise
- `classification`: `KNOWN_THEOREM_FORMALIZED` pending independent novelty review; no first-proof
  or first-formalization claim
- `next_gate`: final closure-ledger commit and its public CI, then fresh route selection
