# R5 Compact Weil Arithmetic Formula Campaign

Campaign: `CAMPAIGN-20260716-R5-COMPACT-WEIL-ARITHMETIC-FORMULA-01`

Date: 2026-07-16

Status: `PREREGISTERED`

Mode: `DISCOVERY -> PROOF_ATTEMPT_A`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap; campaign bounded by the fixed
  complete compact-smooth arithmetic explicit-formula endpoint
- `compaction_since_previous_campaign`: no

## Fixed-Gap Record

- `node_id`: W1
- `gap_id`: G6
- `work_class`: FORMALIZATION
- `result_class`: pending
- `assumption_frontier_before`: the reflection-symmetrized compact-smooth class has a complete
  zero-side cutoff, but its right-line pole, GammaR, and von-Mangoldt evaluation are external
- `assumption_frontier_after`: pending
- `hard_gap_before`: W1c1 is open on the compact arithmetic side
- `hard_gap_after`: pending
- `expected_hard_gap_delta`: 1 at the W1c1 compact arithmetic subedge
- `commit_sha`: pending

## Normalized Tuple

- `statement`: every smooth compactly supported additive-log function satisfies the complete
  reflection-symmetrized xi explicit formula with an explicit finite physical von-Mangoldt side
- `assumptions`: `ContDiff R infinity f`, `HasCompactSupport f`, and `1<c`
- `strategy`: Schwartz Fourier inversion with exact `2*pi` scaling, right-half-plane L-series
  interchange, compact sixth-order decay, the compiled generic pole residue skeleton, and GammaR
  logarithmic growth
- `unresolved_frontier`: exact Fourier normalization for both reflected branches, finite natural
  support of the physical prime weight, and generic compact pole/GammaR full-line control

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `INDEPENDENT_AUDIT -> ROUTE_SELECTION` | The compact zero-side campaign is publicly closed with preregistration, implementation, evidence, and closure CI. W1c1 now has one remaining compact arithmetic subedge; W2/G7 and parked G3/M2 remain open. | Rotate from LITERATURE to DISCOVERY and test whether current Fourier, contour, and decay interfaces suffice for the complete compact arithmetic formula. |
| 2 | `DISCOVERY_INTERFACE_AUDIT` | Mathlib converts `C_c^infinity` functions directly to Schwartz maps and supplies pointwise Fourier inversion. The project supplies the generic two-pole rectangle residue identity, selected-height zero limit, sixth-order compact decay, GammaR digamma growth, and absolutely convergent von-Mangoldt L-series for `c>1`. | Screen a full arithmetic endpoint against partial helper and repeated-criterion alternatives. |
| 3 | `FIVE_CANDIDATE_ADVERSARIAL_SCREEN` | Prime inversion alone, pole/Gamma helpers alone, and finite physical support alone are incomplete endpoints. A new compact RH-equivalent positivity criterion repeats the compiled Gaussian separator without an unconditional sign mechanism. The complete compact formula combines all nontrivial interfaces and changes W1c1. | Admit and preregister the quantified complete compact arithmetic formula before any Lean proof edit. |

## Preregistration

The exact statement, source boundary, proof DAG, five-candidate screen, adversarial tests, and
rejection conditions are fixed in
`research/r5_compact_weil_arithmetic_formula_prereg_20260716.md`.

No Lean proof file has been edited for this campaign at preregistration time.
