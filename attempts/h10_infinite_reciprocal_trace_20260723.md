# H10 Infinite Reciprocal-Trace Transfer Attempt

Campaign: `FALSIFICATION-20260723-H10-INFINITE-RECIPROCAL-TRACE-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: inherited-summary recovery completed before D9 implementation; canonical
  files and all D9 public CI coordinates were re-read before this route selection.
- `global_goal`: active.

## Baseline

- `parent_commit`: `276282262f033aeb3f106e7eb66180a92b23ec4d`.
- `parent_public_ci`: run `29955117117`, build job `89042095525`, passed in `2m2s`.
- `selected_node`: `H10-INFINITE-ORDINARY-TRACE-RECIPROCITY-01`.
- `preregistration`: `research/h10_infinite_reciprocal_trace_prereg_20260723.md`.

## Preregistered endpoint

Kernel-check the finite/infinite transfer boundary: finite spectra admit nonzero reciprocal
pairing and ordinary power sums, while a countably infinite spectrum cannot combine a nonzero
constant reciprocal pairing with ordinary summability of any positive power sequence.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `D9_PUBLIC_CLOSURE` | D9 final-ledger commit `276282262f033aeb3f106e7eb66180a92b23ec4d` passed run `29955117117`, job `89042095525`, in `2m2s`. | Return to historical breadth; actual Suzuki limit and RH remain open. |
| 2 | `CROSS_FAMILY_COMPARISON` | D3/D4 would repeat proportion or sparse-exception logic; D6 has several finite spectral campaigns; D11 has no source-backed individual-zeta transfer. | Select D7/H10 function-field transfer because only its finite rigidity step has been tested. |
| 3 | `SOURCE_RECONSTRUCTION` | Function-field point counts use a fixed finite Frobenius spectrum and ordinary all-power traces; number-field trace proposals require an infinite/regularized framework. | Test the most literal infinite ordinary-trace transfer before proposing new cohomology. |
| 4 | `FALSIFICATION_DESIGN` | Summable positive powers and their permutation reindexing both tend to zero, while reciprocal pairing makes their product the nonzero constant `q^k`. | Preregister the exact contradiction plus a finite reciprocal witness. |

## Assumption and gap accounting

- `assumption_frontier_before`: the finite power-sum rigidity theorem and reciprocal-pairing
  corollary are public; no number-field Frobenius spectrum or ordinary trace is available.
- `hard_gap_before`: construct a number-field spectral object, trace identity, positivity/weights,
  and a uniform infinite-tail or regularization theorem.
- `rh_frontier_before`: RH open.
- `candidate_obstruction`: a literal countable ordinary-power-trace extension is incompatible with
  nonzero reciprocal pairing.
- `expected_hard_gap_delta`: `0` for the generic audit.
- `expected_rh_frontier_delta`: `0`.
- `expected_route_map_delta`: `1`.
- `next_gate`: preregistration commit and public CI; no Lean proof-source editing beforehand.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
