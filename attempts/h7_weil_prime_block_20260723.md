# H7 Weil Prime Block Attempt

Campaign: `LITERATURE-20260723-H7-WEIL-PRIME-BLOCK-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Baseline

- `parent_commit`: `48e57d28b7e8ec98042cb7f21b836f6eb1c98adc`.
- `parent_public_ci`: run `29971448611`, build job `89094128646`, passed in `1m47s`.
- `selected_node`: `H7-WEIL-FINITE-PRIME-SOURCE-INSTANTIATION-01`.
- `preregistration`: `research/h7_weil_prime_block_prereg_20260723.md`.
- `global_goal`: active.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `PARENT_PUBLIC_CLOSURE` | H7 pole-block final ledger passed public CI. The actual pole block is even-nonnegative and odd-nonpositive; prime and archimedean compensation remains open. | Close only the pole endpoint and return to cross-route selection. |
| 2 | `CROSS_ROUTE_SELECTION` | Compared the actual prime block, actual archimedean block, H7 scalar bound, H1 Mellin/contour bridge, and surviving historical routes. | Select the finite prime source because it directly stress-tests the adverse pole sign without numerical optimization or an infinite limit. |
| 3 | `SOURCE_RECONSTRUCTION` | The prime source is a finite sum of negative von Mangoldt sine atoms at frequencies `1-log(q)/log(C)`; derivative diagonals are explicit. | Lock the source samples, atom sum, reflection sectors, and integer-cutoff convention. |
| 4 | `SIGN_STRESS_TEST` | For the actual prime-power atom `C=16,q=8`, the frequency is `1/4`; direct level-one algebra predicts a negative center-even value and a positive edge-odd value. | Preregister this as an exact Lean witness, not as a numerical observation or a statement about the full prime block. |
| 5 | `PREREGISTRATION` | Ten fixed Lean items, success/failure criteria, and claim boundaries are recorded. | Publish and require public CI before creating production Lean source. |

## Frontier accounting

- `rh_frontier_before`: RH open.
- `hard_gap_before`: total Weil parity ordering, the arithmetic Herglotz scalar inequality,
  simple-even uniformity, source transform convergence, and the D3 Mellin/contour bridge are open.
- `registered_delta`: instantiate only the finite integer-cutoff prime source and one exact
  constituent sign witness.
- `expected_information`: determine whether a source normalization mismatch exists and whether
  termwise semidefinite prime compensation is possible.
- `hard_gap_after_if_success`: aggregate prime and archimedean control and every global H7 edge
  remain open.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.

