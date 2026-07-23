# H7 Weil Prime Block Attempt

Campaign: `LITERATURE-20260723-H7-WEIL-PRIME-BLOCK-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PUBLIC_IMPLEMENTATION_CI_PASSED / IMMUTABLE_EVIDENCE_CI_REQUIRED`

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
| 6 | `PREREGISTRATION_PUBLIC_CI` | Commit `21fad44edcbb9277ca7f3142e776ca2f78d2df09` passed run `29971859428`, build job `89095368881`, in `1m34s`. | Open the fixed production proof-source gate. |
| 7 | `SOURCE_AND_DIAGONAL_ALIGNMENT` | Lean proves frequency bounds, coefficient signs and vanishing, and that the displayed cosine sample is the actual derivative of the sine source. | Use only certified samples in the divided-difference matrix. |
| 8 | `ATOM_SUM_AND_REFLECTION` | Lean proves the aggregate source matrix is exactly the finite sum of atom matrices and preserves both reflection sectors. | Feed the actual source into the existing parity interface without assuming a block sign. |
| 9 | `ACTUAL_ATOM_SIGN_WITNESS` | Lean proves `omega(16,8)=1/4`, the `q=8` coefficient is negative, and its level-one even/odd quadratic values are respectively negative and positive. | Register a termwise semidefinite-sign obstruction; do not promote it to the aggregate block. |
| 10 | `TARGET_AXIOM_AND_BUILD_GATES` | One proven Target, 12 exact TargetChecks, 9 standard-only axiom prints, empty forbidden scan, diagnostic-free 297-line module, `git diff --check`, and the 8,754-job full build pass. | Freeze the registered local endpoint and require public implementation CI. |
| 11 | `PUBLIC_IMPLEMENTATION_CI` | Frozen implementation commit `cc264cde977a8b04e596d267aa6656cd8cbf4058` passed Lean Action run `29973199798`, build job `89099433656`, in `2m8s`. | Keep Lean source frozen and publish immutable evidence coordinates. |

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
- `local_result`: `FULL_SUCCESS_AT_PRIME_ENDPOINT`; no source, derivative, cutoff, reflection, or
  sign normalization mismatch was found. The atom obstruction does not decide the aggregate
  prime block. Public implementation CI passes; immutable evidence and final-ledger gates remain.
- `definition_alignment`: `research/h7_weil_prime_block_definition_alignment_20260723.md`.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
