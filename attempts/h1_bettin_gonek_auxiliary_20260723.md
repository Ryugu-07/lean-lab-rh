# H1 Bettin--Gonek Auxiliary Attempt

Campaign: `LITERATURE-20260723-H1-BETTIN-GONEK-AUXILIARY-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

## Baseline

- `parent_commit`: `d4196d0f47d42f1c95d29b48dd341b9a469c514b`.
- `parent_public_ci`: run `29968166845`, build job `89084084918`, passed in `1m54s`.
- `selected_node`: `H1-BETTIN-GONEK-AUXILIARY-REGULARIZATION-01`.
- `preregistration`: `research/h1_bettin_gonek_auxiliary_prereg_20260723.md`.
- `global_goal`: active.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `PARENT_PUBLIC_CLOSURE` | The theta-infinity consumer final ledger passed public CI. The real-cutoff and power-consumer edges close; the analytic bridge remains open. | Return the exact source bridge to value-ranked selection; do not mark H1 exhausted. |
| 2 | `SOURCE_RECONSTRUCTION` | Bettin--Gonek equations `(2.2)`--`(2.3)` isolate a quotient with both the zeta pole and selected-zero denominator, followed by an explicit simple-pole coefficient. | Test the removable singularities and residue algebra before attempting contour estimates. |
| 3 | `LIBRARY_ALIGNMENT` | Existing `zetaPoleRemoved` is entire, and Mathlib `dslope` gives the canonical holomorphic divided difference at a zero. | Use this exact regularization; never rely on totalized raw division at the patched point. |
| 4 | `PREREGISTRATION` | The auxiliary equality, holomorphy domain, punctured-neighborhood coefficient, nonvanishing, claim limits, and outcomes are locked. | Publish and require public CI before proof-source editing. |
| 5 | `PREREGISTRATION_PUBLIC_CI` | Commit `452e266613b7c8444de9366f1f65a6c1352dd219` passed run `29968683311`, build job `89085640497`, in `2m13s`. | Open the fixed proof-source gate. |
| 6 | `REMOVABLE_SINGULARITY_ALIGNMENT` | Lean proves `zetaPoleRemoved rho=0` and uses `dslope zetaPoleRemoved rho` to recover `(s-1)zeta(s)/(s-rho)` away from the patched points. | The source quotient has a canonical holomorphic extension; raw totalized division is not used at the selected zero. |
| 7 | `AUXILIARY_HOLOMORPHY` | The regularized `G_t` equals the raw source formula off the patched points and is holomorphic on `Re(w)>-1`. | The source half-plane contains no additional local singularity. |
| 8 | `SELECTED_POLE_CERTIFICATE` | Lean proves the exact punctured-neighborhood coefficient displayed in equation `(2.3)` and proves it nonzero for every nontrivial zero and `x>0`. | There is no hidden local cancellation of the selected-zero term; move the gap to contour and decay estimates. |
| 9 | `TARGET_AND_AXIOM_GATES` | One proven auxiliary Target, 10 exact TargetChecks, and 7 selected standard-only axiom prints compile; the 277-line module is diagnostic-free and its forbidden scan is empty. | Run diff checks, the full build, and public implementation CI. |
| 10 | `LOCAL_MECHANICAL_CLOSURE` | `git diff --check` and the 8,752-job full build pass. The seven selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`. | Freeze the implementation and require independent public CI before closing this auxiliary endpoint. |
| 11 | `IMPLEMENTATION_PUBLIC_CI` | Frozen implementation commit `2dd7fcb2284b9fe9afd3e01792a6a6c199a770f9` passed run `29969572291`, build job `89088421970`, in `2m4s`. | Keep Lean proof source frozen; publish immutable evidence and require its own public CI. |

## Frontier accounting

- `hard_gap_before`: inverse Mellin support/decay, contour shift, convolution, residue lower bound,
  moment integration, and uniform constants in the Bettin--Gonek bridge.
- `rh_frontier_before`: RH open.
- `registered_delta`: remove only the local removable-singularity and selected-pole algebra layer.
- `falsification_value`: detect a hidden source normalization, singularity, or zero residue before
  building contour infrastructure.
- `hard_gap_after_if_success`: the global analytic estimates and integral identities remain open.
- `local_result`: `FULL_SUCCESS_AT_AUXILIARY_ENDPOINT` at the local mechanical gate, pending
  immutable-evidence and final-ledger gates. No source regularization mismatch was found.
- `definition_alignment`:
  `research/h1_bettin_gonek_auxiliary_definition_alignment_20260723.md`.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
