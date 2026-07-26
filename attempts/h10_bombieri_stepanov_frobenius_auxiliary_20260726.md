# H10 Bombieri--Stepanov Frobenius Auxiliary

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01`

Selected node: `H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01`

Status: `IMMUTABLE_EVIDENCE_PUBLIC_GREEN / FINAL_LEDGER_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / FALSIFICATION`.
- `exact_target`: formalize the finite-field Frobenius descent, perfect-power multiplicity, and
  root-degree budget used inside the Bombieri--Stepanov point-count proof.
- `relation_to_RH`: successful function-field RH mechanism and structural analogy only; no
  number-field transfer without a new trace/cohomology object and controlled infinite tail.
- `success`: generic endpoint, full multiplicity budget, and saturated `ZMod 2` witness.
- `falsification`: any failure of Frobenius expansion, rational-point descent, multiplicity gain,
  or the claimed saturation under the exact preregistered hypotheses.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the D9 Conrey--Li conditional phase-obstruction campaign. | Final ledger `fca9616b7580eeff45b7591a66eb061cf4a94af9` passed run `30196032626`, job `89777631633`, in `1m32s`. | Return to historical-route selection. |
| `CROSS_FAMILY_AUDIT` | Compared D3, D4, D5, D6, D7, D9, and H12 after their latest campaigns. | D7/H10 alone has a successful historical proof family whose construction core remains largely unformalized; only its finite spectral endpoint and an infinite ordinary-trace obstruction are compiled. | Select the Bombieri--Stepanov auxiliary mechanism. |
| `PRIMARY_SOURCE_AUDIT` | Read Stepanov's high-multiplicity polynomial construction and Bombieri/Kedlaya's Frobenius descent presentation. | The proof separates finite-field evaluation, perfect-power multiplicity, nonzero kernel production, pole-degree control, and the later spectral step. | Fix only the finite-field algebra and multiplicity budget. |
| `API_SURVEY` | Checked finite-field cardinal powers, characteristic-`p` sum powers, polynomial roots, Hasse derivatives, root multiplicities, and degree bounds. | The fixed polynomial model has a direct no-sorry formalization surface; curve Riemann--Roch and divisor prerequisites remain unavailable. | Publish docs-only preregistration before proof edits. |
| `PREREGISTRATION_PUBLIC` | Published docs-only commit `44ecd3bcda10a2687d3eac965c312a00ce90007b`. | Public run `30204699920`, build job `89800633257`, passed in `1m53s`. | Open the fixed production gate. |
| `GENERIC_FROBENIUS_ALGEBRA` | Defined the base, descent, and auxiliary polynomials and proved the characteristic-`p` expansion. | `stepanovFrobeniusAuxiliary_eq_sum` compiles for finite polynomial families over a commutative semiring with `ExpChar`. | Specialize the cardinal exponent at finite-field points. |
| `RATIONAL_POINT_DESCENT` | Used `r * p^mu = card K` and finite-field Frobenius evaluation. | `stepanovFrobeniusAuxiliary_eval_eq_descent` identifies every rational-point value with the descent polynomial. | Impose the source kernel identity without hiding nonzero production. |
| `HIGH_MULTIPLICITY` | Kept `base != 0` explicit and proved the auxiliary is a nonzero perfect `p^mu`-power. | Every finite-field point has root multiplicity at least `p^mu` when the descent vanishes. | Convert local multiplicity to a global degree budget. |
| `ROOT_DEGREE_BUDGET` | Summed root multiplicities over an arbitrary finite set and specialized to the universal finite-field finset. | Both `p^mu * card K <= natDegree F` and `card K <= natDegree F / p^mu` compile. | Test whether the algebra leaves any strict slack. |
| `SATURATION_TEST` | Constructed the preregistered `ZMod 2` kernel witness. | The base is nonzero, the descent is zero, roots `0` and `1` have exact multiplicity `2`, and `2 * card (ZMod 2) = natDegree F = 4`. | Record that the algebraic budget is sharp; move omission search to the curve-level construction. |
| `LOCAL_GATES` | Ran warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles; scanned forbidden declarations and resource relaxations; ran the full build. | One proven Target, seven exact checks, six standard-only axiom prints, empty scans, and `8769/8769` build all pass. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC` | Published frozen implementation `61bb73ad666e3bdd4ba460bedd93af16256c997d`. | Public run `30205411443`, build job `89802493185`, passed in `2m31s`. | Keep `LeanLab/` frozen and publish immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC` | Published docs-only evidence `89b7dead3b9a9344dc34c16a1d9e0bfa0c2cd792` and compared it with the frozen implementation. | Public run `30205553507`, build job `89802869900`, passed in `1m30s`; `LeanLab/` diff is empty. | Publish the final ledger and require its own public CI. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; canonical governance, D9 closure,
  HANDOFF, route census, ranked atlas, H10 card, source registry, and primary sources were
  reread before selection.
- `global_goal`: active.

## Current boundary

Local result: `KNOWN_FUNCTION_FIELD_MECHANISM_FORMALIZED`.

The finite-field Frobenius/descent/multiplicity mechanism is valid and its degree budget can be
saturated. This closes neither the Bombieri--Stepanov curve proof nor H10. The live historical
frontier is the construction of a nonzero optimized auxiliary from Riemann--Roch spaces,
polar/tensor injectivity, and pole-degree control; the number-field transfer and RH remain open.
The six inherited user/exposure files remain untouched and unstaged.

Frozen implementation: `61bb73ad666e3bdd4ba460bedd93af16256c997d`. No Lean proof-source
changes are permitted during immutable evidence and final-ledger publication.

After final-ledger CI, close only this fixed source-algebra endpoint and return the active global
Goal to historical route selection. Keep the H10 curve-geometric construction and all
number-field bridges open; conjecture generation and direct RH attacks remain available.
