# H10 Bombieri--Stepanov Frobenius Auxiliary

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01`

Selected node: `H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01`

Status: `PREREGISTERED / PUBLIC_PREREGISTRATION_CI_REQUIRED`

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

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; canonical governance, D9 closure,
  HANDOFF, route census, ranked atlas, H10 card, source registry, and primary sources were
  reread before selection.
- `global_goal`: active.

## Current boundary

No production Lean source exists for this campaign. Public preregistration CI is required before
implementation. The full curve theorem, number-field transfer, and RH remain open. The six
inherited user/exposure files remain untouched and unstaged.
