# H10 Bombieri--Stepanov Polar Injectivity

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H10-BOMBIERI-STEPANOV-POLAR-INJECTIVITY-01`

Selected node: `H10-E-BOMBIERI-STEPANOV-POLAR-INJECTIVITY-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

## Target

- `mode`: `LITERATURE / FALSIFICATION`.
- `exact_target`: formalize dimension-surplus kernel production, injective realization, and a
  separated coefficient-block model of Bombieri's polar noncancellation lemma.
- `relation_to_RH`: known function-field proof mechanism only. The actual curve valuation lemma,
  Riemann--Roch dimensions, point counts, number-field transfer, and RH remain open.
- `success`: generic kernel certificate, injective-realization theorem, block equivalence,
  source-shaped nonzero-kernel theorem, noninjective countermodel, and positive witness.
- `falsification`: any hidden use of injectivity, false dimension direction, or claim that the
  coefficient-block model is the actual curve theorem.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the H10 Frobenius/descent/multiplicity campaign. | Final ledger `b23d601ee8c69a654d542f1da43d16bb042eaf22` passed run `30205670028`, job `89803179330`, in `1m30s`. | Return to historical-route selection. |
| `CROSS_FAMILY_AUDIT` | Compared H1, H2, H7, H10, H11, and H12 at their latest compiled edges. | H1/H2/H7/H11/H12 next require direct open analytic or spectral inputs. H10 retains an adjacent unformalized hinge inside a successful proof. | Select the nonzero-production gate, not another point-count constant. |
| `PRIMARY_SOURCE_AUDIT` | Re-read Bombieri's key product-isomorphism lemma and Kedlaya's tensor/dimension presentation. | The source needs injective realization before dimension surplus yields a nonzero auxiliary. | Fix the positive logic and a countermodel without injectivity. |
| `API_SURVEY` | Checked finite-dimensional rank-nullity, `ker_ne_bot_of_finrank_lt`, polynomial `degreeLT`, coefficient equivalences, and finite `Pi` linear equivalences. | The fixed finite-dimensional and coefficient-block endpoints have a direct no-sorry Lean surface. | Publish docs-only preregistration before proof edits. |
| `PREREGISTRATION_PUBLIC` | Published docs-only commit `e4efd3e2c6a2c2cae983b1d3224a8780aaa88f1c`. | Public run `30205991741`, build job `89804024442`, passed in `2m15s`. | Open the fixed production gate. |
| `KERNEL_CERTIFICATE` | Applied finite-dimensional rank-nullity to an arbitrary descent map. | A strict source-target finrank surplus yields a nonzero vector with zero descent. | Test whether realization preserves nonzeroness. |
| `INJECTIVE_REALIZATION` | Added an arbitrary injective linear realization. | The nonzero kernel vector realizes to a nonzero target object. | Build a source-shaped noncancellation model. |
| `COEFFICIENT_BLOCK_EQUIV` | Reindexed `n` degree-`<q` coefficient blocks into one degree-`<n*q` polynomial. | The construction is a linear equivalence and exact block coefficients transport through it. | Combine it with the kernel certificate. |
| `SOURCE_SHAPED_ENDPOINT` | Used the block equivalence as the realization map. | Any descent target of finrank below `n*q` has a zero-descent block family with nonzero realized polynomial. | Run the negative control. |
| `NONINJECTIVE_CONTROL` | Set both descent and realization to the first projection on `Q x Q`. | The descent kernel contains `(0,1)`, but every kernel vector realizes to zero. | Record injectivity as indispensable. |
| `POSITIVE_WITNESS` | Realized the blocks `1` and `X` in width two. | Two exact output coefficients equal one, and the realized polynomial is nonzero. | Run all local gates. |
| `LOCAL_GATES` | Ran warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles; scanned forbidden declarations and resource relaxations; ran the full build. | One proven Target, six exact checks, six standard-only axiom prints, empty scans, and `8770/8770` build all pass. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC` | Published frozen implementation `011ce4d16bb565d03059ae220e9ad1996e6ec7cb`. | Public run `30206491939`, build job `89805380158`, passed in `2m25s`. | Keep `LeanLab/` frozen and publish immutable evidence. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; governance, external memory, parent
  closure, route census, ranked atlas, H10 route card, source registry, Bombieri, Kedlaya, and
  the pinned Lean API were checked before selection.
- `global_goal`: active.

## Current boundary

Local result: `SOURCE_NONCANCELLATION_GATE_FORMALIZED`.

The source's nonzero-production logic is valid when realization is injective and false without
that premise. This does not prove Bombieri's actual curve polar-order injection. A number-field
analogue would likewise need both an injective realization and a separately constructed
dimension-surplus descent map; no such map is supplied here. Riemann--Roch construction,
point counts, number-field transfer, and RH remain open. The six inherited user/exposure files
remain untouched and unstaged.

Frozen implementation: `011ce4d16bb565d03059ae220e9ad1996e6ec7cb`. No Lean proof-source
changes are permitted during immutable evidence and final-ledger publication.
