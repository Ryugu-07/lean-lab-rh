# H1 Hardy Critical-Line Sign Bridge

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H1-HARDY-CRITICAL-LINE-SIGN-01`

Selected node: `H1-HARDY-CRITICAL-LINE-REAL-SIGN-BRIDGE-01`

Status: `PUBLICLY_CLOSED`

## Target

- `mode`: `LITERATURE`.
- `exact_target`: compile the actual project-xi critical-line coordinate, real-valuedness,
  evenness, continuity, exact nontrivial-zero dictionary, both interval sign orientations, and
  an alternating-sequence interval-witness consumer.
- `relation_to_RH`: Hardy's historical theorem supplies infinitely many critical-line zeros,
  which is strict partial progress toward RH. This campaign formalizes its normalization and
  sign consumer only; it does not prove the sign changes or their infinitude.
- `success`: every fixed xi-specific endpoint, M0 definition alignment, one aggregate Target,
  exact TargetChecks, standard-only axiom audit, full build, and all public evidence gates.
- `falsification`: reject an abstract continuous-function substitute, assumed real-valuedness,
  assumed xi zeros, lost interval membership, hidden distinctness, or any promotion from
  real-valuedness to oscillation.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the H9 Riesz Mellin-boundary endpoint. | Final ledger `18110c4a553e710fcb67fbe5617562fc573eca45` passed run `30212583915`, job `89821224995`, in `1m31s`. | Return to fresh cross-family route selection. |
| `CROSS_FAMILY_AUDIT` | Compared H1 Hardy and mollifier edges, H2 bow exclusion, H7 ground-state convergence, H9 Farey and Riesz successors, H10 geometry, H11 sparse amplification, and H12 contour assembly. | The Hardy theorem is cited in the route card but its real critical-line xi/sign consumer is absent from production Lean. Farey is also missing but starts with a larger ordered-rational interface. | Select the bounded H1 historical entry node and queue Farey for later comparison. |
| `PRIMARY_SOURCE_AUDIT` | Located Hardy 1914 and the later Hardy--Littlewood full account. | The historical endpoint is infinitely many critical-line zeros; the first formal hinge is a real critical-line coordinate plus a theorem converting signs to actual zeros. | Keep infinitude and transform estimates outside this fixed endpoint. |
| `REPOSITORY_DUPLICATION_SCAN` | Searched production, attempts, route cards, and ledgers for Hardy xi, Hardy Z, or an xi sign-change theorem. | Production Lean has xi conjugation, functional equation, analyticity, and zero dictionaries, but no direct Hardy critical-line real/sign module. | Admit the new H1 subroute. |
| `LEAN_API_SURVEY` | Checked the existing xi symmetry and differentiability theorems and the real intermediate-value route. | The fixed endpoint has a direct no-sorry path; exact theorem syntax remains to be tested after the public preregistration gate. | Publish docs-only preregistration before proof edits. |
| `PUBLIC_PREREG_GATE` | Published the docs-only fixed endpoint. | Commit `fa9f7842d87263370e4c166553f130d6e3d3ca2d` passed run `30213072417`, job `89822480269`, in `1m47s`. | Open production editing. |
| `CRITICAL_LINE_GEOMETRY` | Defined the literal point `1/2+i*t` and proved its conjugate and negative-parameter identities. | Both identities normalize exactly to `s -> 1-s`, and every point satisfies project `OnCriticalLine`. | Transport the xi symmetries. |
| `REAL_EVEN_CONTINUOUS_XI` | Combined `riemannXi_conj`, `riemannXi_one_sub`, and entire continuity. | `hardyCriticalXi(t)=ofReal(hardyXi(t))`; `hardyXi` is even and continuous. Real-valuedness does not supply any sign. | Register the exact zero dictionary. |
| `ZERO_DICTIONARY` | Rewrote project xi zeros through the existing multiplicity-safe nontrivial-zero equivalence. | `hardyXi(t)=0` iff `IsNontrivialZero(1/2+i*t)` compiles, with critical-line membership proved separately. | Apply the real intermediate value theorem. |
| `SIGN_CONSUMERS` | Proved negative-to-positive and positive-to-negative weak endpoint versions and a disjunctive bracket theorem. | Each theorem returns an interval member together with actual `IsNontrivialZero` and `OnCriticalLine`; endpoint zeros are admitted. | Lift pointwise to a sequence. |
| `SEQUENCE_CONSUMER` | Applied the bracket theorem to every adjacent interval of an ordered alternating-sign sequence. | One actual witness compiles in each interval. No pairwise distinctness is claimed. | Register Target and audits. |
| `LOCAL_GATES` | Added one aggregate Target, five exact checks, and nine selected axiom prints; ran standalone, warning-as-error, forbidden, and full-build checks. | Selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`; new-module scan is empty; full build passes `8774/8774`. | Freeze and publish implementation. |
| `IMPLEMENTATION_PUBLIC_CI` | Froze and pushed the complete implementation and local ledgers. | Commit `98bf9927a8a331cd0da7541492cc4502c29e24ee` passed run `30213428759`, job `89823396107`, in `2m6s`. | Freeze all `LeanLab/` files and publish docs-only immutable evidence. |
| `IMMUTABLE_EVIDENCE_PUBLIC_CI` | Published docs-only proof-freeze evidence. | Commit `657b6dd3fa33e00d9c4f79ef3d4b64fa09b3d2de` passed run `30213562165`, job `89823746008`, in `2m22s`; the implementation-to-evidence `LeanLab/` diff is empty. | Publish one docs-only final ledger and require public CI. |
| `FINAL_LEDGER_PUBLIC_CI` | Published the docs-only final ledger. | Commit `24567b9a7bd2baae902c83ffbb1b2281a676a074` passed run `30213706063`, job `89824117700`, in `1m50s`. | Close only the fixed sign-consumer node and return to cross-family selection. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; rechecked the protected worktree,
  Riesz final public closure, H0--H14 route ledgers, repository duplication, primary-source
  anchors, and pinned project xi APIs before selection.
- `global_goal`: active.

## Assumption frontier

The unconditional endpoint may use only the existing project xi definition, its proved
functional equation and conjugation symmetry, entire differentiability/continuity, the proved
xi-zero/nontrivial-zero equivalence, complex-coordinate algebra, and the real intermediate value
theorem.

Endpoint sign inequalities are explicit arguments to the interval consumer. The campaign may not
assert that such signs exist at arbitrarily large heights, import Hardy's theorem as a premise,
assume RH, or infer oscillation from real-valuedness.

The six inherited user/exposure files remain untouched and unstaged.

## Local result

- `result`: `HARDY_CRITICAL_LINE_REAL_SIGN_BRIDGE_FORMALIZED`.
- `module`: `LeanLab/Riemann/HardyCriticalLineSign.lean`, 179 lines.
- `proved_boundary`: the actual project xi restriction is a real even continuous coordinate,
  and either weak sign orientation on an ordered interval produces a genuine nontrivial
  critical-line zero in that interval.
- `unproved_boundary`: no endpoint sign, transform estimate, zero distinctness, critical-line
  infinitude, H1, or RH is proved.
- `local_gates`: one proven Target, five exact TargetChecks, nine selected standard-only axiom
  prints, empty forbidden scan, warning-as-error compile, and full `8774/8774` build.
- `frozen_implementation`: `98bf9927a8a331cd0da7541492cc4502c29e24ee`, public-green.
- `immutable_evidence`: `657b6dd3fa33e00d9c4f79ef3d4b64fa09b3d2de`, public-green.
- `final_ledger`: `24567b9a7bd2baae902c83ffbb1b2281a676a074`, public-green.
- `next_gate`: none for this fixed node; Farey--Franel--Landau is selected by fresh
  cross-family route choice.
- `global_goal`: active.
