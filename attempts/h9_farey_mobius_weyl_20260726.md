# H9 Farey--Mobius--Weyl Transform

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-FAREY-MOBIUS-WEYL-01`

Selected node: `H9-FAREY-MOBIUS-WEYL-TRANSFORM-01`

Status: `PREREGISTRATION / PRODUCTION_GATE_CLOSED`

## Target

- `mode`: `LITERATURE`.
- `exact_target`: compile source-aligned reduced positive Farey pairs, their uniqueness and
  totient count, the exact finite Mertens transform for arbitrary complex test functions, and
  the frequency-one specialization equal to `finiteMertens`.
- `relation_to_RH`: Farey discrepancy estimates and Mertens square-root cancellation have
  RH-equivalent formulations. This campaign proves only the exact finite arithmetic transform
  that exposes the unresolved estimate.
- `success`: every fixed endpoint, M0 definition alignment, one aggregate Target, exact checks,
  standard-only axiom audit, full build, and all public evidence gates.
- `falsification`: reject wrong endpoint conventions, zero denominators, duplicate reduced
  values, missing `M(floor(N/n))`, detached root sums, or promotion of an exact identity to a
  discrepancy estimate or RH.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the H1 Hardy real critical-line xi/sign-consumer endpoint. | Final ledger `24567b9a7bd2baae902c83ffbb1b2281a676a074` passed run `30213706063`, job `89824117700`, in `1m50s`. | Return to fresh cross-family route selection. |
| `CROSS_FAMILY_AUDIT` | Compared Hardy's transform, Riesz decay/continuation, Redheffer estimates, H2 density, H7 spectral convergence, H10 function fields, H11 statistics, H12 Speiser, and Farey--Franel--Landau. | Farey is canonical, historically independent, entirely absent from production Lean, and has a bounded exact entry mechanism before its RH-strength estimates. | Select the Farey Mobius transform rather than optimizing a recent bound. |
| `PRIMARY_SOURCE_AUDIT` | Read Kanemitsu--Yoshimoto 1996 and retained Franel 1924 as the discrepancy anchor. | Source Lemma 3 gives an exact finite Farey-to-Mertens transform; the later square-root estimates, not the identity, carry RH strength. | Freeze the transform and frequency-one specialization while keeping discrepancy estimates open. |
| `REPOSITORY_DUPLICATION_SCAN` | Searched production Lean, route cards, attempts, and source registry. | Farey appears only as a queued historical family; no Farey pair, sum, transform, or discrepancy theorem exists. Existing `finiteMertens` supplies the exact target coefficient. | Admit a new H9 subroute. |
| `LEAN_API_SURVEY` | Checked finite interval/filter sums, rational arithmetic, Mobius inversion, divisor antidiagonals, geometric sums, and the existing one-based `finiteMertens`. | A no-sorry route is plausible; exact reindexing and root-of-unity syntax remain to be tested only after public preregistration CI. | Publish docs-only preregistration before proof edits. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; rechecked the protected worktree,
  Hardy's final public closure, the source convention and Lemma 3 endpoint, repository
  duplication, the existing one-based Mertens sum, and relevant Mathlib Mobius APIs.
- `global_goal`: active under the research protocol, notwithstanding client-side pause metadata.

## Assumption frontier

The unconditional endpoint may use only finite sums, rational arithmetic, standard Mobius
inversion, complex exponential periodicity, finite geometric sums, and the already compiled
definition of `finiteMertens`.

It may not assume any Farey discrepancy estimate, Mertens growth estimate, PNT, zero-free region,
RH-equivalent bound, RH, or an ordered Farey enumeration.

The six inherited user/exposure files remain untouched and unstaged.
