# H9 Farey--Mobius--Weyl Transform

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-FAREY-MOBIUS-WEYL-01`

Selected node: `H9-FAREY-MOBIUS-WEYL-TRANSFORM-01`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

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
| `PUBLIC_PREREG_GATE` | Published the docs-only fixed endpoint. | Commit `2829a845aad703992bc99b0f0e73f93b7c83ddfe` passed run `30214114568`, job `89825172204`, in `1m29s`. | Open production editing. |
| `PAIR_NORMALIZATION` | Defined positive reduced `(denominator,numerator)` pairs and proved exact source membership. | `0/1` is excluded, `1/1` is included exactly once, reduced rational values are injective, and cardinality is the source sum of totients. | Decompose complete blocks by reduced denominator. |
| `REDUCTION_BIJECTION` | Sent every `1<=a<=q` to `(q/gcd(a,q),a/gcd(a,q))` and constructed the inverse. | Lean verifies the finite sum has no omission or duplicate and equals the divisor sum of reduced blocks. | Apply Mobius inversion. |
| `MOBIUS_AND_GLOBAL_REINDEX` | Applied Mathlib Mobius inversion at fixed denominator, then compiled the finite divisor-antidiagonal to `(n,d)` reindexing. | The actual arbitrary-test Farey sum equals `sum_{n<=N} M(floor(N/n))*V_f(n)`. | Specialize the exponential test. |
| `FREQUENCY_ONE` | Proved the complete root sums, primitive block identity, and total specialization. | Complete blocks vanish for `n>1`; the primitive `q` block is `mu(q)` and the total is `finiteMertens(N)`. | Register Target and audits. |
| `LOCAL_GATES` | Added one aggregate Target, eight exact checks, and nine selected axiom prints; ran standalone, warning-as-error, forbidden, and full-build checks. | Selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`; new-module scan is empty; full build passes `8775/8775`. | Freeze and publish implementation. |
| `IMPLEMENTATION_PUBLIC_CI` | Froze and pushed the complete implementation and local ledgers. | Commit `10bbaa1825bac871d5664322f85ab04f6668ec20` passed run `30214982286`, job `89827558524`, in `2m7s`. | Freeze all `LeanLab/` files and publish docs-only immutable evidence. |

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

## Local result

- `result`: `FAREY_MOBIUS_WEYL_TRANSFORM_FORMALIZED`.
- `module`: `LeanLab/Riemann/FareyMobiusWeyl.lean`, 579 lines.
- `proved_boundary`: source-aligned pair normalization, reduced-value injectivity, totient
  cardinality, complete-to-reduced divisor decomposition, exact Mobius inversion, the generic
  finite Mertens transform, primitive frequency-one `mu(q)`, and total frequency-one `M(N)`.
- `unproved_boundary`: no ordered Farey enumeration, Franel discrepancy formula, discrepancy
  estimate, equidistribution rate, Mertens growth, H9, or RH.
- `local_gates`: one proven Target, eight exact TargetChecks, nine selected standard-only axiom
  prints, empty forbidden scan, warning-as-error compile, and full `8775/8775` build.
- `classification`: `historical_route_coverage_delta=1`, `farey_normalization_delta=1`,
  `farey_mertens_transform_delta=1`, `farey_discrepancy_delta=0`,
  `mertens_growth_delta=0`, `hard_gap_delta=0`, `rh_frontier_delta=0`.
- `frozen_implementation`: `10bbaa1825bac871d5664322f85ab04f6668ec20`,
  public-green.
- `next_gate`: docs-only immutable evidence and public Lean Action CI.
- `global_goal`: active.
