# H9 Redheffer--Mertens Determinant

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-REDHEFFER-MERTENS-DETERMINANT-01`

Selected node: `H9-REDHEFFER-MERTENS-DETERMINANT-01`

Status: `PUBLICLY_CLOSED`

## Target

- `mode`: `LITERATURE / FALSIFICATION`.
- `exact_target`: compile Vaughan's integer Mobius row elimination, the exact Redheffer product
  form, the unit complementary determinant, `det A_n=M(n)`, and determinant-zero criteria.
- `relation_to_RH`: the later bound `M(n)=O(n^(1/2+epsilon))` is equivalent to RH. It is not a
  premise or result of this campaign.
- `success`: the generic determinant theorem, exact low-order checks, standard-only axiom audit,
  empty forbidden scans, full build, and public evidence gates.
- `falsification`: reject index-zero leakage, divisor-orientation errors, the false Mertens
  conjecture, or any inference from determinant product to individual eigenvalue location.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the H10 polar-injectivity finite-dimensional gate. | Final ledger `76c21bb536ad205b53eb8aee2035c2529e32eb96` passed run `30206809306`, job `89806209072`, in `1m33s`. | Return to cross-family historical route selection. |
| `CROSS_FAMILY_AUDIT` | Compared H0, H2, H8, H9, and the current H1/H7/H11/H12 frontiers. | H2/H8/H11 and the current H1/H7/H12 edges need new global inputs. H0 has truncated-Perron and exact explicit-formula support. The Redheffer branch is absent. | Select the missing H9 arithmetic-spectral interface. |
| `PRIMARY_SOURCE_AUDIT` | Read Vaughan I equations `(3)`--`(12)`, Barrett--Jarvis, and Vaughan II. | The determinant is obtained by exact Mobius row elimination; the later route concentrates the Mertens product in logarithmically many non-unit roots. | Fix the source elimination before auditing the characteristic polynomial. |
| `REPOSITORY_DUPLICATION_SCAN` | Searched `research/` and `LeanLab/Riemann/` for Redheffer and summatory-Mobius matrix objects. | No Redheffer definition, determinant identity, or dedicated route card exists. | Admit a new H9 historical subroute. |
| `LEAN_API_SURVEY` | Checked Mathlib's arithmetic-function Mobius API, determinant multiplication, row updates, Laplace expansion, and triangular determinant support. | The fixed finite integer endpoint has a direct no-sorry Lean surface. | Publish docs-only preregistration before proof edits. |
| `PREREGISTRATION_PUBLIC` | Published docs-only commit `1b535d265bdd186bbcd1e5e5c67cf69b441259f2`. | Public run `30207301448`, build job `89807491114`, passed in `2m11s`. | Open the fixed production gate. |
| `POSITIVE_INDEX_BIJECTION` | Reindexed `Fin N` by `k |-> k+1` onto the positive divisors of each column index. | The finite matrix sum is exactly Mathlib's divisor sum and never evaluates `mu(0)`. | Apply Mobius convolution. |
| `FIRST_ROW_ELIMINATION` | Multiplied Vaughan's first-row Mobius matrix by the Redheffer matrix. | The first pivot is `M(N)` and every other entry in that row is zero. | Audit the complementary determinant. |
| `TAIL_TRIANGULARITY` | Removed the first row and column and inspected the successor divisibility block. | A larger positive integer cannot divide a smaller one, so the block is unit upper triangular and has determinant one. | Expand the eliminated determinant. |
| `MERTENS_DETERMINANT` | Combined determinant multiplicativity, the first-row expansion, and the unit tail. | `det A_N=M(N)` compiles for every positive order, with exact zero/nonzero criteria. | Run low-order orientation checks. |
| `LOW_ORDER_CHECKS` | Checked orders one through four. | Determinants are `1,0,-1,-1`, matching the finite Mertens sums. | Run all local gates. |
| `LOCAL_GATES` | Ran warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles; scanned forbidden declarations and resource relaxations; ran the full build. | One proven Target, eight exact checks, six standard-only axiom prints, empty scans, and `8771/8771` build all pass. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC` | Published frozen implementation commit `2003f912dfb0627b1c41d4b80db1abc6eb24e5d3`. | Public run `30207909320`, build job `89809080863`, passed in `2m6s`; the proof source is frozen. | Publish docs-only immutable evidence with no `LeanLab/` change. |
| `IMMUTABLE_EVIDENCE_PUBLIC` | Published docs-only evidence commit `ad5444b8948eab6ac2cf2dd60f0a0e2fb7f85975`. | Public run `30208079452`, build job `89809518957`, passed in `1m29s`; the implementation-to-evidence `LeanLab/` diff is empty. | Publish the docs-only final ledger and require public CI. |
| `FINAL_LEDGER_PUBLIC` | Published final-ledger commit `6dfb8689243824598d865c911f64c46a0dc8de18`. | Public run `30208188470`, build job `89809811907`, passed in `1m37s`; the fixed determinant endpoint is fully public-green. | Close only this endpoint and return to route selection. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from a compacted live state; governance, `HANDOFF.md`, the route
  census, ranked atlas, current H10 closure, source registry, Vaughan I/II, Barrett--Jarvis, and
  the pinned Lean APIs were checked before selection.
- `global_goal`: active.

## Assumption frontier

The fixed determinant theorem may use only finite integer matrices, ordinary finite sums,
Mathlib's Mobius divisor-cancellation theorem, and standard determinant identities. It may not
assume RH, the RH-equivalent Mertens growth estimate, the false Mertens conjecture, or any
unproved spectral-location claim.

Public implementation result: `REDHEFFER_MERTENS_ELIMINATION_FORMALIZED`.

The characteristic polynomial, the exact multiplicity of eigenvalue one, the two dominant-root
asymptotics, estimates for the remaining roots, reciprocal-zeta continuation, H9, and RH remain
open after this first campaign. The compiled determinant identity is an exact arithmetic-spectral
interface, not a Mertens growth estimate. The six inherited user/exposure files remain untouched
and unstaged.
