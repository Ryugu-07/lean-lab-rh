# H9 Redheffer Characteristic Polynomial

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-REDHEFFER-CHARPOLY-01`

Selected node: `H9-REDHEFFER-CHARACTERISTIC-POLYNOMIAL-01`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Target

- `mode`: `LITERATURE / FALSIFICATION`.
- `exact_target`: compile Vaughan equations `(7)`--`(12)` through ordered-factor counts, a
  denominator-free polynomial row eliminator, the generic Redheffer characteristic polynomial,
  and exact algebraic multiplicity of eigenvalue one.
- `relation_to_RH`: this compresses the determinant product into logarithmically many non-unit
  roots but proves no estimate for those roots and no Mertens growth bound.
- `success`: generic source factorization, exact multiplicity, low-order sign checks, standard-
  only axiom audit, empty forbidden scans, full build, and public evidence gates.
- `falsification`: reject denominator cancellation at `lambda=1`, unordered counts, log-floor
  off-by-one errors, geometric-for-algebraic multiplicity substitution, and spectral-location
  conclusions not present in the factorization.

## Attempt log

| phase | action | result | next decision |
| --- | --- | --- | --- |
| `PARENT_PUBLIC_CLOSURE` | Closed the exact Redheffer--Mertens determinant endpoint. | Final ledger `6dfb8689243824598d865c911f64c46a0dc8de18` passed run `30208188470`, job `89809811907`, in `1m37s`. | Return to fresh cross-family route selection. |
| `CROSS_FAMILY_AUDIT` | Compared the adjacent H9 source edge with the current H0/H1/H2/H7/H8/H11/H12 frontiers. | The other candidates require new global analytic, spectral, or sparse-exception inputs; H9 has an exact unformalized structural transition. | Select the characteristic polynomial, not a new numerical bound. |
| `PRIMARY_SOURCE_AUDIT` | Checked Vaughan I equations `(7)`--`(12)` and Theorem 1. | The source uses ordered factor counts and a rational first-row transform; exact multiplicity requires retaining `lambda=1`. | Preregister a denominator-free polynomial reconstruction. |
| `REPOSITORY_DUPLICATION_SCAN` | Searched production and research files for Redheffer charpoly and ordered-factor objects. | Only the determinant module exists; no characteristic-polynomial theorem or factor-count recursion is present. | Admit the adjacent H9 node. |
| `LEAN_API_SURVEY` | Checked `Matrix.charpoly`, `Matrix.eval_charpoly`, polynomial determinant APIs, `Nat.log`, `pow_log_le_self`, and `lt_pow_succ_log_self`. | The exact finite polynomial endpoint has a no-sorry route with the log-floor boundary exposed. | Publish docs-only preregistration before proof edits. |

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `budget`: no numerical quota under V4.1.
- `compaction_state`: resumed from compacted live state, then rechecked governance, the current
  route ledgers, the public H9 parent closure, Vaughan equations `(7)`--`(12)`, repository
  duplication, and pinned Mathlib APIs.
- `global_goal`: active.

## Assumption frontier

The fixed endpoint may use only finite matrices, integer polynomials, finite divisor sums,
ordered-factor support, standard characteristic-polynomial identities, and the already compiled
Redheffer matrix. It may not assume RH, a Mertens growth estimate, any root-location estimate,
normality, self-adjointness, or the dominant-root asymptotics.

The parent determinant identity is public-green. The characteristic polynomial, exact unit-root
multiplicity, dominant-root estimates, remaining-root estimates, Mertens growth, H9, and RH are
open at launch. The six inherited user/exposure files remain untouched and unstaged.
