# H9 Redheffer Characteristic Polynomial

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H9-REDHEFFER-CHARPOLY-01`

Selected node: `H9-REDHEFFER-CHARACTERISTIC-POLYNOMIAL-01`

Status: `PUBLICLY_CLOSED`

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
| `PREREGISTRATION_PUBLIC` | Published docs-only commit `0b0654a53272104e64bfba6f18d36b9c362e1028`. | Public run `30208450587`, build job `89810511648`, passed in `1m59s`. | Open the fixed production gate. |
| `ORDERED_FACTOR_SUPPORT` | Defined `D_k(m)` recursively through proper divisors and proved its minimal-product support. | `D_k(m)=0` for `m<2^k`, all depth sums vanish above `floor(log_2 N)`, and `m=2^L` witnesses positivity at `L=floor(log_2 N)`. | Build the source row coefficients without an infinite series. |
| `DENOMINATOR_FREE_ELIMINATION` | Cleared powers of `lambda-1` before multiplying the characteristic matrix. | The polynomial eliminator has a proved determinant and cancels every nonfirst entry without assuming `lambda != 1`. | Take determinants over `Z[X]`. |
| `SOURCE_FACTORIZATION` | Combined the exact product and determinant identities. | Vaughan's reduced polynomial and the full characteristic-polynomial factorization compile for every positive matrix order. | Audit the root at one. |
| `UNIT_ROOT_MULTIPLICITY` | Proved the reduced factor is nonzero at one and computed root multiplicity. | For order `N>=2`, the multiplicity is exactly `N-floor(log_2 N)-1`. At `N=1`, it is one, so the unrestricted source formula has a genuine boundary exception. | Register both the generic theorem and the order-one correction. |
| `MERTENS_AND_LOW_ORDERS` | Evaluated the characteristic polynomial at zero and compiled orders one through four. | Evaluation gives `(-1)^N M(N)` with project indexing; the first four source polynomials fix the sign and indexing conventions. | Run all local gates. |
| `LOCAL_GATES` | Ran warning-as-error production, Targets, TargetChecks, and AxiomsAudit compiles; scanned forbidden declarations and resource relaxations; ran `git diff --check` and the full build. | One proven Target, eight exact checks, seven standard-only axiom prints, empty scans, and `8772/8772` build all pass. | Freeze and publish the implementation. |
| `IMPLEMENTATION_PUBLIC` | Published frozen implementation commit `4fbad00c4c24c8a5ae9b9885b0a23da82744665b`. | Public run `30209691871`, build job `89813735900`, passed in `2m24s`; the proof source is frozen. | Publish docs-only immutable evidence with no `LeanLab/` change. |
| `IMMUTABLE_EVIDENCE_PUBLIC` | Published docs-only evidence commit `ada5bb11085378fb8c1def1e3e9924a4a6b672a9`. | Public run `30209857664`, build job `89814144474`, passed in `1m47s`; the implementation-to-evidence `LeanLab/` diff is empty. | Publish the docs-only final ledger and require public CI. |
| `FINAL_LEDGER_PUBLIC` | Published final-ledger commit `2799ec66850919db744026ae58aaea4c2bd2f769`. | Public run `30210035283`, build job `89814585909`, passed in `1m37s`; the complete four-gate chain is public-green. | Close only the fixed endpoint and return to fresh route selection. |

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

The parent determinant identity is public-green. The characteristic polynomial and exact
unit-root multiplicity now compile locally, including the separate order-one source boundary.
Dominant-root estimates, remaining-root estimates, any joint non-unit-root product bound,
Mertens growth, H9, and RH remain open. The six inherited user/exposure files remain untouched
and unstaged.

Local result: `REDHEFFER_CHARACTERISTIC_POLYNOMIAL_FORMALIZED`, with
`historical_route_coverage_delta=1`, `spectral_compression_interface_delta=1`,
`unit_root_multiplicity_delta=1`, `source_boundary_correction_delta=1`,
`nonunit_root_location_delta=0`, `mertens_growth_delta=0`, `hard_gap_delta=0`, and
`rh_frontier_delta=0`.

Public closure: final-ledger commit `2799ec66850919db744026ae58aaea4c2bd2f769`,
run `30210035283`, job `89814585909`, in `1m37s`. The fixed endpoint is closed; every
non-unit-root estimate, Mertens growth, H9, and RH remain open.
