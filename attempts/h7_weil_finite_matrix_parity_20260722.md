# H7 Finite Weil Matrix and Parity Attempt

Campaign: `LITERATURE-20260722-H7-WEIL-FINITE-MATRIX-PARITY-01`

Mode: `LITERATURE`

Status: `LOCAL_IMPLEMENTATION_COMPLETE / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Runtime record

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: two inherited compactions. Governance, HANDOFF, Targets, TargetChecks, the
  current and closed H7 records, DAG, portfolio, external ACTIVE ledger, and git state were reread
  after each recovery.
- `global_goal`: active.

## Baseline

- `parent_commit`: `9ab3bf45101226f731b371a11ec06b149fa11a9a`.
- `baseline_public_ci`: run `29925232284`, build job `88940549581`, passed in `1m55s`.
- `selected_node`: `H7-WEIL-GROUNDSTATE-FINITE-MATRIX-01`.
- `preregistration`: `research/h7_weil_finite_matrix_parity_prereg_20260722.md`.

## Preregistered endpoint

Formalize the exact source divided-difference matrix and reflection parity split. Prove that
strict Rayleigh positivity on the even orthogonal complement of one normalized even eigenvector,
together with strict Rayleigh positivity on the whole odd block, makes that eigenvector the unique
global ground state. The theorem must expose an executable target for later exact or interval
certificates without assuming the source's unproved simple-even condition.

## Loop ledger

| loop | mode | result | decision |
| --- | --- | --- | --- |
| 1 | `RECOVERY / SOURCE_AND_CERTIFICATE_AUDIT` | Recovered the public H7 M0 frontier. Re-read the 2025 divided-difference, reflection, commutator, and even-simple definitions; audited the July 2026 matrix code, Arb inertia certificate, finite-height errata, and even-sector eigenflow. | Existing evidence neither proves nor falsifies simple-even. Select an exact finite matrix/parity checker as a separate literature campaign. |
| 2 | `PREREGISTRATION` | Fixed the source matrix, parity decomposition, strict two-block Rayleigh certificate, numerical-evidence boundary, and local stopping rule. No Lean proof source was edited. | Publish preregistration alone and require public CI before implementation. |
| 3 | `LITERATURE / LEAN_IMPLEMENTATION` | Lean compiled the exact centered source matrix, transpose and reflection symmetry, source rank-two commutator, reflection commutation, parity preservation, orthogonal decomposition, and quadratic split. The strict two-block Rayleigh certificate proves global minimality and equality/eigenspace exactly on the candidate line. | The fixed implementation endpoint is reached without assuming arithmetic simple-even. Run independent local audits. |
| 4 | `DISCOVERY / FALSIFICATION_SCREEN` | A numerical probe found mixed off-diagonal signs and tested checkerboard positivity of the inverse. High precision rejects the universal inverse-sign conjecture at `(2,8)`, `(3,8)`, `(5,8)`, and `(7,6)`. A source search found four June 2026 S3 preprints already pursuing Perron, Loewner, parity, and Herglotz reductions. | Do not open an original Perron campaign. Register the human scalar Herglotz frontier; numerical failures remain navigation only. |
| 5 | `INDEPENDENT_LOCAL_AUDIT` | The 556-line module, Targets, nine exact TargetChecks, nine selected standard-only axiom prints, empty forbidden scans, `git diff --check`, and the full 8,738-job build pass. | Classify as a finite certificate interface with no RH or hard-gap delta. Publish implementation and require public CI. |

## Compiled theorem inventory

- `weilFiniteCenteredFrequency_rev`
- `weilFiniteDividedDifferenceMatrix_transpose`
- `weilFiniteDividedDifferenceMatrix_reflection`
- `weilFiniteDividedDifferenceMatrix_commutator`
- `weilFiniteMatrix_mulVec_reflect`
- `weilFiniteQuadratic_split`
- `WeilFiniteParityRayleighCertificate.defect_nonneg_and_eq_smul`
- `WeilFiniteParityRayleighCertificate.evenSimpleGroundState`
- `weilFiniteDividedDifferenceMatrix_evenSimple_of_parityRayleigh`

The selected declarations use only the accepted Lean/mathlib trust base. No arithmetic strict
Rayleigh premise is proved or imported.

## Historical omission audit outcome

The initially considered Perron mechanism is already an active human route. The newly registered
S3 sources claim that removing the rank-two pole term gives a positivity-improving operator with
a simple even ground state, while adding the pole term reduces the remaining ordering problem to
one scalar odd-sector resolvent inequality. The exact open candidate is
`H7-WEIL-GROUNDSTATE-HERGLOTZ-01`: align and formalize the finite Herglotz/Schur-complement
criterion, then seek a proof or theorem-producing counterexample for the arithmetic matrices.

The numerical checkerboard-inverse idea is not universal and is not admitted to the conjecture
pool. It neither proves nor disproves simple-even structure.

## Assumption and gap accounting

- `assumption_frontier_before`: source matrix structure is published, while simple-even is an
  explicit missing assumption and no project theorem checks it.
- `hard_gap_before`: uniform simple-even ground-state structure and the actual
  `xi_lambda -> k_lambda` comparison are open.
- `rh_frontier_before`: RH open.
- `current_result`: `KNOWN_SOURCE_STRUCTURE_FORMALIZED / FINITE_CERTIFICATE_INTERFACE`.
- `hard_gap_delta`: `0`.
- `rh_frontier_delta`: `0`.
- `route_infrastructure_delta`: `1`.
- `obstruction_map_delta`: `1`.
- `next_gate`: implementation commit and public CI, then immutable evidence backfill and closure.
- `next_route_candidate`: `H7-WEIL-GROUNDSTATE-HERGLOTZ-01`, subject to fresh route selection
  after this campaign is publicly closed.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.
