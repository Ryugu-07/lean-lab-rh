# R5 Weil Finite Gaussian Test-Core Campaign

Campaign: `CAMPAIGN-20260716-R5-WEIL-FINITE-GAUSSIAN-TEST-CORE-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED_BRIDGE_REDUCED`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: yes; continued from the preserved task summary and
  repository/external-memory checkpoints

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | Rebuilt the frontier after public closure of the symmetric Gaussian probe family. R1/M2 remains parked by exact sparse-span and literature falsifications; R4's next edge is conjectural; R5/G6 still lacks a genuine test core, density, continuity, and regularization. | Audit a density-first continuation against smaller but compositional G6 edges. |
| 2 | `LITERATURE` | Arias de Reyna's Delsarte formula uses a finite Hermite-function core dense in Schwartz space and then extends by tempered-distribution continuity. Mathlib has Schwartz topology and Fourier automorphisms but no packaged Hermite completeness or compactly supported smooth density theorem. | Preserve full Schwartz density as a later indivisible campaign; reject L2 density as too weak. |
| 3 | `FALSIFICATION` | Fixed-width Gaussian-cosine density survived mathematical boundary checks, but immediate formalization requires several missing analysis edges. Finite complex packets survive empty, singleton, repeated-parameter, zero-coefficient, summability, and carrier checks, and directly create the algebraic core needed before closure. | Select and preregister the direct finite-packet explicit formula; begin Proof Attempt A. |
| 4 | `PROOF_ATTEMPT_A` | `WeilFiniteGaussianTestCore.lean` defines the directly synthesized packet weight, pole factor, GammaR integral, and von-Mangoldt family. Lean proves absolute zero and prime summability, direct finite `tsum` interchange, direct integrability and integral interchange, and the complete packet formula over every finite index type with complex coefficients. Independent singleton and empty-packet reductions compile. | The fixed endpoint is reached without statement shrinkage; run the complete verification gate. |
| 5 | `INDEPENDENT_AUDIT` | Rechecked direct rather than componentwise definitions, arbitrary finite types, complex coefficients, positive-width quantification, singleton/empty boundaries, and the absence of density, positivity, or RH claims. Standalone source, exact Targets and TargetChecks, six standard-only axiom prints, empty forbidden scans, `git diff --check`, and the 8,672-job full build pass. | Close locally as `BRIDGE_REDUCED`; publish implementation and require public CI. |
| 6 | `PUBLIC_IMPLEMENTATION_GATE` | Implementation commit `736901e03f08ccb399e4ec5f84980a641cb4e344` passed public Lean Action CI run `29445905312`, build job `87456185038`, in `2m33s`. | Backfill immutable evidence and require the evidence commit's own public CI. |
| 7 | `PUBLIC_EVIDENCE_GATE` | Evidence-backfill commit `6d7433b694b60150c19ca67f85087ba0e0c6255b` passed public Lean Action CI run `29446148141`, build job `87456989353`, in `1m26s`. | Close publicly as `BRIDGE_REDUCED`; keep the persistent RH Goal active and return to fresh route selection. |

## Accounting At Selection

- `classification_if_complete`: `BRIDGE_REDUCED`
- `hard_gap_before`: individually evaluated two-parameter probes
- `hard_gap_after`: complete direct explicit formula on their finite complex span
- `hard_gap_delta`: one algebraic test-core subedge of G6; zero for density, G7, and RH
- `unconditional_RH_progress`: none
- `forbidden_success`: an outer sum of old equalities, one interchange lemma, or L2-only density

## Local Result Before Verification

- `main_theorem`: `symmetricGaussianXiPacket_arithmetic_explicit_formula`
- `direct_zero_side`: `summable_riemannXiSymmetricGaussianPacketWeight` and exact packet `tsum`
- `direct_archimedean_side`: `integrable_symmetricGaussianXiPacketArchimedean` and exact integral
  interchange
- `direct_prime_side`: `summable_symmetricGaussianPacketVonMangoldtWeight` and exact packet `tsum`
- `boundary_checks`: independent singleton reduction to the predecessor theorem and exact empty
  packet reduction
- `axiom_audit_so_far`: only `propext`, `Classical.choice`, and `Quot.sound`
- `local_verification`: complete
- `full_build`: 8,672 jobs passed
- `implementation_ci`: run `29445905312`, job `87456185038`, passed in `2m33s`
- `evidence_ci`: run `29446148141`, job `87456989353`, passed in `1m26s`
- `remaining_gate`: none
