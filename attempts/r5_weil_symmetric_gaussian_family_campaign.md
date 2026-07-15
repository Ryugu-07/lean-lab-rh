# R5 Weil Symmetric Gaussian Translate-Family Campaign

Campaign: `CAMPAIGN-20260716-R5-WEIL-SYMMETRIC-GAUSSIAN-FAMILY-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

## Runtime Record

- `model`: Codex, GPT-5 family
- `reasoning_effort`: not exposed
- `loop_budget`: persistent Goal; no explicit per-loop token cap
- `compaction_since_previous_campaign`: no

## Loop Ledger

| Loop | Mode | Result | Decision |
|---|---|---|---|
| 1 | `ROUTE_MAP` | Rebuilt the frontier after public closure of the centered Gaussian formula. R1/R2's next positive edge is RH-hard, R3's Li criterion is complete, R4 lacks a spectrum bridge, and generic W1 remains open beyond one Gaussian. | Generate candidates across distributional, heat-flow, operator, Gram, and translated-test routes. |
| 2 | `CONJECTURE_GENERATION` | Screened the symmetric Gaussian translate family, Gaussian-Perron defect, prime quasicrystal temperedness, de Bruijn--Newman flow, screw operators, and renewed Gram estimates. | Send all six to carrier, strength, and boundary falsification. |
| 3 | `ADVERSARIAL_TEST` | Conditional localization, RH-equivalent temperedness, conjectural operator limits, and unsupported Gram residual bounds were excluded. Lean checked the translate family's reflection, `b` parity, `b=0`, both prime-transform centers, and absolute zero summability. | Select and preregister the full two-parameter explicit formula; begin Proof Attempt A. |
| 4 | `PROOF_ATTEMPT_A/ZERO_SIDE` | Factored out a generic selected-height rectangle theorem for analytic reflection-symmetric weights with summable zero values and a vanishing top edge. The new family satisfies the strip bound, absolute zero summability, and selected top-edge decay, hence its right edge tends to `pi` times the full multiplicity-bearing zero sum. | Continue to exact arithmetic evaluation; do not treat the generic skeleton alone as campaign success. |
| 5 | `PROOF_ATTEMPT_A/PRIME_SIDE` | Split `cosh` into two exponential branches. Lean evaluated each quadratic exponential exactly, proved individual and summed integrability, justified absolute sum/integral interchange, and recovered the average of kernels centered at `log(n)=b` and `log(n)=-b`. | Continue to pole and GammaR terms; both preregistered branches survived sign checks. |
| 6 | `PROOF_ATTEMPT_A/ASSEMBLY` | Proved the GammaR term integrable by bounded modulation, generalized the two-pole rectangle argument, computed both residues as `exp(a/4)*cosh(b/2)`, and spliced all selected truncation limits. The final theorem and its independent `b=0` compatibility theorem compile without placeholders. | Classify locally as `NEW_RELEVANT_LEAN_THEOREM`; run the full verification gate. |
| 7 | `VERIFICATION` | Standalone, Targets, TargetChecks, AxiomsAudit, empty placeholder/declaration scans, `git diff --check`, and the 8,671-job full build pass. Selected axiom prints contain only the three standard Lean/mathlib axioms. | Local verification complete; publish implementation and require public CI before campaign closure. |
| 8 | `PUBLIC_IMPLEMENTATION_GATE` | Implementation commit `5c4ae54c031a6d999111390694ef738a3da57146` passed public Lean Action CI run `29444276732`, build job `87450715956`, in `1m50s`. | Backfill immutable evidence and require that evidence commit's own public CI before closure. |

## Accounting At Selection

- `classification_if_complete`: `NEW_RELEVANT_LEAN_THEOREM`
- `hard_gap_before`: one centered Gaussian explicit formula
- `hard_gap_after`: one symmetric translated Gaussian probe family if the indivisible endpoint compiles
- `hard_gap_delta`: 1 parametric probe-family subedge; 0 for G6, G7, and RH
- `unconditional_RH_progress`: none
- `forbidden_success`: a bound-only helper, one transformed prime term, a fixed nonzero `b`, or a
  conditional localization theorem

## Local Result

- `classification`: `NEW_RELEVANT_LEAN_THEOREM`
- `main_theorem`: `symmetricGaussianXi_arithmetic_explicit_formula`
- `generic_bridge`: `tendsto_selectedXiRightVerticalIntegralFor`
- `zero_side`: absolute multiplicity-bearing `tsum` and selected-height right-edge limit
- `prime_side`: both exact translated kernels plus absolute summability and integral interchange
- `pole_side`: `2*pi*exp(a/4)*cosh(b/2)`
- `specialization`: exact `b=0` reduction to `gaussianXi_arithmetic_explicit_formula`
- `hard_gap_delta`: 1 parametric probe-family subedge; 0 for G6, G7, and RH
- `remaining_frontier`: Schwartz/Hermite density, tempered-distribution extension, generic local
  regularization, Weil positivity, and RH
