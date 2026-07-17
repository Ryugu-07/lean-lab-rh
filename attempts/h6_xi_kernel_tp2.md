# H6 Actual Xi-Kernel TP2

Campaign: `LITERATURE-20260717-H6-XI-KERNEL-TP2-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION_PENDING_PUBLIC_CI`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited continuation; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, H6 route card, current attempt logs, and the closed external
  log-concavity audit were reread before selection
- `global_goal`: active

## Selection record

- `exact_target`: prove the actual full-series strict log-concavity numerator `Q_Phi(u)<0` for
  every `u>=0`, together with both termwise derivative identifications
- `primary_source`: Csordas-Varga 1988, DOI `10.1007/BF02075457`, exact project normalization
- `secondary_source`: Coffey-Csordas 2013, DOI `10.1090/S0025-5718-2013-02681-6`
- `material_difference`: prove a nontrivial derivative inequality for the compiled theta kernel,
  rather than audit the vacuous 2026 Lean predicate or extend a finite heat-Li prefix
- `nearest_attempt`: the closed external Lean audit and H6-X4 all-index heat-Li criterion
- `assumption_frontier_before`: `Phi>0` and term summability are compiled; `Phi'`, `Phi''`, and
  every full-kernel TP2 inequality are absent
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open

## Pre-proof findings

- the exact TP2 theorem was already published in stronger form in 1988 and reproved in 2013
- the 2026 preprint is not a proof premise; its analytic tail step contains unproved global bounds
- project normalization matches the 1988 kernel exactly; the 2026 variable is scaled by a factor
  of two
- symbolic differentiation fixes derivative polynomials of degrees three and four in
  `y=pi*n^2*exp(4*u)`
- high-precision exploratory decimal evaluation found the normalized numerator negative on a
  broad grid from `u=0` through `u=2`; this is target selection only
- the decisive Lean risk is a quantitative infinite-tail bound, not pointwise differentiation

## Frozen stop rule

Do not report the first summand, a finite truncation, or termwise log-concavity as campaign
success. Full success requires the exact infinite `tsum` inequality. On failure, record the first
unproved source inequality as an OBS node and return the persistent Goal to route selection.
