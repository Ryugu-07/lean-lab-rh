# H6 de Bruijn Upper-Half Campaign

Campaign: `CAMPAIGN-20260717-H6-UPPER-HALF-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION_LOCAL_READY_PUBLIC_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: resumed after public closure of H6-H2c; canonical governance, HANDOFF,
  Targets, the hard-gap DAG, H6 route card, source registry, and the completed forward campaign
  were reread from the repository
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: for `0 <= t <= 1/2`, every zero of `H_t` satisfies
  `Im(z)^2 <= 1-2*t`; hence every zero of `H_(1/2)` is real.
- `proposed_Lean_statements`: `deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul` and
  `deBruijnNewmanAllZerosReal_one_half`.
- `relation_to_RH`: proves the classical positive upper-time witness and threshold nonemptiness.
  It does not prove `deBruijnNewmanAllZerosReal 0`, which remains RH-equivalent.
- `success_criterion`: both exact endpoints plus every witness, trust, build, and public CI gate in
  `research/h6_upper_half_prereg_20260717.md`.
- `falsification_criterion`: the paired-factor contraction, multiplicity involution, factor of two,
  finite strip invariant, or limit persistence fails for the source normalization.
- `assumption_frontier_before`: exact source integral, order-one entire heat family, strict
  time-zero strip, closed good-time set, forward preservation, vertical averages, heat-multiplier
  convergence, and Jensen persistence are public.
- `hard_gap_before`: threshold nonemptiness/upper-time existence, H6-E/G8, W2/G7, M2/G3, and RH
  are open.
- `known_obstacle`: mathlib has no Laguerre-Polya or strip-preserver class. The multiplicity-bearing
  Hadamard divisor has no conjugation involution, and the prior product comparison applies only
  when every root is real.
- `nearest_primary_source`: de Bruijn 1950; Rodgers-Tao arXiv `1801.05914`; Branden-Chasse arXiv
  `1402.2795`.
- `nearest_project_attempt`: H6-H2c proves the zero-width vertical-average theorem and the exact
  heat limit. It cannot be applied at time zero because that would assume RH.
- `new_attack_angle`: generalize the compiled factor comparison from single real factors to
  conjugate factor pairs, carry a squared strip-width invariant through the existing finite
  `cosh` iteration, and reuse the already kernel-checked limit argument.

## Route-selection loop

- Re-read the canonical V4.1 governance and current project state after the H6-H2c closure.
- Compared direct H6-E, W2, and M2 re-entry, the numerical `0.22`/`0.2` frontier, threshold
  definition packaging, and the classical half-time theorem.
- Found no materially new unconditional positivity or approximation mechanism for the three
  direct hard gaps.
- Rejected threshold-definition packaging before nonemptiness as bookkeeping rather than the
  next mathematical frontier.
- Deferred `0.22` and `0.2`: both require substantially more effective and numerical
  certification infrastructure than the classical source theorem.
- Confirmed in Rodgers-Tao that the exact source normalization is all-real-zero for `t >= 1/2`.
- Confirmed in Branden-Chasse the shifted strip contraction by `a^2` and heat contraction by
  `2*t`, including the finite-order entire extension.
- Audited the compiled H6-H2c proof and found reusable order-one factorization, vertical-average
  iteration, scaled `cosh` limit, error majorant, and Jensen persistence.
- Identified the first genuinely new dependency as conjugate-pair comparison on the
  multiplicity-bearing Hadamard divisor.
- `result`: select H6-H2d; public preregistration gate pending.
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Current decision

- `route_selection_decision`: publicly preregister the fixed quantitative strip endpoint before
  any Lean proof-source edit.
- `campaign_status`: local preregistration ready; public preregistration CI pending; persistent RH
  Goal remains active.
