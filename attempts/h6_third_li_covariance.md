# H6 Third-Li Covariance Attempt

Campaign: `DISCOVERY-20260717-H6-THIRD-LI-COVARIANCE-01`

Mode: `DISCOVERY`

Status: `PUBLICLY_CLOSED`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: inherited compacted summary; canonical governance, HANDOFF, Targets,
  TargetChecks, hard-gap DAG, H6 source modules, and current route records reread from the clean
  public worktree
- `global_goal`: active

## Selection record

- `exact_target`: prove the exact theta-source covariance `B*C<=A*D`, the standard third heat-Li
  formula, its time-zero equality with `liCoefficientCandidate 2`, and strict positive real sign.
- `relation_to_RH`: one finite necessary Li condition; strictly below the all-index RH-equivalent
  criterion.
- `material_difference`: the failed positive-cosh branch used generic positivity only. This attack
  combines same-order covariance with the source-specific compiled time-zero bound `lambda1<1`.
- `nearest_attempt`: H6 first-two moment campaign and `OBS-H6-POSITIVE-COSH-LI3-01`.
- `nearest_sources`: Li 1997, Bombieri-Lagarias 1999, Polymath 2019, Coffey 2004, Maslanka 2004.
- `numerical_screen`: candidate selection only; approximate time-zero signs are positive through
  order three, and no sampled time in `[-100,100]` refuted the third sign.
- `assumption_frontier_before`: no theorem about the fourth theta moment, ordered covariance,
  third heat-Li formula, or `liCoefficientCandidate 2` sign is currently admitted.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open.

## Preregistration gate

- commit `6c1c8c0defb2186ef20701ae9e33ca6be95c4daa`
- public Lean Action CI run `29544246770`, build job `87772850526`, passed in `1m45s`
- no Lean proof source was edited before this public gate passed

## Formalized result

- `DeBruijnNewmanThirdLi.lean` defines the fourth source moment `D_t`, proves its integrability
  and strict positivity, and proves the exact spatial derivative factor `F_t'''(1)=64*D_t`.
- `deBruijnNewmanHeatLiMomentB_mul_C_le_A_mul_D` proves `B_t*C_t<=A_t*D_t` from the registered
  one-integral Chebyshev certificate with `X(u)=u*tanh(u)`, `Y(u)=u^2`, `m=C/A`, and
  `r=sqrt(m)`.
- `deBruijnNewmanHeatLiThree_eq` proves the exact normalized formula
  `6*b+12*(c-b^2)+4*d-12*b*c+8*b^3` for every real `t`.
- `liCoefficientCandidate_two_eq_third_li_expression` specializes the existing all-index finite
  Leibniz formula, and `deBruijnNewmanHeatLiThree_zero_eq_candidate_two` transports it through
  the compiled identity `deBruijnNewmanHeatXi 0=riemannXi`.
- `liCoefficientCandidate_two_re_pos` uses `B^2<=A*C`, `B*C<=A*D`, and the compiled exact bound
  `liCoefficientCandidate_zero_re_lt_one`. The normalized expression is rearranged as
  `6*b+(12-8*b)*(c-b^2)+4*(d-b*c)`, so no numerical estimate is a proof premise.
- `liCoefficientCandidate_two_im_eq_zero` proves the candidate is real.
- The fixed aggregate theorem is `deBruijnNewmanHeat_thirdLi_covariance_endpoint`.

## Mechanical audit

- standalone module: diagnostic-free
- exact `Targets.lean` and full-conjunction `TargetChecks.lean`: pass
- selected axiom prints: exactly `propext`, `Classical.choice`, and `Quot.sound`
- forbidden proof/declaration/resource-relaxation scans: empty
- `git diff --check`: pass
- full build: `8695` jobs, pass

## Public implementation evidence

- implementation commit `1b521686d4e8561f01ba98a6ceaa4905ced4d92f`
- public Lean Action CI run `29545583372`, build job `87777066173`, passed in `1m56s`
- evidence commit `abf5ebf19e3636662a45eed7a5eff9e947c3c3b4`
- public Lean Action CI run `29545784893`, build job `87777708775`, passed in `2m01s`

## Current result

- `result`: `DISCOVERY_FORMALIZED`
- `closure`: `PUBLICLY_CLOSED`
- `rh_frontier_delta`: 0
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `engineering_delta`: 0
- `proof_source_edits`: `LeanLab/Riemann/DeBruijnNewmanThirdLi.lean` plus exact registry/audit
  integration
