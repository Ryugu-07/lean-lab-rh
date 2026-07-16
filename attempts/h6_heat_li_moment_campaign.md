# H6 Heat-Li Moment Discovery Attempt

Campaign: `DISCOVERY-20260717-H6-HEAT-LI-MOMENTS-01`

Status: `PREREGISTERED_PUBLIC_CI_PENDING`

## Target

- `mode`: `DISCOVERY`
- `node_id`: H6-X below H6-E/G8
- `exact_mathematical_statement`: for every real heat time, express the first two source heat-Xi
  Li quantities by positive theta moments and prove both real parts strictly positive.
- `proposed_lean_statement`: `deBruijnNewmanHeatLi_first_two_re_pos (t : ℝ)` together with the
  exact moment formulas and `B_t^2 <= A_t*C_t` witness.
- `relation_to_RH`: finite necessary condition only; all-index positivity at time zero is
  RH-equivalent, but this campaign does not assume or claim it.
- `success_criterion`: all fixed clauses and machine/public gates pass.
- `falsification_criterion`: an exact factor/sign differs, the source moment inequality fails, or
  strict positivity cannot be obtained from the actual source weight.

## Route selection

- Re-read canonical governance, HANDOFF, Targets, the hard-gap DAG, H6 card, route atlas, and the
  just-closed adjacent-gap attempt from the clean synchronized worktree.
- Rejected another generic zero-repulsion loop because
  `OBS-H6-ADJACENT-GAP-EIGHT-01` is an exact sharpness countermodel.
- Deferred H6-Q because `Lambda<=1/5` remains strictly weaker than RH and needs a certified
  numerical stack not present in the repository.
- Found no materially new explicit M2 approximant or W2 global cancellation mechanism beyond the
  recorded projection, ladder, sparse-Gram, and prime-kernel obstructions.
- Selected the heat-Li moment attack because the source positive-cosh representation is absent
  from both generic H6 countermodels and is already supported by compiled all-time integrability,
  positivity, and spatial derivative infrastructure.
- Primary-source search found the Polymath heat family and general heat-deformation literature,
  but no exact first-two all-real-time moment theorem. No novelty claim is made.

## Fixed architecture

1. Define the exact heat-Xi coordinate and audit reflection, `t=0`, and the forward heat PDE.
2. Define `A_t`, `B_t`, and `C_t`; prove integrability, nonnegativity, and strict positivity where
   required.
3. Compile `F(1)=8*A`, `F'(1)=16*B`, and `F''(1)=32*C`.
4. Derive the exact first and second Li moment formulas through `logDeriv`.
5. Prove `B^2<=A*C` by an actual weighted Holder/Cauchy-Schwarz argument.
6. Close strict positivity, exact statement witnesses, axiom audit, forbidden scans, full build,
   logs, and public CI.

## Attempt log

Preregistration prepared. No Lean proof source has been edited.

## Accounting

- `assumption_frontier_before`: exact source `Phi>0`, all-time heat integrability, entire spatial
  family, two spatial derivatives, backward heat PDE, and generic log-derivative algebra.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH are open.
- `hard_gap_delta_expected`: 0.
- `route_infrastructure_delta_expected`: 1 only for the complete fixed endpoint.
- `nearest_project_attempt`: `OBS-H6-REVERSE-HEAT-LI-01` rejects generic backward Li transfer;
  this attempt adds the exact positive theta-transform premise rather than reusing that inference.

## Runtime record

- `model`: GPT-5 Codex (exact exposed runtime model identifier unavailable).
- `reasoning_effort`: not exposed.
- `budget`: no token budget.
- `compaction_state`: no new compaction detected after the public adjacent-gap evidence gate.
- `commit_and_CI`: pending preregistration publication.
