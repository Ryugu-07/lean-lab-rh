# H6 Heat-Li Moment Discovery Attempt

Campaign: `DISCOVERY-20260717-H6-HEAT-LI-MOMENTS-01`

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_CI_PENDING`

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

| Loop | State | Compiler-checked result | Decision |
| --- | --- | --- | --- |
| 0 | `PREREGISTRATION_GATE` | Preregistration commit `05b2b57e392ab53c0aeb9488cd7e31d28f9ff8f0` passed public Lean Action CI run `29539585856`, build job `87758769100`, from `2026-07-16T22:27:21Z` to `22:28:49Z`. | Open the fixed proof surface. |
| 1 | `MOMENT_INTEGRABILITY` | Defined the exact heat-Xi coordinate and moments `A/B/C`. Reused the complex heat integrability for `A/C`; dominated `B` by `A+C` using `sinh(u)<=cosh(u)` on the positive half-line. Proved all three moments strictly positive. | Continue to exact derivative normalization. |
| 2 | `DEFINITION_AND_DERIVATIVE_NORMALIZATION` | Proved the exact reflection `F_t(1-s)=F_t(s)`, time-zero identity `F_0=riemannXi`, Xi-coordinate heat equation `partial_t F=(1/4)*partial_s^2 F`, `H_t(-i)=A`, `H_t'(-i)=iB`, and the registered second moment equals `C`; the chain rule compiles `F_t(1)=8A`, `F_t'(1)=16B`, `F_t''(1)=32C`. | Admit definition alignment and derive logarithmic derivatives. |
| 3 | `LOG_DERIV_FORMULAS` | Proved `heatLiOne=2B/A` and `heatLiTwo=4*(A*B+A*C-B^2)/A^2`, carrying the compiled `A!=0` witness through both quotient derivatives. | Continue to the theta-specific inequality. |
| 4 | `WEIGHTED_CAUCHY_SCHWARZ` | With `W=exp(t*u^2)*Phi(u)*cosh(u)` and `X=u*tanh(u)`, defined `D=integral W*X^2`, proved `D<=C`, and expanded the nonnegative integral `integral W*(A*X-B)^2` to obtain `B^2<=A*D<=A*C`. | The fixed analytic obstacle is closed. |
| 5 | `FIXED_ENDPOINT` | Proved both Li quantities have zero imaginary part and strictly positive real part for every real `t`. Bundled every preregistered clause in `deBruijnNewmanHeat_firstTwoLi_endpoint`. | Run all local output gates. |
| 6 | `INDEPENDENT_LOCAL_AUDIT` | Standalone module, Targets, exact TargetChecks, seven selected axiom prints, placeholder/declaration/resource scans, and `git diff --check` pass. Every selected theorem uses only `propext`, `Classical.choice`, and `Quot.sound`; the full build passes with 8,693 jobs. | Publish the implementation and require exact public CI before evidence closure. |

## Accounting

- `assumption_frontier_before`: exact source `Phi>0`, all-time heat integrability, entire spatial
  family, two spatial derivatives, backward heat PDE, and generic log-derivative algebra.
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH are open.
- `assumption_frontier_after`: no new mathematical premise. The new reusable edge is the exact
  positive theta-moment representation and first-two all-real-time positivity.
- `hard_gap_delta`: 0. Finite first-two positivity does not imply the all-index Li criterion.
- `route_infrastructure_delta`: 1.
- `classification`: `DISCOVERY_FORMALIZED`; no novelty claim is made.
- `hard_gap_delta_expected`: 0.
- `route_infrastructure_delta_expected`: 1 only for the complete fixed endpoint.
- `nearest_project_attempt`: `OBS-H6-REVERSE-HEAT-LI-01` rejects generic backward Li transfer;
  this attempt adds the exact positive theta-transform premise rather than reusing that inference.

## Runtime record

- `model`: GPT-5 Codex (exact exposed runtime model identifier unavailable).
- `reasoning_effort`: not exposed.
- `budget`: no token budget.
- `compaction_state`: the implementation continuation began from a compacted thread summary;
  canonical files, clean git state, fixed endpoint, and the preregistration gate were rechecked
  before source edits.
- `preregistration_commit_and_CI`: commit `05b2b57e392ab53c0aeb9488cd7e31d28f9ff8f0`,
  run `29539585856`, job `87758769100`, success.
- `implementation_commit_and_CI`: commit `2bc304e9fe2473519c398269b26b0b06b715e593`,
  run `29541314279`, job `87763968249`, success in `2m19s`.

## Public implementation result

Implementation commit `2bc304e9fe2473519c398269b26b0b06b715e593` passed public Lean Action CI
run `29541314279`, build job `87763968249`, from `2026-07-16T23:05:13Z` to `23:07:32Z`
(`2m19s`). The independent runner rebuilt the definition-alignment theorems, complete first-two
endpoint, Targets, TargetChecks, and seven selected standard-only axiom prints.
