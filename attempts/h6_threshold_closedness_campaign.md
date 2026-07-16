# H6 Threshold Closedness Campaign

Campaign: `CAMPAIGN-20260717-H6-THRESHOLD-CLOSEDNESS-01`

Mode: `LITERATURE`

Status: `LOCAL_AUDITS_COMPLETE_PUBLIC_IMPLEMENTATION_CI_PENDING`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: resumed from the publicly closed H6 zero-coordinate framework; canonical
  governance, HANDOFF, Targets, DAG, H6 route card, and recent attempts reread
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`:
  `IsClosed {t : ℝ | deBruijnNewmanAllZerosReal t}`.
- `relation_to_RH`: H6-H2 threshold infrastructure; it changes no unconditional truth value of
  the time-zero RH-equivalent predicate.
- `success_criterion`: exact closedness plus every witness, trust, full-build, and public CI gate
  in `research/h6_threshold_closedness_prereg_20260717.md`.
- `falsification_criterion`: a fixed dependency of the Jensen persistence proof fails for the
  compiled source normalization.
- `assumption_frontier_before`: source family, entire spatial heat flow, exact all-real predicate,
  zero coordinate, strict time-zero strip, and RH equivalence are public.
- `hard_gap_before`: forward preservation, threshold existence/closedness, H6-E/G8, W2/G7,
  M2/G3, and RH open.
- `known_obstacle`: no packaged Rouche/Hurwitz theorem; joint parameter continuity and nonzero
  family witnesses are not yet public; Jensen inequalities must be assembled without assuming
  simple zeros.
- `nearest_primary_source`: Rodgers-Tao 2018 and D. H. J. Polymath 2019.
- `nearest_project_attempt`: the H6-H1 heat equation and H6-H2a zero-coordinate campaigns are
  publicly closed.
- `new_attack_angle`: derive full-multiplicity root persistence from the zero-free Jensen circle
  mean instead of formalizing the argument principle.

## Selection and preregistration loop

- Verified the supplied Sol V4 zip was already imported with V4.1 precedence; the Downloads and
  repository V4.1 directives are byte-identical.
- Compared forward real-zero preservation with threshold closedness.
- Audited mathlib for Rouche, Hurwitz, argument-principle, Laguerre-Polya, real-rooted polynomial,
  analytic isolated-zero, Jensen, and dominated parameter-integral support.
- Found no packaged root-persistence theorem, but found the exact zero-free Jensen mean identity.
- Fixed the seven-step proof architecture and exact `IsClosed` endpoint before proof-source edits.
- Preregistration commit `02758ff243c3f8cd434eb3c007a2a5f6b094fea7` passed public Lean Action CI
  run `29515723482`, build job `87680126242`, in `1m56s`.
- `result`: public preregistration complete; implementation active
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Lean implementation loop

- Proved every `deBruijnNewmanPhiTerm n u` is strictly positive for `u>=0`, then used summability
  and the positive zeroth term to prove `deBruijnNewmanPhi u>0`.
- Proved the real `z=0` integrand is integrable and positive on a positive-measure subset, yielding
  `Re(H_t(0))>0` and `H_t(0)!=0` for every real `t`.
- Applied dominated parameter convergence with the existing quadratic/linear source majorant to
  prove joint continuity of `(t,z) |-> H_t(z)`.
- On a zero-free circle, compactness supplies a positive minimum modulus. Joint continuity keeps
  the boundary modulus above half that minimum while the center value tends to zero.
- Assuming a nearby function is zero-free on the closed disk makes Jensen's logarithmic circle
  mean equal the center log norm, contradicting the boundary lower bound. This persists zeros of
  arbitrary multiplicity without a Rouche theorem.
- Analytic isolated zeros and `H_t(0)!=0` produce an isolating circle around each nonreal zero;
  shrinking inside `|Im(z0)|` keeps the entire closed ball off the real axis.
- The complement of the all-real-zero time set is therefore open, compiling the exact fixed
  `IsClosed` endpoint.
- `result`: `KNOWN_THEOREM_FORMALIZED` locally; public implementation CI pending
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 1
- `engineering_delta`: 1

## Mechanical audit

- exact module compilation: diagnostic-free
- `Targets.lean`: exact H6 threshold-closedness target compiles as proven
- `TargetChecks.lean`: positivity, nonvanishing, joint continuity, and exact closedness compile
- `AxiomsAudit.lean`: all four selected theorem prints use only `propext`, `Classical.choice`, and
  `Quot.sound`
- target/check/axiom build: passed locally, 8,684 jobs
- forbidden proof-token, declaration, and resource-relaxation scans: empty
- `git diff --check`: passed
- full local build: passed, 8,688 jobs
- public implementation CI: pending

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED` locally
- `assumption_frontier_after`: exact closedness of the all-real-zero time set is compiled
- `hard_gap_after`: forward preservation, threshold nonemptiness/upper-ray structure, H6-E/G8,
  W2/G7, M2/G3, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `OBS_node`: none yet
- `theorem_names`: `deBruijnNewmanPhi_pos`, `deBruijnNewmanH_zero_pos`,
  `deBruijnNewmanH_zero_ne_zero`, `continuous_deBruijnNewmanH_joint`,
  `isClosed_setOf_deBruijnNewmanAllZerosReal`
- `failure_or_obstacle`: none at the closedness endpoint; forward preservation is the next deeper
  source theorem and remains unproved
- `route_selection_decision`: publish the locally audited implementation and require public CI
  before immutable evidence closure
- `campaign_status`: active; persistent RH Goal remains active
