# H6 de Bruijn-Newman Time-Zero Bridge Campaign

Campaign: `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01`

Mode: `LITERATURE`

Status: `PUBLICLY_PREREGISTERED_IMPLEMENTATION_ACTIVE`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: recovered from the V4.1/Census Batch A summary
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: the source-defined time-zero cosine transform satisfies
  `H_0(z) = (1/8) * riemannXi((1+i*z)/2)` for every complex `z`.
- `proposed_lean_statement`: `deBruijnNewmanH_zero` in
  `research/h6_de_bruijn_newman_h0_bridge_prereg_20260717.md`.
- `relation_to_RH`: bridge; it changes no unconditional RH frontier.
- `success_criterion`: complete identity, exact witness, standard-only axiom audit, full build, and
  public CI.
- `falsification_criterion`: normalization mismatch or a precise unclosed theta-Mellin dependency.
- `assumption_frontier_before`: project xi/divisor/Hadamard infrastructure compiled; `Phi`, `H_t`,
  and the xi Fourier representation absent.
- `hard_gap_before`: H6 `Lambda <= 0`, W2/G7, M2/G3, and RH open.
- `known_obstacle`: mathlib identifies `completedRiemannZeta₀` with the entire Mellin transform of
  the self-dual theta kernel, but no current local theorem performs the remaining explicit-kernel
  conversion to the required `Phi` cosine transform.
- `nearest_primary_source`: D. H. J. Polymath, arXiv `1904.12438`.
- `nearest_project_attempt`: none; this is the first H6 source campaign.
- `new_attack_angle`: reuse the pinned project xi and current Jacobi-theta/Gaussian Fourier
  libraries instead of introducing an abstract heat family disconnected from RH.

## Preregistration loop

- Compared H6-B against direct W2/G7, M2/G3, H1-B, H2-B, and H6-Q.
- Selected H6-B because it is the exact gateway to a source-faithful H6 route and has a fixed,
  informative theta-Mellin failure boundary.
- Local inventory found Jacobi-theta and Gaussian/Poisson infrastructure but no xi integral bridge.
- A second audit located the exact upstream Mellin starting point:
  `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`, where `Λ₀` is definitionally
  `mellin (hurwitzEvenFEPair 0).f_modif`.
- The remaining proof chain is now localized to expanding `f_modif`, inserting the exact theta
  series, changing variables `x = exp (4*u)`, carrying out the required integration by parts, and
  evenizing the resulting Fourier integral into the source cosine transform.
- No Lean proof source was edited during this preregistration loop.
- `result`: `PUBLIC_PREREGISTRATION_COMPLETE`
- `rh_frontier_delta`: 0
- `route_infrastructure_delta`: 0
- `engineering_delta`: 0

## Mechanical audit

- exact module compilation: pending implementation
- `Targets.lean`: pending implementation
- `TargetChecks.lean` exact witness: pending implementation
- `AxiomsAudit.lean` and printed axioms: pending implementation
- forbidden token/declaration/resource scan: pending implementation
- witness audit: pending implementation
- definition/source alignment: fixed in preregistration; proof pending
- full `lake build`: pending implementation

## Result

- `result_class`: pending
- `assumption_frontier_after`: pending
- `hard_gap_after`: pending
- `OBS_node`: none yet
- `theorem_names`: none yet
- `failure_or_obstacle`: pending
- `route_selection_decision`: H6-B selected
- `preregistration_commit`: `0eab341f1ad74b866fc942ccb9d89e77cbe51438`
- `preregistration_CI`: public Lean Action run `29493974202`, build job `87606471329`, passed in
  `1m55s` (`2026-07-16T11:19:01Z` to `2026-07-16T11:20:56Z`)
- `commit_and_CI`: preregistration public; implementation pending
