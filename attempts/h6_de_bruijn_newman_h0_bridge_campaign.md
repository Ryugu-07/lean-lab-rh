# H6 de Bruijn-Newman Time-Zero Bridge Campaign

Campaign: `CAMPAIGN-20260717-H6-H0-XI-BRIDGE-01`

Mode: `LITERATURE`

Status: `PUBLICLY_CLOSED`

## Runtime record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_state`: recovered from the V4.1/Census Batch A summary
- `global_goal`: active

## Target and prior state

- `exact_mathematical_statement`: the source-defined time-zero cosine transform satisfies
  `H_0(z) = (1/8) * riemannXi((1+i*z)/2)` for every complex `z`.
- `implemented_lean_statement`: `deBruijnNewmanH_zero_eq_riemannXi` in
  `LeanLab/Riemann/DeBruijnNewman.lean`.
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

## Implementation loop

- Defined the source-normalized theta tail, derivative terms, `deBruijnNewmanPhiTerm`,
  `deBruijnNewmanPhi`, and `deBruijnNewmanH` explicitly. The final theorem does not obtain the
  identity by defining `H` in terms of xi.
- Proved the termwise differential identity `F_n'' - F_n = 8 * Phi_n`, the derivative boundary
  sum at zero, double-exponential summability and integrability, termwise integration by parts,
  and the global theta-tail/Phi cosine-transform identity.
- Split the self-dual theta Mellin integral at one, transformed its lower half by `x -> 1/x`,
  changed variables by `x = exp (4*u)`, and converted the conjugate exponential pair on the
  critical line to the complex cosine transform.
- Compiled
  `completedRiemannZeta₀_critical_line_eq_thetaTailIntegral`, then combined it with the global
  integration-by-parts identity and the project's xi normalization to prove
  `deBruijnNewmanH_zero_eq_riemannXi`.
- The `z = 0`, factors-of-two/eight, xi reflection, and complex-cosine normalization checks are
  all consequences of the same exact theorem rather than numerical tests.

## Mechanical audit

- exact module compilation: passed without diagnostics
- `Targets.lean`: passed; `H6.debruijn-newman.h0-xi-bridge` is a proven target
- `TargetChecks.lean` exact witness: passed for the completed-zeta integral and final H0-xi bridge
- `AxiomsAudit.lean`: passed; all four new prints use only `propext`, `Classical.choice`, and
  `Quot.sound`
- forbidden token/declaration/resource scan: empty
- witness audit: exact theorem witness compiled; no weakened wrapper is registered
- definition/source alignment: explicit Polymath-normalized kernel and cosine transform compiled
- full `lake build`: passed locally, 8,683 jobs
- `git diff --check`: passed before documentation backfill and will be rerun before publication

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `assumption_frontier_after`: the source-defined `Phi` and `H_t` are now connected exactly to the
  project xi at `t = 0`; later H6 work may use this compiled bridge as a premise
- `hard_gap_after`: H6-H/H6-E (`Lambda <= 0` or all zeros of `H_0` real), W2/G7, M2/G3, and RH
  remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `OBS_node`: none; the preregistered theta-Mellin conversion obstacle is closed
- `theorem_names`: `integral_Ioi_deBruijnNewmanPhi_mul_cos`,
  `mellin_hurwitzEvenFEPair_zero_critical_line`,
  `completedRiemannZeta₀_critical_line_eq_thetaTailIntegral`,
  `deBruijnNewmanH_zero_eq_thetaTailIntegral`, `deBruijnNewmanH_zero_eq_riemannXi`
- `failure_or_obstacle`: no normalization mismatch; the next H6 obstruction is the heat-flow and
  all-real-zero theory, not the H0-xi definition bridge
- `route_selection_decision`: H6-B complete; fresh value-ranked route selection required after
  public closure
- `preregistration_commit`: `0eab341f1ad74b866fc942ccb9d89e77cbe51438`
- `preregistration_CI`: public Lean Action run `29493974202`, build job `87606471329`, passed in
  `1m55s` (`2026-07-16T11:19:01Z` to `2026-07-16T11:20:56Z`)
- `implementation_commit`: `b7824a3b3f3d206617f0a23b124959b6edad937d`
- `implementation_CI`: public Lean Action run `29500096845`, build job `87626587502`, passed in
  `2m37s` (`2026-07-16T12:56:04Z` to `2026-07-16T12:58:41Z`)
- `evidence_commit`: `8b9bd1c10000a518ff2f689a69f6431fba412281`
- `evidence_CI`: public Lean Action run `29500378390`, build job `87627536976`, passed in `1m28s`
  (`2026-07-16T13:00:17Z` to `2026-07-16T13:01:45Z`)
- `commit_and_CI`: preregistration, implementation, and immutable evidence backfill are public and
  independently built; campaign closed
