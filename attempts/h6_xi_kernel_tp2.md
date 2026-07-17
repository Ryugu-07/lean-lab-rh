# H6 Actual Xi-Kernel TP2

Campaign: `LITERATURE-20260717-H6-XI-KERNEL-TP2-01`

Mode: `LITERATURE`

Status: `CLOSED_SUCCESS`

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

## Lean proof record

Module: `LeanLab/Riemann/XiKernelStrictLogConcavity.lean`

Compiled endpoints:

- `hasDerivAt_deBruijnNewmanPhi`: the explicit first-derivative `tsum` is the derivative of the
  actual source kernel at every real point;
- `hasDerivAt_deBruijnNewmanPhiDeriv`: the explicit second-derivative `tsum` is the derivative of
  the first derivative at every real point;
- `deBruijnNewmanPhiSecond_mul_phi_sub_deriv_sq_neg`: the complete full-series numerator is
  strictly negative for every `u>=0`.

The successful route was not the paper's three-range estimate. Each positive summand `a_n` was
given an exact logarithmic slope `s_n` and strictly negative logarithmic curvature `c_n`. For each
finite prefix Lean proves the weighted identity bound

```text
A*C-B^2 <= A*(a_0*c_0 + sum_(n>0) a_n*(s_n-s_0)^2).
```

The relative weights and slope differences satisfy exact first-term bounds. With
`Y=pi*exp(4*u)`, `m=n+1`, `m<=2^n`, `m^2-1>=3n`, `exp(-Y)<1/20`, and
`Y*exp(-3Y)<63/160000`, the normalized Gaussian variance tail is bounded by the geometric sum
`63/605<1/8`. This yields a tail `<16Y`, while `-c_0=16Y+96Y/(2Y-3)^2>16Y`. Hence every finite
prefix has one uniform negative upper bound; convergence of the three series transfers the bound
to the exact `tsum` numerator.

Failed or rejected subroutes retained for future avoidance:

- first-summand or termwise strict log-concavity alone cannot control the positive weighted
  variance between different logarithmic slopes;
- a finite-prefix numerical check cannot discharge the omitted infinite tail;
- the 2026 preprint's qualitative phrases about negligible tails and improving bounds are not
  usable as Lean premises;
- reconstructing the 1988 three-interval proof was unnecessary once the uniform first-term tail
  estimate closed globally on `u>=0`.

## Verification and classification

- preregistration: commit `36bad715a056e1c626b3ccc8fefae458ddec4110`, public CI run
  `29552030474`, job `87796448768`;
- implementation: commit `1c0c21076d8752c1c9fd623198fb2434fe6cc453`, public CI run
  `29560492371`, job `87821686793`, passed in `2m51s`;
- standalone new-module compile: diagnostic-free;
- exact `Targets`, `TargetChecks`, and `AxiomsAudit`: pass;
- selected transitive axioms: `[propext, Classical.choice, Quot.sound]` only;
- forbidden-token/declaration/resource-relaxation scan: empty;
- full build: 8,698 jobs, success.

Result: `KNOWN_THEOREM_FORMALIZED`. `hard_gap_delta=0`; `route_infrastructure_delta=1`.
Strict TP2 is now a compiled theta-kernel shape asset, but TP-infinity, H6-E/G8, and RH are not
proved by it. The global RH Goal remains active and returns to value-ranked route selection.
