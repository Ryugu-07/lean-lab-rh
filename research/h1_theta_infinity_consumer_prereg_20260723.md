# H1 Theta-Infinity Consumer Preregistration

Date: 2026-07-23

Campaign: `LITERATURE-20260723-H1-THETA-INFINITY-CONSUMER-01`

Selected node: `H1-FARMER-BETTIN-GONEK-THETA-INFINITY-01`

Status: `PREREGISTRATION_CI_PASSED / PROOF_SOURCE_GATE_OPEN`

## Baseline

- `parent_commit`: `5e36c53da657b4018f23339d4744562da07002ba`.
- `parent_public_ci`: Lean Action run `29965855724`, build job `89077075898`, passed in `1m51s`.
- `route_selection`: `research/route_selection_post_h7_20260723.md`.
- `nearest_attempt`: `LITERATURE-20260722-H1-SHORT-MOLLIFIER-VARIATIONAL-01`.
- `material_difference`: the earlier campaign certified a 2025 finite variational optimization;
  this campaign reconstructs the 1993/2017 arbitrary-length mechanism that excludes individual
  off-line zeros and tends directly to RH.
- `global_goal`: active.

## Locked sources

1. Bettin--Gonek, arXiv:1604.02740, Theorems 1 and 2 and equations `(1.1)`, `(2.1)`--`(2.5)`.
   <https://arxiv.org/abs/1604.02740>
2. Farmer, Mathematika 40 (1993), 71--87.
   <https://doi.org/10.1112/S0025579300013723>
3. Radziwill, arXiv:1207.6583.
   <https://arxiv.org/abs/1207.6583>
4. Conrey et al., arXiv:2508.11108, introduction.
   <https://arxiv.org/abs/2508.11108>

## Exact source objects

For real `x > 1`, complex `s`, and the arithmetic Mobius function, align

```text
M_x(s) = sum_(1 <= n <= x) mu(n) * n^(-s) * log(x/n) / log x,
M_1(s) = 0,
I_x(T1,T2) = integral_[T1,T2]
  |M_x(1/2 + i*t) * zeta(1/2 + i*t)|^2 dt.
```

The project statement must retain the logarithmic taper, normalization by `log x`, real cutoff,
critical-line shift, zeta factor, squared complex norm, and interval endpoints. A generic Dirichlet
polynomial may support the interpolation proof but cannot replace the source definitions.

## Fixed Lean endpoint

Only after this preregistration passes public CI, create a production module and compile without
placeholders or resource relaxation:

1. Define the source-shaped logarithmically tapered mollifier at natural and real cutoffs and the
   source mollified second moment.
2. Prove endpoint simplifications, including the vanishing new coefficient at an integer cutoff.
3. For `2 <= N` and `N <= x <= N+1`, prove the exact affine interpolation of `M_x(s)` between
   `M_N(s)` and `M_(N+1)(s)` in the coordinate `1/log x`.
4. Prove the interpolation coefficient lies in `[0,1]`, then prove the pointwise convex squared-norm
   bound after multiplication by an arbitrary complex factor. If the source integrability API is
   available without weakening, lift it to a moment bound on a finite interval.
5. Define the exact final power-obstruction predicate corresponding to
   `T^(2*beta*theta) <<_epsilon T^(1+epsilon+theta)` and prove that it forces
   `beta <= 1/2 + 1/(2*theta)` for `theta > 0`.
6. Prove a fixed-`theta` zero-free consumer from the power obstruction for every nontrivial zeta
   zero, and prove the all-positive-`theta` consumer gives `Mathlib.RiemannHypothesis` using the
   functional-equation reflection of nontrivial zeros.
7. Prove a finite algebraic witness that one fixed `theta` boundary still permits a point strictly
   off the critical line, so fixed-length quasi-RH is not mislabeled RH.
8. Register proven generic/source-consumer Targets, leave the actual moment-to-power bridge and
   Farmer `theta=infinity` conjecture open with no `leanName`, and add exact TargetChecks and
   selected axiom prints.

Names may change to fit Mathlib APIs. The logarithmic taper, real-cutoff interpolation coordinate,
source exponent `2*beta*theta` versus `1+epsilon+theta`, and boundary
`1/2+1/(2*theta)` may not be weakened.

## Unavailable analytic bridge

The campaign does not assume or prove that the source moment hypothesis yields the power
obstruction. That published analytic step contains Mellin inversion, construction and decay of
`G_t`, contour shifting, a residue at the selected zero, Cauchy--Schwarz, the critical-line zeta
second-moment lower bound, and uniform constant bookkeeping. It remains an open Target and may not
be used as a premise in later unconditional work until separately compiled.

The Farmer `theta=infinity` moment conjecture is also open and may never be used as a premise.
Conditional consumer theorems must display every assumption and must not be reported as progress
on the unconditional RH frontier.

## Success and falsification criteria

- `FULL_SUCCESS_AT_CONSUMER_ENDPOINT`: exact source objects, real-cutoff interpolation, convex
  bound, exponent barrier, fixed-`theta` zero-free consumer, all-`theta` RH consumer, and the
  fixed-`theta` countermodel all compile and pass every gate.
- `MEANINGFUL_PARTIAL`: source definitions, interpolation, and exponent barrier compile, but a
  precise existing Mathlib integration or functional-equation API blocks one registered consumer.
- `SOURCE_QUANTIFIER_GAP`: integer cutoff bounds do not control real cutoffs under the exact source
  normalization; record the counterexample or missing endpoint condition.
- `NO_PROGRESS`: the exact logarithmic taper or source exponent cannot be represented without a
  materially different object.

No outcome proves the moment-to-power bridge, Farmer's conjecture, or RH.

## Mechanical gates

Publish this preregistration, route selection, and H7 final public coordinates first. Require public
Lean Action CI before any production proof-source edit. Keep the six inherited protected files
untouched and unstaged.

Before theorem acceptance, require exact Targets and TargetChecks, selected transitive axiom
prints, an empty production forbidden scan, direct compiles, `git diff --check`, full build, and
independent public CI.

## Stop and successor rule

Stop at one registered outcome. On consumer success, select between a direct formalization of the
Bettin--Gonek Mellin/residue bridge `(2.2)`--`(2.5)` and another value-ranked historical mechanism.
Do not spend the successor campaign optimizing a critical-line percentage. Persistent RH Goal
remains active; original conjectures and direct attacks remain open.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant not exposed.
- `reasoning_effort`: not exposed.
- `loop_budget`: no numerical quota under V4.1; serving token budget not exposed.
- `compaction_state`: inherited-summary recovery supplied the H7 closure coordinates; the H1 route
  card, prior H1 attempt, Bettin--Gonek paper, current door directive, Targets, and relevant zeta
  APIs were re-read before selection.
- `protected_files`: all six inherited user/exposure files remain untouched and unstaged.

## Preregistration public gate

- `commit`: `1cb89557a3630778270da171ba59d87b1fa1f132`.
- `public_ci`: Lean Action run `29966502725`, build job `89079059819`, passed in `1m56s`.
- `effect`: the fixed proof-source endpoint is open. No production Lean source was created before
  this gate passed.

## Local endpoint result

The exact source definitions, real-cutoff interpolation, pointwise and moment convexity, final
power-exponent barrier, fixed-theta zeta zero-free consumer, all-theta RH consumer, and fixed-theta
boundary witness compile without warnings. This is `FULL_SUCCESS_AT_CONSUMER_ENDPOINT` locally:
the production scan is empty, diff checks pass, and the full `8,751`-job build succeeds. Public
implementation CI remains. The Mellin/residue moment-to-power bridge and Farmer's theta-infinity
moment conjecture remain open with no proving declaration.
