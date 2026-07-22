# H1 Short-Mollifier Variational Preregistration

Date: 2026-07-22

Campaign: `LITERATURE-20260722-H1-SHORT-MOLLIFIER-VARIATIONAL-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Baseline and cross-route selection

- `parent_commit`: `7e15cfb386e961f7437dfa25d39b6cab85d3946b`.
- `parent_public_ci`: Lean Action run `29934044666`, build job `88970856616`, passed in `1m37s`.
- `previous_campaign`: the H7 finite Herglotz criterion is publicly closed. Its arithmetic scalar
  inequality and spectral limit remain open, but further optimization is not automatic.
- `selected_node`: `H1-SHORT-MOLLIFIER-VARIATIONAL-01`.
- `route_comparison`: H2 density and H11 zero statistics still lack a functional that detects one
  sparse off-line orbit; H10 function-field transfer still lacks a number-field trace object and
  a uniform infinite-spectrum tail. H1 has a source-identified underused degree of freedom, an
  exact variational functional, and a machine-checkable question about global optimality under
  the full advertised parameter condition `c < 1/4`.
- `material_difference`: this leaves H7 and reconstructs a different historical family. It does
  not optimize a reported decimal proportion. It tests whether the Euler-Lagrange solution in the
  2025 short-mollifier framework is a unique global minimizer rather than merely stationary.
- `global_goal`: active; this variational theorem alone cannot prove proportion one or RH.

## Primary source and exact boundary

Primary source: J. Brian Conrey, David W. Farmer, Chung-Hang Kwan, Yongxiao Lin, and Caroline L.
Turnage-Butterbaugh, [Short mollifiers of the Riemann zeta-function](https://arxiv.org/abs/2508.11108),
arXiv:2508.11108v1 (2025), registered as S2.

The source proves that suitably optimized derivative combinations give a positive critical-line
zero proportion for every sufficiently short mollifier. Equations `(58)`-`(63)` state the general
quadratic functional, endpoint conditions, normalized parameter `c < 1/4`, and Euler-Lagrange
equation. The paper writes down the hypergeometric solution and calls it optimal, but the bounded
source audit did not locate a separate proof that stationarity plus `c < 1/4` implies strict
global minimality over the whole admissible path class.

This campaign checks that sufficiency claim independently. It does not import the mollified
mean-value asymptotic, equation `(60)`, the hypergeometric formula, Mathematica output, a zeta-zero
proportion, or any open source question as a Lean premise.

## Exact mathematical target

For `R > 0`, let `h` be a continuously differentiable real function on `[0,R]` with
`h(0)=h(R)=0`. First prove the weighted completion identity

```text
integral cosh(t) * (h'(t) + tanh(t)*h(t)/2)^2
  = integral cosh(t)*h'(t)^2
      - (1/4)*integral cosh(t)*h(t)^2
      - (1/4)*integral h(t)^2/cosh(t),
```

and hence the source-threshold Hardy inequality

```text
(1/4)*integral cosh(t)*h(t)^2
  <= integral cosh(t)*h'(t)^2.
```

Next normalize source equation `(58)` by `c1 > 0` and `c=-c0/c1`:

```text
E(S) = integral [
  2*cosh(t)*(S'(t)^2-c*S(t)^2)
  + 2*c*beta*exp(-t)*S(t)
  - c*beta^2*exp(-t)].
```

Prove the algebraic equality between this expression and source `K(S)/c1`. If `Sstar` has the
source endpoints and satisfies equation `(63)` in weighted form

```text
(cosh(t)*Sstar'(t))'
  = -c*cosh(t)*Sstar(t) + c*beta*exp(-t)/2,
```

then every admissible competitor `S=Sstar+h` satisfies the exact energy-gap identity

```text
E(S)-E(Sstar)
  = 2*integral cosh(t)*(h'(t)^2-c*h(t)^2).
```

Finally prove that `c < 1/4` makes the right side nonnegative, and strictly positive whenever the
competitor differs from `Sstar` somewhere on `[0,R]`. Thus every source Euler-Lagrange solution is
the unique global minimizer in the represented class.

## Proposed Lean spine

The intended production module is `LeanLab/Riemann/ShortMollifierVariational.lean`. Final syntax
may adapt to checked interval-integral APIs without weakening the endpoint. Proposed declarations:

1. `shortMollifierNormalizedEnergy`;
2. `shortMollifierNormalizedEnergy_eq_source`;
3. `shortMollifierWeightedHardyIdentity`;
4. `shortMollifierWeightedHardy_quarter_le`;
5. `shortMollifierNormalizedEnergy_gap_of_eulerLagrange`;
6. `shortMollifierNormalizedEnergy_unique_minimizer`.

Use explicit derivative functions and `HasDerivAt` or an equivalent checked C1 package. The source
alignment, weighted identity, energy-gap equality, nonnegativity, and strict uniqueness endpoint
receive exact TargetChecks. Selected declarations receive `#print axioms` entries.

## Success, falsification, and stopping criteria

- `success`: Lean proves source normalization, the `1/4` weighted inequality, the exact gap
  identity, and unique global minimality for every `c < 1/4`; all mechanical gates and public CI
  pass.
- `meaningful_partial`: the weighted inequality and non-strict minimization compile, but strict
  uniqueness is reduced to a precisely named integral-support or regularity obstruction.
- `falsification`: a kernel-checked path or sign calculation shows that source `(58)`-`(63)` does
  not imply global minimality on the stated parameter domain. Record the exact missing condition.
- `no_progress`: interval integration by parts cannot represent the exact source statement after
  bounded API work. Record the API boundary and route-select; do not replace the continuum target
  with an unrelated finite quadratic form.
- `local_stop`: stop after the global-minimizer certificate is publicly closed or exactly
  falsified. Solving the hypergeometric ODE, optimizing `P`, proving equation `(60)`, and deriving
  a new zeta-zero proportion are separate campaigns.

## Assumption and implication audit

- `assumption_frontier_before`: the source Euler-Lagrange equation is a stationarity condition;
  strict global optimality requires coercivity of its second variation.
- `assumption_frontier_after_on_success`: `c < 1/4` and fixed endpoints are sufficient through a
  kernel-checked weighted Hardy inequality. No numerical plot or explicit special-function formula
  is needed for this implication.
- `arithmetic_boundary`: the source mollified mean-value asymptotic remains outside the Lean
  theorem. The result cannot by itself improve `5/12`, yield proportion one, eliminate sparse
  off-line zeros, or prove RH.
- `not_a_conjecture_premise`: source Questions (1)-(6), including joint `P,S` optimization and the
  all-`theta` numerical bound, remain open targets and are not assumed.
- `expected_deltas`: `rh_frontier_delta=0`, `hard_gap_delta=0`,
  `route_infrastructure_delta=1`, `source_sufficiency_audit_delta=1` on success.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: one inherited recovery occurred in the closed H7 parent; no compaction in
  this route-selection step.
- `protected_files`: the six inherited user/exposure files remain untouched and unstaged.

## Publication gate

Commit only this preregistration, its attempt record, the H7 final-CI backfill, and synchronized
research ledgers first. Public Lean Action CI must pass before
`ShortMollifierVariational.lean`, Targets, TargetChecks, AxiomsAudit, or aggregate imports are
edited.
