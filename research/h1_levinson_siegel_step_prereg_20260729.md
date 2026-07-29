# H1 Levinson--Siegel Step Geometry Preregistration

Date: 2026-07-29

Campaign: `PROOF-ATTEMPT-20260729-H1-LEVINSON-SIEGEL-STEP-01`

Node: `H1-LEVINSON-SIEGEL-STEP-GEOMETRY-01`

Mode: `PROOF-ATTEMPT / HISTORICAL_OMISSION / CROSS_ROUTE`

Status: `IMPLEMENTED_LOCAL / PUBLIC_IMPLEMENTATION_REQUIRED`

Preregistration commit `ab02915f8719c6715e0cadd06dcaad9fa7a10a7d` passed public Lean
Action run `30409200376`, build job `90441363357`, in `1m30s`. Production proof editing began
only after this gate passed.

## Parent and selection

- `parent_closure`: H7 Berry--Keating closure receipt
  `9a545be84ea2bd053936195f5e616f92ee6730b6`, public Lean Action run
  `30408587106`, build job `90439516550`, passed in `1m34s`.
- `selected_node`: `H1-LEVINSON-SIEGEL-STEP-GEOMETRY-01`.
- `selection_reason`: the project has formalized a short-mollifier variational sufficiency
  theorem but not the structural mechanism by which length-dependent derivative combinations
  approach Siegel's discontinuous step. That mechanism overturned a long-standing negative
  expectation about short mollifiers and is therefore a high-value omission probe.
- `material_difference`: this leaves H7 and does not optimize an existing numerical upper
  bound. It tests the geometry and necessary complexity of the source admissibility class.

## Source lock

Primary sources:

1. J. B. Conrey, *More than two fifths of the zeros of the Riemann zeta function are on the
   critical line*, J. reine angew. Math. 399 (1989), equations `(32)`--`(39)`:
   <https://aimath.org/~kaur/publications/24.pdf>.
2. J. B. Conrey, D. W. Farmer, C.-H. Kwan, Y. Lin, and C. L. Turnage-Butterbaugh,
   *Short mollifiers of the Riemann zeta-function*, equations `(3)`, `(11)`, `(18)` and
   Proposition 1:
   <https://arxiv.org/abs/2508.11108>.

The 2025 source allows continuously differentiable functions on `[0,1]` satisfying

```text
Q(0) = 1
Q(y) + Q(1-y) = 1.
```

Its actual optimizer depends on the mollifier length and converges pointwise to the Siegel step
as that length tends to zero. This campaign does not claim that its explicit family is that
optimizer. It independently audits the geometry of the same admissibility condition.

## Fixed definitions

Create `LeanLab/Riemann/LevinsonSiegelStep.lean` only after preregistration public CI.

For `R > 0`, define the logistic profile

```text
L_R(y) = 1 / (1 + exp(R * (2*y - 1)))
```

and its endpoint normalization

```text
Q_R(y) = (L_R(y) - L_R(1)) / (L_R(0) - L_R(1)).
```

Define the Siegel step by the exact three cases `y < 1/2`, `y = 1/2`, and `1/2 < y`.
Names may be adjusted to local style, but the mathematical statements may not be weakened
silently.

## Fixed Lean endpoint

`FULL_SUCCESS` requires all of the following.

1. Prove `L_R(1-y) = 1-L_R(y)` and positivity/nonvanishing of the normalization denominator
   for every `R>0`.
2. Prove `Q_R(0)=1`, `Q_R(1)=0`, and `Q_R(y)+Q_R(1-y)=1`.
3. Prove differentiability of `Q_R` and an exact derivative formula.
4. Prove the exact midpoint value `Q_R(1/2)=1/2`.
5. Prove pointwise convergence as `R -> +infinity`:
   `Q_R(y) -> 1` for `y<1/2`, `Q_R(1/2)=1/2`, and `Q_R(y) -> 0` for `1/2<y`.
6. Prove the midpoint derivative has unbounded magnitude. An exact formula plus a bound
   `R/2 <= |Q_R'(1/2)|` for `R>0` is sufficient.
7. Prove a general real mean-value theorem: if a differentiable function falls from `u` at
   `a` to `v` at `b`, with `a<b` and `v<u`, then at some interior point
   `|Q'| >= (u-v)/(b-a)`. Package a corollary showing that arbitrarily sharp step
   approximation cannot have one uniform derivative bound.
8. Combine the explicit admissible family, pointwise step limit, and general steepness
   obstruction in one endpoint theorem.

Register one proven Target and exact TargetChecks. Add selected standard-only axiom prints to
`AxiomsAudit.lean`. Import the module from `LeanLab.lean`.

## Success, partial, and failure criteria

`FULL_SUCCESS` requires all eight fixed items, no placeholders, warning-as-error compiles,
exact TargetChecks, standard-only selected axiom prints, empty forbidden/resource scans,
`git diff --check`, a full build, and independent public CI.

`MEANINGFUL_PARTIAL` requires the exact source endpoint/reflection identities and either:

- the full three-case pointwise limit; or
- the general sharp-transition derivative lower bound.

`FALSIFIED_EXPLICIT_FAMILY` requires a compiled counterexample to one of the claimed endpoint,
reflection, or limit properties for the exact normalized logistic family.

`BLOCKED_API` is not mathematical failure. It requires an exact statement of the missing
Mathlib limit or mean-value interface and retention of every already compiled subtheorem.

## Negative controls

- Pointwise convergence must not be reported as uniform convergence. A continuous family
  cannot converge uniformly to the discontinuous step on `[0,1]`.
- The normalized logistic family must not be identified with the source hypergeometric
  optimizer `Q_theta`.
- A smooth source-admissible function is not automatically a polynomial differential
  combination. The source's Weierstrass approximation passage remains separate.
- Derivative blow-up does not by itself prove polynomial degree growth without an additional
  approximation theorem.
- No mollified mean-value asymptotic, argument-principle count, critical-zero proportion,
  zero-free region, H1, or RH may be assumed or inferred.

## Obstacle map

- `OBS-H1-LEVINSON-COUNTING-BRIDGE-01`: the actual zeta auxiliary, argument variation,
  right-zero count, Littlewood lemma, and finite-height critical-zero count remain uncompiled.
- `OBS-H1-MEAN-VALUE-01`: the required source mollified second moment remains an analytic
  producer, not a consequence of admissibility geometry.
- `OBS-H1-COMPLEXITY-UNIFORMITY-01`: source mean-value estimates must remain uniform while
  the derivative combination becomes increasingly sharp or high degree.
- `OBS-H1-SPARSE-EXCEPTION-01`: even critical-line density one does not exclude a finite or
  density-zero off-line orbit.

The campaign may close only the geometry and complexity node. The persistent RH Goal remains
active after every local outcome.

## Audit gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. exact checks for every registered theorem;
4. selected `#print axioms` output contains only accepted standard foundations;
5. warning-as-error compile of the new module and registration files;
6. full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop this local campaign and rerank all
historical routes.

The preregistration gate passed at commit
`ab02915f8719c6715e0cadd06dcaad9fa7a10a7d`, Lean Action run `30409200376`, build job
`90441363357`, in `1m30s`.
