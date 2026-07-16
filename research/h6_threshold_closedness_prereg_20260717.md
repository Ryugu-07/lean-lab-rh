# H6 Threshold Closedness Preregistration

Date: 2026-07-17

Campaign: `CAMPAIGN-20260717-H6-THRESHOLD-CLOSEDNESS-01`

Mode: `LITERATURE`

Status: `LOCAL_AUDITS_COMPLETE_PUBLIC_IMPLEMENTATION_CI_PENDING`

## Route selection

The time-zero zero-coordinate framework is publicly closed. Fresh selection compares the two
first open H6-H2 edges: de Bruijn forward preservation of real zeros and closedness of the set of
times at which all zeros are real.

- Forward preservation is the deeper source theorem. The current mathlib/project inventory has
  no Laguerre-Polya, Hermite-Poulain, strip-shrinking, or real-rooted polynomial infrastructure
  that exposes its core mechanism.
- Mathlib has no packaged Rouche theorem, Hurwitz theorem, or argument principle suitable for
  importing root persistence directly.
- Mathlib does have analytic isolated zeros and the zero-free Jensen/mean-value identity
  `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`.
- The compiled source majorant already controls arbitrary local quadratic and linear exponential
  weights, so joint parameter-space continuity can be proved by dominated convergence.

Closedness is therefore the shortest source-aligned theorem that materially advances the H6-H2
threshold framework. It does not prove that the all-real-zero set is nonempty or upward closed.

## Exact mathematical endpoint

For the already compiled predicate

`AllZerosReal(t) := forall z : C, H_t(z)=0 -> Im(z)=0`,

prove the exact topological statement

`IsClosed {t : R | AllZerosReal(t)}`.

Equivalently, if `t_n -> t` and every `H_(t_n)` has only real zeros, then every zero of `H_t` is
real. The theorem quantifies every complex zero and allows arbitrary multiplicity.

## Proposed Lean interface

The final implementation target is a new module imported after
`LeanLab/Riemann/DeBruijnNewmanZeros.lean`:

```lean
theorem continuous_deBruijnNewmanH_joint :
    Continuous (fun p : ℝ × ℂ => deBruijnNewmanH p.1 p.2)

theorem deBruijnNewmanH_zero_ne_zero (t : ℝ) :
    deBruijnNewmanH t 0 ≠ 0

theorem isClosed_setOf_deBruijnNewmanAllZerosReal :
    IsClosed {t : ℝ | deBruijnNewmanAllZerosReal t}
```

Helper theorem names may change, but the final `IsClosed` statement and its predicate may not.

## Fixed proof architecture

1. Prove `deBruijnNewmanPhi u > 0` for `u >= 0`. Each summand factors into positive terms and
   `2*pi*n^2*exp(4*u)-3 > 0`; summability then gives strict positivity of the theta sum.
2. Integrate the positive `z=0` kernel on `Ioi 0` to prove `H_t(0) != 0` for every real `t`.
   This excludes an identically zero spatial function at every time.
3. Apply the isolated-zero theorem to any zero `z0` of `H_t` and choose a positive radius whose
   boundary contains no zero. If `z0` is nonreal, shrink the radius so the closed ball is disjoint
   from the real axis.
4. Prove joint continuity of `(t,z) |-> H_t(z)` by dominated parameter integration. The local
   majorant uses `(|t|+1)*u^2 + (norm z+1)*u` and the existing all-real-time integrability theorem.
5. Compactness of the zero-free boundary gives a positive lower bound for `norm(H_t)` there.
   Joint continuity preserves a smaller lower bound for all nearby times and makes the value at
   the center arbitrarily small.
6. If a nearby `H_tau` had no zero in the closed ball, the zero-free Jensen mean identity would
   equate the circle average of `log(norm(H_tau))` to its center value. The boundary lower bound
   makes the average at least `log m`, while the center is strictly below `log m`, a contradiction.
7. Thus every sufficiently nearby time has a zero in the nonreal ball. The complement of the
   all-real-zero set is open, so the set itself is closed.

This proof does not require simple zeros, differentiable zero trajectories, or a full Rouche
theorem.

## Adversarial tests

- A theorem for simple zeros only is rejected; multiplicities are unrestricted.
- Pointwise continuity in `t` is insufficient. The proof must kernel-check joint or compact-uniform
  control on the chosen circle.
- The chosen ball must be disjoint from the real axis, not merely centered at a nonreal point.
- The Jensen hypothesis must be zero-free on the full closed ball, including its boundary.
- `H_t` must be proved nonzero for every real `t`; an implicit assumption that an entire function
  is not identically zero is rejected.
- Closedness alone must not be reported as threshold existence, upper-ray monotonicity, or a
  definition of `Lambda` with attained infimum.

## Sources and originality boundary

- B. Rodgers and T. Tao, *The De Bruijn-Newman constant is non-negative* (arXiv `1801.05914`),
  states that the source-normalized `H_t` has all zeros real exactly for `t >= Lambda`.
- D. H. J. Polymath, *Effective approximation of heat flow evolution of the Riemann xi function*
  (arXiv `1904.12438`), uses the same `H_t` normalization and threshold statement.
- Mathlib supplies analytic isolated zeros and Jensen's zero-free logarithmic circle mean.

The closedness theorem is known threshold infrastructure, not an originality claim.

## DAG position and accounting

- `node_id`: H6-H2b
- `gap_id`: G8 dependency
- `relation_to_RH`: threshold infrastructure; at time zero the predicate remains exactly RH
- `assumption_frontier_before`: source `H_t`, all-real-zero predicate, entire spatial family,
  backward heat equation, and exact time-zero RH equivalence are compiled
- `hard_gap_before`: H6 forward preservation, threshold existence/closedness, H6-E/G8, W2/G7,
  M2/G3, and RH open
- `expected_hard_gap_delta`: 0
- `expected_route_infrastructure_delta`: 1

Success closes only threshold closedness. Forward preservation, nonempty upper-time existence, a
definition and interval theorem for `Lambda`, `Lambda <= 0`, and RH remain open.

## Success, falsification, and stop criteria

- `success_criterion`: the exact `IsClosed` theorem compiles; joint continuity and nonzero-family
  witnesses are registered; exact Targets and TargetChecks compile; selected axiom prints are
  standard-only; forbidden scans, `git diff --check`, the full build, and public implementation CI
  pass.
- `falsification_criterion`: the fixed Jensen persistence argument fails because a required local
  domination, strict positivity, isolated-circle extraction, or zero-free mean-value hypothesis is
  false for the compiled source family. Record the exact mathematical/compiler boundary without
  weakening the endpoint.
- `forbidden_success`: sequential closure with an extra compact-uniform hypothesis, simple-zero
  closure, closure only on a bounded time interval, or a theorem about a surrogate family.
- `local_stop`: close only after the exact endpoint and audits pass, or record
  `DEPENDENCY_GAP_IDENTIFIED`/`NO_PROGRESS` with the first unproved dependency and an OBS node.
  Helper lemmas alone do not count as campaign success.

No Lean proof source has been edited in this campaign before this preregistration.

## Public preregistration gate

Preregistration commit `02758ff243c3f8cd434eb3c007a2a5f6b094fea7` passed public Lean Action CI
run `29515723482`, build job `87680126242`, in `1m56s`. Lean proof-source edits begin only after
this gate.

## Registered implementation result

`LeanLab/Riemann/DeBruijnNewmanThreshold.lean` compiles the exact preregistered endpoint
`isClosed_setOf_deBruijnNewmanAllZerosReal`. The proof establishes strict positivity of the source
kernel, nonvanishing at spatial zero for every real time, joint time-space continuity, and
arbitrary-multiplicity zero persistence through Jensen's zero-free logarithmic circle mean. It
then proves the complement of the exact all-complex-zero predicate is open.

The module is diagnostic-free. Targets, four exact TargetChecks, and four selected transitive
axiom prints compile; every selected declaration uses only `propext`, `Classical.choice`, and
`Quot.sound`. Forbidden proof-token, declaration, and resource-relaxation scans are empty;
`git diff --check` passes; and the full 8,688-job build succeeds. Classification is locally
`KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and `route_infrastructure_delta=1`. Public
implementation CI is pending. Forward preservation, nonempty upper-time existence, threshold
upper-ray structure, H6-E/G8, and RH remain open.
