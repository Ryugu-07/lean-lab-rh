# H6 Forward Real-Zero Preservation Preregistration

Date: 2026-07-17

Campaign: `CAMPAIGN-20260717-H6-FORWARD-PRESERVATION-01`

Mode: `LITERATURE`

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

## Route selection

The exact H6 source family, entire backward heat equation, all-complex-zero predicate, time-zero
RH equivalence, and closedness of the all-real-zero time set are publicly compiled. Fresh
value-ranked selection compares the remaining open frontiers.

- H1-B and H2-B are finite-count statement infrastructure and do not shorten an RH hard gap.
- H10-B is complete; the curve construction and any number-field transfer require much larger
  missing prerequisites.
- M2/G3 and W2/G7 remain direct targets, but the current obstruction map supplies no materially
  new unconditional approximation or positivity mechanism after the compiled audits.
- H6 forward preservation is the next source theorem after closedness. It turns the compiled
  all-real-zero time set into an upper set and is necessary for the threshold interval theorem.

Select the exact de Bruijn forward theorem. This is not a helper campaign and may not close on
finite-degree, simple-zero, bounded-time, or conditional variants.

## Exact mathematical endpoint

For all real times `t <= tau`, if every complex zero of the exact source-normalized `H_t` is real,
then every complex zero of `H_tau` is real:

`t <= tau -> AllZerosReal(t) -> AllZerosReal(tau)`.

The statement quantifies all complex zeros, allows arbitrary multiplicity and an infinite zero
set, and has no spacing or simplicity premise.

## Fixed Lean endpoint

The final declaration must have the following strength:

```lean
theorem deBruijnNewmanAllZerosReal_mono
    {t tau : Real} (htt : t <= tau)
    (ht : deBruijnNewmanAllZerosReal t) :
    deBruijnNewmanAllZerosReal tau
```

Binder order or the final theorem name may change, but the exact two-time implication and the
existing predicate may not be weakened.

## Fixed proof architecture

1. Prove that each spatial function `H_t` is a real entire function of order at most one in the
   existing `Complex.Hadamard.EntireOfOrderAtMost` sense. The new estimate must use the source
   double-exponential kernel decay; the current quadratic majorant gives only a coarse order-two
   bound and is insufficient for the fixed route.
2. Apply the generic genus-one Hadamard factorization. Under `AllZerosReal(t)`, every divisor
   factor is supported on the real axis. Use evenness, conjugation symmetry, and `H_t(0) != 0` to
   eliminate the origin monomial and the unwanted linear exponential contribution.
3. Prove the source-specialized de Bruijn vertical-shift lemma: if `F` is in the resulting
   real genus-one class and all its zeros are real, then
   `(F(z+i*a)+F(z-i*a))/2` has only real zeros for every `a >= 0`. The proof compares the two
   shifted factorization norms off the real axis and cannot assume simple zeros.
4. Iterate the shift average with `a_n = sqrt(2*lambda/n)`. On the Fourier side, the `n`-fold
   average multiplies the kernel by `cosh(a_n*u)^n` and remains all-real-zero by step 3.
5. Prove `cosh(sqrt(2*lambda/n)*u)^n -> exp(lambda*u^2)` with the correct factor of two and the
   domination `cosh(x) <= exp(x^2/2)`. Existing source integrability at time `t+lambda` then gives
   compact-uniform convergence of the iterated averages to `H_(t+lambda)`.
6. Use a kernel-checked Hurwitz substitute: the Jensen zero-free circle argument from the
   threshold-closedness campaign transfers any nonreal zero of the nonzero limit to sufficiently
   large approximants. Since every approximant has only real zeros, the limit does as well.
7. Set `lambda = tau-t`, discharge `lambda >= 0`, and identify the limit multiplier with the exact
   compiled `H_tau` integral.

The implementation may replace this architecture only if it proves the same exact endpoint and
records the stronger source theorem used. A generic theorem imported as an unproved premise is
forbidden.

## Existing support and missing dependencies

Available and public:

- exact source integral and all-real-time quadratic/linear integrability;
- entire spatial family and the backward heat equation;
- positivity and nonvanishing at spatial zero;
- joint time-space continuity and arbitrary-multiplicity Jensen zero persistence;
- generic finite-order Hadamard factorization infrastructure vendored from
  `PrimeNumberTheoremAnd`.

Missing at selection time:

- a source order-at-most-one growth bound for `H_t`;
- a Laguerre-Polya or real-entire strip class in mathlib;
- the de Bruijn vertical-shift norm comparison;
- a packaged real-rooted polynomial or entire-function heat preserver;
- a packaged Hurwitz theorem for locally uniform limits;
- the compact-uniform `cosh` heat-multiplier limit.

## Adversarial tests

- `tau=t` must reduce to the original predicate without a strict-time assumption.
- The heat sign and the factor `sqrt(2*(tau-t)/n)` must agree with
  `partial_t H_t = -partial_z^2 H_t`.
- Multiple real zeros are allowed; no differentiable zero trajectories may be assumed.
- Infinite zero sets and zeros escaping to infinity may not be replaced by a finite polynomial
  model.
- The limit argument must rule out a nonreal zero in an arbitrary compact nonreal ball, not only
  prove pointwise convergence on the real axis.
- The proof may not assume a uniform lower zero gap, simplicity, or positive-time zero
  asymptotics.
- A theorem for small `tau-t`, nonnegative times only, or a bounded time interval is rejected.
- Closedness of the good-time set does not imply forward preservation and may not be used as if it
  did.

## Sources and originality boundary

- N. G. de Bruijn, *The roots of trigonometric integrals* (1950), proves the classical strip
  contraction and forward heat preservation mechanism.
- B. Rodgers and T. Tao, *The De Bruijn-Newman constant is non-negative*, arXiv `1801.05914`,
  records for this exact normalization that real-zero times are forward preserved.
- P. Branden and M. Chasse, *Classification theorems for operators preserving zeros in a strip*,
  arXiv `1402.2795`, restates de Bruijn's shifted Jensen theorem, the polynomial
  `exp(-lambda*D^2)` strip contraction, and finite-order entire extensions.

This campaign reconstructs known mathematics in Lean. It makes no originality claim.

## DAG position and accounting

- `node_id`: H6-H2c
- `gap_id`: G8 dependency
- `relation_to_RH`: threshold structure; at time zero the predicate is exactly RH, but the forward
  implication does not prove the time-zero predicate
- `assumption_frontier_before`: exact source family, entire heat evolution, zero coordinate,
  time-zero RH equivalence, nonzero-family witness, and threshold closedness are public
- `hard_gap_before`: forward preservation, threshold nonemptiness/upper-ray structure, H6-E/G8,
  W2/G7, M2/G3, and RH are open
- `expected_hard_gap_delta`: 0
- `expected_route_infrastructure_delta`: 1

Success closes only forward preservation. Threshold nonemptiness, a finite upper bound proved
inside this project, the definition and interval theorem for `Lambda`, `Lambda <= 0`, and RH
remain open.

## Success, falsification, and stop criteria

- `success_criterion`: the exact two-time monotonicity theorem compiles; the order-one,
  shift-preserver, heat-multiplier, and nonreal-zero limit witnesses used by it are registered;
  exact Targets and TargetChecks compile; selected axiom prints are standard-only; forbidden
  scans, `git diff --check`, the full build, and public implementation CI pass.
- `falsification_criterion`: a fixed mathematical component is false for the compiled
  normalization, including the heat sign, factor-of-two multiplier, source order, shifted norm
  comparison, or claimed domination. Record the exact counterexample or compiler-checked
  contradiction without weakening the endpoint.
- `dependency_gap`: if the endpoint cannot be kernel-closed, record the first missing theorem and
  its exact hypotheses as an OBS node. Helper lemmas do not count as success.
- `local_stop`: close only after the exact endpoint and all gates pass, or record
  `DEPENDENCY_GAP_IDENTIFIED`, `FALSIFIED`, or `NO_PROGRESS` and return to route selection. A local
  stop never pauses the persistent RH Goal.

No Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Public preregistration gate

Preregistration commit `6e10d6eb74f038575e1d6ab4dcde92eb4e58b2ce` passed public Lean Action CI
run `29520281656`, build job `87695371156`, in `1m51s`. Lean proof-source edits may begin from
this fixed endpoint and architecture.

## Local implementation result

`LeanLab/Riemann/DeBruijnNewmanForward.lean` compiles the exact fixed endpoint
`deBruijnNewmanAllZerosReal_mono` without additional hypotheses. The implementation proves the
source order-one bound, genus-one Hadamard factorization with the linear exponent eliminated,
strict shifted-product comparison, vertical-average real-zero preservation, finite shift
iteration, the scaled `cosh` heat-multiplier limit with an integrable scalar-error majorant, and
Jensen persistence of an isolated nonreal zero in the locally uniform limit.

The exact Targets entry and TargetCheck compile. The registered witnesses
`deBruijnNewmanH_entireOfOrderAtMost_one`,
`exists_deBruijnNewmanH_constant_hadamard_factorization`,
`deBruijnNewman_verticalAverage_allZerosReal`, and
`deBruijnNewmanAllZerosReal_mono` each print exactly the transitive axioms `propext`,
`Classical.choice`, and `Quot.sound`. The new module has no diagnostics under default resource
limits; forbidden proof-token, custom-declaration, and resource-relaxation scans are empty;
`git diff --check` passes; and the full 8,689-job build succeeds.

This is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. Implementation commit
`344b4669224a5beb9e7c9a99a176b24735688986` passed public Lean Action CI run `29526887492`,
build job `87717424885`, in `2m47s`. Immutable evidence backfill and its own public CI remain, so
the campaign is not yet publicly closed. Threshold nonemptiness and upper-time existence,
H6-E/G8, W2/G7, M2/G3, and RH remain open.
