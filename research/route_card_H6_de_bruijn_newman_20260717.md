# Route Card H6: de Bruijn-Newman Heat Flow

Date: 2026-07-17

Status: `H6_UPPER_HALF_LOCAL_IMPLEMENTATION_VERIFIED_PUBLIC_CI_PENDING`

## Endpoint and normalization

Following the Polymath normalization, define

`H_t(z) = integral_0^infinity exp(t*u^2) * Phi(u) * cos(z*u) du`,

where `Phi` is the standard super-exponentially decaying theta kernel. Then

`H_0(z) = (1/8) * xi((1 + i*z)/2)`

and `partial_t H_t = - partial_z^2 H_t`. There is a finite real constant `Lambda` such that all
zeros of `H_t` are real exactly for `t >= Lambda`. RH is equivalent to `Lambda <= 0`.

Rodgers-Tao prove `Lambda >= 0`; consequently the remaining H6 endpoint is exactly `Lambda = 0`,
not merely another upper-bound improvement.

## Sources and strongest unconditional result

- de Bruijn established forward preservation of real zeros under the heat deformation and an
  initial upper bound.
- Newman established the threshold constant and conjectured `Lambda >= 0`.
- Rodgers and Tao,
  [*The de Bruijn-Newman constant is non-negative*](https://arxiv.org/abs/1801.05914), prove
  `Lambda >= 0`.
- D. H. J. Polymath,
  [*Effective approximation of heat flow evolution of the Riemann xi function*](https://arxiv.org/abs/1904.12438),
  proves the unconditional upper bound `Lambda <= 0.22` using effective estimates and certified
  numerical work.

Thus the audited interval is `0 <= Lambda <= 0.22`.

## First open edge and false-progress patterns

The exact open edge is to prove all zeros of `H_0` are real, equivalently `Lambda <= 0`. Proving
`Lambda <= c` for any fixed positive `c` improves an upper bound but does not approach the sign
endpoint by logic alone; a sequence `c_n -> 0` needs uniform certified arguments before taking a
limit.

False-progress patterns:

- proving real-rootedness at one `t > 0` and propagating the heat equation in the wrong direction;
- using numerically tracked zeros without a global nonvanishing region and argument-principle
  certificate;
- changing the `H_t`, xi, or heat-sign normalization without an M0 alignment;
- treating zero repulsion or simplicity as real-rootedness;
- defining `Lambda` as an infimum and assuming membership at the infimum without closedness.

## Formalization fit

The project has a source-aligned entire xi, its multiplicity divisor, reflection, Hadamard
factorization, Li criterion, Fourier infrastructure, Gaussian transforms, and compact Weil test
classes. Missing prerequisites are the exact theta kernel `Phi`, super-exponential integrability,
joint differentiation under the integral, the backward heat equation, all-real-zero predicates,
de Bruijn monotonicity, threshold existence/closedness, and certified complex nonvanishing tools.

## Candidate H6-B: exact time-zero bridge

**Exact proposition.** With `H` and `Phi` defined from the Polymath source,

`forall z : C, H 0 z = (1/8) * riemannXi ((1 + I*z)/2)`.

**Compiled Lean statement.** The definition-alignment campaign compares the project's `riemannXi`
normalization term by term:

```lean
theorem deBruijnNewmanH_zero_eq_riemannXi (z : Complex) :
    deBruijnNewmanH 0 z =
      (1 / 8 : Complex) * riemannXi ((1 + Complex.I * z) / 2)
```

**DAG and strength.** H6/M0-style definition bridge. It does not prove a new zero statement, but
it is necessary before any H6 theorem can touch the project RH target.

**Adversarial tests.** Evaluate `z = 0`, check all factors of two and eight, compare the project's
xi at `s` and `1-s`, and verify the complex cosine/Fourier convention.

**Implementation result.** `LeanLab/Riemann/DeBruijnNewman.lean` explicitly defines the source
theta kernel and heat family, proves the double-exponential convergence and integration-by-parts
chain, transforms mathlib's self-dual theta Mellin representation by `x = exp (4*u)`, and compiles
the exact identity above. TargetCheck witnesses and the transitive axiom audit pass with only
`propext`, `Classical.choice`, and `Quot.sound`.

**Verdict:** `COMPLETE`, classified `KNOWN_THEOREM_FORMALIZED`. This closes the H6/M0 bridge with
`hard_gap_delta=0`; it does not prove any new zero statement.

## Candidate H6-H1: entire heat family and backward heat equation

**Exact proposition.** For every real `t`, the compiled source integral `H_t` is entire in the
complex spatial variable, differentiable in real time, and satisfies

`partial_t H_t(z) = -partial_z^2 H_t(z)`

for every complex `z`, with both sides equal to the same `u^2`-weighted source integral.

**DAG and strength.** H6 analytic infrastructure between H6-B and the all-real-zero/threshold
theory. It proves no zero-location statement and has `hard_gap_delta=0`, but H6-X and an honest
zero-dynamics layer require it.

**Adversarial tests.** Require all real `t`, not only nonnegative or bounded time; require complex
`z`, not only the real axis; audit the backward sign; and prove neighborhood-uniform domination
rather than differentiating a merely formal integrand.

**Implementation result.** `LeanLab/Riemann/DeBruijnNewmanHeat.lean` proves a reusable all-real-time
majorant for `(1+u^2)*exp(c*u^2+d*u)*|Phi(u)|`, then applies dominated parameter integration in
real time and complex space. The compiled endpoints are `hasDerivAt_deBruijnNewmanH_time`,
`differentiable_deBruijnNewmanH`, `deriv_deriv_deBruijnNewmanH`, and
`deBruijnNewmanH_backward_heat_equation`. Exact witnesses and all five selected transitive axiom
prints pass; the latter use only `propext`, `Classical.choice`, and `Quot.sound`.

**Verdict:** `COMPLETE` as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. It closes H6-H1 only. The all-real-zero predicate, forward
preservation, threshold existence/closedness, H6-E, and RH remain open.

## Candidate H6-H2a: exact zero-coordinate framework

**Exact proposition.** Define `AllZerosReal(t)` by quantifying every complex zero of the compiled
source `H_t`. Under the inverse coordinate `z(s)=-i*(2*s-1)`, prove both directions of the zero
correspondence, prove every `H_0` zero lies in `-1<Im(z)<1`, and compile

`Mathlib.RiemannHypothesis <-> AllZerosReal(0)`.

**DAG and strength.** This is the definition-alignment subedge of H6-H2. The final equivalence is
exactly RH-strength, but proving the equivalence does not prove either side. It supplies the fixed
predicate and coordinate required by forward preservation and threshold work.

**Adversarial tests.** Check `s=0,1`, the sign `Im(z(s))=1-2*Re(s)`, strict strip endpoints,
surjectivity from an arbitrary nontrivial zero, the nonzero factor `1/8`, and all complex zero
quantifiers. Do not claim multiplicity transport.

**Campaign gate.** Selected as campaign
`CAMPAIGN-20260717-H6-ZERO-COORDINATE-FRAMEWORK-01`. Exact preregistration is in
`h6_zero_coordinate_framework_prereg_20260717.md`. Preregistration commit
`8ec051e767319a2a7c6dc40c465e0e9d8b1e2d7e` passed public CI run `29512089828`, build job
`87667820977`, in `2m17s`.

**Implementation result.** `DeBruijnNewmanZeros.lean` compiles the exact source coordinate and
inverse, both zero-correspondence directions, strict strip, boundary exclusions, and
`RiemannHypothesis <-> deBruijnNewmanAllZerosReal 0`. The aggregate witness and five selected
axiom prints pass with the standard trust base only.

**Verdict:** `COMPLETE` as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. Implementation commit
`0283db6a11ef452a7241e17c535744677272a7d1` passed public CI run `29513380203`, build job
`87672181193`, in `1m59s`. Evidence commit `0848fcaf5050d6cc842d53a4154172d7511619f6`
passed run `29513928275` on attempt 2, build job `87674259193`, in `2m5s`; the campaign is publicly
closed. Forward preservation, threshold existence/closedness, H6-E/G8, and RH remain open.

## Candidate H6-H2b: closedness of the all-real-zero time set

**Exact proposition.** For the compiled source family and all-complex-zero predicate, prove

`IsClosed {t : R | deBruijnNewmanAllZerosReal t}`.

**Proof architecture.** Prove the family is jointly continuous in time and complex space and is
never identically zero. Isolate any nonreal zero by a zero-free circle. The zero-free Jensen
logarithmic circle mean then shows that every sufficiently small parameter perturbation has a zero
inside that same nonreal ball. Hence the complement of the all-real-zero set is open.

**DAG and strength.** This is threshold infrastructure at H6-H2. It validates passage to a limit
time once all-real-zero times converge, but does not prove the set is nonempty or upward closed.
It has expected `hard_gap_delta=0` and `route_infrastructure_delta=1`.

**Adversarial tests.** Require arbitrary zero multiplicity, joint or compact-uniform parameter
control, a closed ball disjoint from the real axis, a nonzero-family proof at every real time, and
the exact all-complex-zero predicate. Do not infer threshold existence or forward preservation.

**Campaign gate.** Selected as
`CAMPAIGN-20260717-H6-THRESHOLD-CLOSEDNESS-01`. Exact preregistration is in
`h6_threshold_closedness_prereg_20260717.md`.

Preregistration commit `02758ff243c3f8cd434eb3c007a2a5f6b094fea7` passed public Lean Action CI
run `29515723482`, build job `87680126242`, in `1m56s`.

**Implementation result.** `DeBruijnNewmanThreshold.lean` proves source-kernel positivity,
nonvanishing at spatial zero for every real time, joint time-space continuity, and full-multiplicity
zero persistence using Jensen's zero-free logarithmic circle mean. Analytic isolated zeros provide
a nonreal isolating ball, and the complement of the all-real-zero time set is open.

The exact endpoint, target witness, four TargetChecks, and four standard-only axiom prints compile
locally. Forbidden scans are empty, `git diff --check` passes, and the full 8,688-job build
succeeds. Implementation commit `6322bbd59d25f919befc91cd5a057251bcf94cb4` passed public Lean
Action CI run `29518062294`, build job `87687972172`, in `2m7s`. Evidence-backfill commit
`c5b9405befd3029f04b1301f55a8a9c45074dce4` passed run `29518417233`, build job `87689151089`, in
`1m36s`; the campaign is publicly closed.

**Verdict:** `COMPLETE` as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. At this campaign's closure, forward preservation remained open;
H6-H2c is now locally proved below. Threshold nonemptiness/upper-ray structure, H6-E/G8, W2/G7,
M2/G3, and RH remain open.

## Candidate H6-H2c: de Bruijn forward real-zero preservation

**Exact proposition.** For the compiled source family and all-complex-zero predicate,

`t <= tau -> deBruijnNewmanAllZerosReal t -> deBruijnNewmanAllZerosReal tau`.

The statement permits arbitrary multiplicity and an infinite zero set. It has no simplicity,
spacing, bounded-time, or finite-degree premise.

**Proof architecture.** Prove source order at most one from the double-exponential kernel decay,
then use the vendored genus-one Hadamard factorization to establish de Bruijn's vertical-shift
average preserver. Iterating shifts of size `sqrt(2*(tau-t)/n)` gives the Fourier multiplier
`cosh(sqrt(2*(tau-t)/n)*u)^n`, which converges compact-uniformly to the exact heat multiplier
`exp((tau-t)*u^2)`. Jensen zero persistence excludes a nonreal zero in the nonzero limit.

**DAG and strength.** This is the next open H6-H2 threshold edge. Together with the compiled
closedness theorem it will show that the good-time set is a closed upper set. It does not prove
that the set is nonempty or that time zero belongs to it. Expected `hard_gap_delta=0` and
`route_infrastructure_delta=1`.

**Adversarial tests.** Require equality times, arbitrary multiplicity, infinite zero sets, the
backward-heat sign, the factor of two in the shift scale, compact-uniform rather than real-axis
convergence, and the exact source predicate. Reject small-time, simple-zero, bounded-time, and
polynomial-surrogate weakenings.

**Campaign gate.** Selected as
`CAMPAIGN-20260717-H6-FORWARD-PRESERVATION-01`. Exact preregistration is in
`h6_forward_preservation_prereg_20260717.md`. Public preregistration CI is required before Lean
proof-source edits.

Preregistration commit `6e10d6eb74f038575e1d6ab4dcde92eb4e58b2ce` passed public Lean Action CI
run `29520281656`, build job `87695371156`, in `1m51s`.

**Implementation result.** `DeBruijnNewmanForward.lean` proves the exact endpoint through the
fixed architecture: source order one, genus-one Hadamard factorization, strict shifted-product
comparison, de Bruijn vertical averages, finite `cosh` multiplier iteration, dominated locally
uniform convergence to the exact forward heat multiplier, and Jensen persistence of a nonreal
zero. No simplicity, spacing, finite-degree, bounded-time, or nonnegative-time premise is added.

The exact target and TargetCheck compile. Four registered axiom prints each contain exactly
`propext`, `Classical.choice`, and `Quot.sound`; forbidden scans and `git diff --check` pass; and
the full 8,689-job build succeeds under default resource limits.

Implementation commit `344b4669224a5beb9e7c9a99a176b24735688986` passed public Lean Action CI
run `29526887492`, build job `87717424885`, in `2m47s`.
Evidence-backfill commit `b6e9dd7f6492f60574be68796f38818661422359` passed run `29527202922`, build
job `87718477219`, in `1m57s`; the campaign is publicly closed.

**Verdict:** `COMPLETE` as `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. Threshold nonemptiness/upper-time existence, H6-E/G8, W2/G7,
M2/G3, and RH remain open.

## Candidate H6-H2d: de Bruijn strip contraction and the half-time upper bound

**Exact proposition.** For every `0<=t<=1/2` and every zero `z` of the compiled source family,

`Im(z)^2 <= 1-2*t`.

In particular `deBruijnNewmanAllZerosReal (1/2)`.

**Proof architecture.** Generalize H6-H2c's real-root factor comparison to conjugate pairs of
genus-one Weierstrass factors. A conjugation involution on the multiplicity-bearing divisor index
turns the paired strict inequality into de Bruijn's vertical-average strip contraction. Iterating
`n` shifts of size `sqrt(2*t/n)` subtracts exactly `2*t` from the squared strip width. The
compiled `cosh` heat-multiplier limit and Jensen persistence transfer the same closed strip to
`H_t`.

**DAG and strength.** This is the first nonempty-good-time edge after closedness and forward
preservation. It gives the classical unconditional upper bound `Lambda<=1/2` once a threshold is
packaged. It does not prove the RH-equivalent time-zero predicate and has expected
`hard_gap_delta=0`, `route_infrastructure_delta=1`.

**Adversarial tests.** Require the exact factor `1-2*t`, equality at `t=1/2`, arbitrary
multiplicity, infinite zero sets, real fixed points of conjugation, a positive-natural iteration
index, and a limit ball disjoint from the full contracted strip. Reject polynomial-only,
epsilon-width, conditional, simple-zero, and numerical-surrogate endpoints.

**Campaign gate.** Selected as `CAMPAIGN-20260717-H6-UPPER-HALF-01`. Exact preregistration is in
`h6_upper_half_prereg_20260717.md`. Public preregistration CI is required before Lean proof-source
edits.

Preregistration commit `502864b4a84740600c80a4864f3a3e3deb331c46` passed public Lean Action CI
run `29528426983`, build job `87722558836`, in `1m50s`.

**Implementation result.** `DeBruijnNewmanUpperHalf.lean` compiles the full fixed proposition and
the half-time endpoint. The proof registers conjugation-preserving analytic multiplicity, a
multiplicity-aware divisor involution, paired genus-one factor comparison, one-step strip
contraction, the finite `1-n*a^2` invariant, and isolating-ball Jensen persistence. Targets,
TargetChecks, standard-only axiom audit, forbidden scans, `git diff --check`, and the 8,690-job
full build pass locally.

**Verdict:** `LOCAL_COMPLETE` as `KNOWN_THEOREM_FORMALIZED`; public implementation and evidence
CI remain. Threshold nonemptiness and `Lambda<=1/2` are closed locally. H6-E/G8, W2/G7, M2/G3,
and RH remain open.

## Candidate H6-Q: improve the upper bound to one fifth

**Exact proposition.** Every zero of `H_(1/5)` is real. With the established de Bruijn
monotonicity theorem this gives `Lambda <= 1/5`.

**Proposed Lean statement.** After the H6 definition and zero predicate exist:

```lean
def AllZerosReal (f : Complex -> Complex) : Prop :=
  forall z, f z = 0 -> z.im = 0

def DeBruijnNewmanOneFifth : Prop :=
  AllZerosReal (deBruijnNewmanH (1 / 5))
```

**DAG and strength.** This would improve `0.22` to `0.2`, but remains strictly short of RH and
`Lambda = 0`.

**Adversarial tests.** Search for nonreal zeros near the certified region boundary; audit all
floating-point enclosures; require a global tail nonvanishing proof; verify monotonicity uses the
same heat-sign convention.

**Verdict:** `OPEN_CANDIDATE`. It has a crisp falsification surface but depends on substantial
analytic and interval-arithmetic infrastructure.

## Candidate H6-X: heat-deformed Li criterion

**Exact proposition.** Define

`heatXi_t(s) = 8 * H_t(-i*(2*s-1))`

and define its Li coefficients by the same derivative convention used for project xi. For every
real `t` for which the source genus-one and nonvanishing-at-one hypotheses hold,

`AllZerosReal(H_t) <-> forall n, 0 <= Re(heatLi_t(n))`.

**Proposed Lean statement.** The final theorem should expose, rather than hide, the analytic
hypotheses needed by the generic Bombieri-Lagarias transfer:

```lean
theorem allZerosReal_deBruijnNewmanH_iff_heatLi_nonneg
    (t : Real) (hEntire : HeatXiEntireOrderOne t)
    (hSymm : HeatXiSymmetric t) (hOne : heatXi t 1 != 0) :
    AllZerosReal (deBruijnNewmanH t) <->
      forall n : Nat, 0 <= (heatLiCoefficient t n).re
```

**DAG and strength.** At `t = 0` this specializes to an RH-equivalent H6-H4 bridge. At positive
`t` it is a criterion for the deformed zero set, not RH. The closest known result is the general
Li/Bombieri-Lagarias criterion plus the project's compiled xi specialization.

**Adversarial tests.** Check the `s <-> z` map, multiplicities, normalization invariance of log
derivatives, possible zeros at `s = 1`, and whether the genus/order assumptions survive every
real `t` under consideration.

**Verdict:** `SHORTLIST_CANDIDATE`. It offers high reuse after H6-B, but cannot precede the exact
source normalization and analytic hypotheses.

## Recommendation

H6-B, H6-H1, H6-H2a, H6-H2b, and H6-H2c are publicly complete; H6-H2d is locally complete and
awaits public implementation/evidence CI. After closure, return to fresh value-ranked route
selection. Keep H6-Q as a later `PROOF-ATTEMPT` and keep direct H6-E/G8, W2/G7, and M2/G3 attacks
open.

## Candidate H6-Y: reverse-heat Li transfer audit

**Exact falsification target.** Test whether the heat PDE, reflection symmetry, nonvanishing at
`s=1`, and critical-line zeros at a later time generically force Li positivity at an earlier time.
The fixed polynomial candidate is

`F_t(s)=(s-1/2)^2-1/16+t/2`.

It is predicted to satisfy all those structural clauses, while its generalized second Li value is
`-64/9` at time zero and `448/121` at time one. This would leave the fixed-time H6-X criterion
intact but prove that a backward transfer needs theta-kernel-specific information.

**Implementation result.** Every registered clause compiles in `H6ReverseHeatLiAudit.lean`,
including the all-zero theorem and the exact `logDeriv`-based Li values. The base point stays
nonzero for all real `t>=0`, so the sign reversal is not caused by crossing a Li singularity.

**Verdict:** `BRANCH_FALSIFIED` as `OBS-H6-REVERSE-HEAT-LI-01`, with `hard_gap_delta=0`. The
actual theta-kernel family, fixed-time H6-X criterion, H6-E/G8, and RH are unchanged.
