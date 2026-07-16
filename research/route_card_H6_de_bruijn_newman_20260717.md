# Route Card H6: de Bruijn-Newman Heat Flow

Date: 2026-07-17

Status: `H6_H1_PUBLICLY_CLOSED_REVERSE_HEAT_LI_EVIDENCE_PENDING`

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

H6-B and H6-H1 are complete. Return to fresh value-ranked route selection before choosing the
all-real-zero/threshold framework or H6-X. Keep H6-Q as a later `PROOF-ATTEMPT`; the H0-xi bridge
and heat equation alone supply no evidence for its global zero certificate.

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
