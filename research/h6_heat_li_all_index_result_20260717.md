# H6 Heat-Li All-Index Result

Date: 2026-07-17

Campaign: `LITERATURE-20260717-H6-HEAT-LI-ALL-INDEX-01`

Status: `LOCAL_IMPLEMENTATION_AUDITED`

## Compiled endpoint

`LeanLab/Riemann/DeBruijnNewmanLiCriterion.lean` defines the successor-indexed derivative
coefficient `deBruijnNewmanHeatLiCoefficient t n` and proves:

- the exact reflection-paired, multiplicity-bearing zero formula for every real `t` and every
  index;
- `deBruijnNewmanAllZerosReal t` iff every coefficient has nonnegative real part, for every real
  `t`;
- pointwise equality with `liCoefficientCandidate n` at `t=0`;
- the existing RH criterion iff all time-zero heat coefficients have nonnegative real part;
- the preregistered nonnegative-time aggregate endpoint.

## Stronger boundary

The proof does not use the `t>=0` zero strip. The compiled affine finite-order bridge gives order at
most one for heat-Xi at every real time, hence reciprocal-square summability of its nonzero divisor
for every `t`. The complete criterion therefore holds on all of `Real`.

## Proof architecture

1. Preserve entire order under complex input scaling and output scaling.
2. Build the heat-Xi divisor, reflection permutation, multiplicity preservation, and zero coverage.
3. Extract an abstract Bombieri-Lagarias criterion for any reflected divisor with finite norm
   sublevels and reciprocal-square summability.
4. Reconstruct the all-order Hadamard logarithmic-derivative formula with locally uniform
   termwise differentiation.
5. Average reflection pairs and cancel the linear Hadamard contribution using `F(1-s)=F(s)`.
6. Transport critical-line divisor values back to real source zeros and align `t=0` definitions.

## Audit

- new module: 1,855 lines, standalone diagnostic-free compile
- full build: 8,696 jobs, success
- TargetChecks and registry compile
- selected axioms: `propext`, `Classical.choice`, `Quot.sound`
- no `sorry`, `admit`, `native_decide`, custom axiom/constant/opaque/unsafe declaration, or resource
  relaxation

## Classification

`KNOWN_CRITERION_HEAT_FAMILY_SPECIALIZATION`; `hard_gap_delta=0`,
`route_infrastructure_delta=1`. This does not prove unconditional all-index positivity or RH.
Implementation public CI and evidence backfill are pending.
