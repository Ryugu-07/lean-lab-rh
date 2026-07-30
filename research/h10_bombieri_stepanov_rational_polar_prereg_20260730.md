# H10 Bombieri--Stepanov Rational Polar Realization Preregistration

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H10-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Selected node:
`H10-F-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLICATION_REQUIRED`

## Primary-source anchor

- Enrico Bombieri, *Counting points on curves over finite fields (d'apres S. A. Stepanov)*,
  Seminaire Bourbaki 430 (1973), pages 236--239. The key lemma proves the natural product
  homomorphism is an isomorphism by comparing pole orders at the chosen point before the
  dimension argument:
  `https://www.numdam.org/item/SB_1972-1973__15__234_0.pdf`.
- Kiran Kedlaya, *Two approaches to RH for curves*, Theorem 5.1.5. The modern presentation
  writes the source as `H_l^(p^mu) * H_m^q`, assumes `l * p^mu < q`, identifies it with the
  tensor product, and only then applies Riemann--Roch dimensions:
  `https://kskedlaya.org/weil-cohom/chapter-5.html`.

For the rational curve with its point at infinity, `H_n` is represented by polynomials of degree
at most `n`. The source tensor basis maps into the actual function field `K(t)` by

`e_(i,j) |-> X^(i * pPower + j * q)`.

If `i <= l` and `l * pPower < q`, reduction modulo `q` recovers `i * pPower`, cancellation of
the positive `pPower` recovers `i`, and then cancellation of positive `q` recovers `j`.

## Fixed endpoint

The production module must prove all of the following.

1. Define the source exponent map on
   `Fin (l+1) x Fin (m+1)` by `i * pPower + j * q`.
2. Prove this exponent map injective from `0 < pPower` and `l * pPower < q`.
3. Define a linear polynomial realization by embedding the finite coefficient family at those
   exponents, then define the actual rational realization by the injective algebra map
   `K[X] -> RatFunc K`.
4. Prove exact coefficient recovery at every source exponent.
5. Prove both polynomial and rational realizations injective.
6. Compose rational injectivity with the existing finite-dimensional kernel theorem: whenever
   the descent target has smaller finrank than the source, produce a descent-kernel coefficient
   family whose realized rational function is nonzero.
7. Prove a basis-vector pole certificate using `RatFunc.inftyValuation`, so the output is
   checked in the actual valued function field rather than only through polynomial coefficients.
8. At the equality boundary `l=1`, `pPower=q=1`, construct a nonzero two-term coefficient
   family whose rational realization is zero.

Exact declaration names may follow local style. An implementation through `Finsupp.embDomain`
and `Polynomial.toFinsuppIsoLinear` is allowed, provided TargetChecks expose literal exponent,
coefficient, rational nonzero, valuation, and cancellation statements.

## Falsification tests

- `STRICT_TO_WEAK`: replacing `l * pPower < q` by `<=` must be refuted by the compiled
  equality-boundary collision.
- `ZERO_PPOWER`: no injectivity theorem may omit `0 < pPower`.
- `POLYNOMIAL_ONLY`: a theorem ending in `K[X]` without the `RatFunc K` realization does not
  meet the fixed endpoint.
- `ASSUMED_REALIZATION`: importing injectivity as a premise does not count as success.
- `GENERAL_CURVE_OVERCLAIM`: the rational-curve specialization may not be labeled as the
  general curve polar-expansion theorem.
- `DIMENSION_ONLY`: dimension surplus without proved realization injectivity remains invalid.
- `POINT_COUNT_OVERCLAIM`: no point count, function-field RH, number-field transfer, or RH
  consequence may be claimed.

## Success and classification

Success requires:

- all eight clauses of the fixed endpoint;
- one proven Target and exact positive and negative TargetChecks;
- selected transitive axiom prints containing standard axioms only;
- empty placeholder, custom-declaration, and resource-relaxation scans;
- warning-as-error module, registry, check, and audit compilation;
- a full local build and all public CI gates.

Expected classification:

- `result=RATIONAL_FUNCTION_FIELD_POLAR_REALIZATION_SUCCESS`;
- `historical_route_coverage_delta=1`;
- `actual_function_field_instance_delta=1`;
- `general_curve_polar_lemma_delta=0`;
- `riemann_roch_delta=0`;
- `point_count_delta=0`;
- `number_field_transfer_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No `LeanLab/` or theorem-registration file may be created or edited until this docs-only
preregistration commit passes public Lean Action CI. Local failure after the gate must be logged
with the first exact Lean or mathematical obstruction; it does not stop the persistent RH Goal.

The production gate passed at commit `e0101629812eb788a6d579e6f5d9b02a4db43fb9`, public Lean
Action run `30517894620`, build job `90791696200`, in `1m40s`.

## Local result

`LeanLab/Riemann/BombieriStepanovRationalPolar.lean` compiles the full fixed endpoint. The
actual `RatFunc K` realization is injective under `pPower>0` and `l*pPower<q`, composes with the
finite-dimensional kernel producer, and has exact infinity-valuation certificates. A compiled
nonzero source vector realizes to zero at the equality boundary.

All local gates pass: warning-as-error module/registry/check/audit compilation, six exact
TargetChecks, six selected standard-only axiom prints, empty forbidden scans,
`git diff --check`, and full `8812/8812` build. General curve geometry and every RH-strength
successor remain open.
