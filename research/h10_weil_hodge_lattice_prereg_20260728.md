# H10 Weil Surface Hodge-Lattice Preregistration

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H10-WEIL-HODGE-LATTICE-01`

Node: `H10-WEIL-SURFACE-HODGE-LATTICE-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED_LOCAL / PUBLIC_CI_REQUIRED`

## Primary-source anchor

The fixed source is Kiran Kedlaya, *Two approaches to RH for curves*, Section 5.2, especially
Theorem 5.2.2, Lemma 5.2.3, the diagonal/Frobenius intersection table, and the final quadratic
form:

`https://kskedlaya.org/weil-cohom/chapter-5.html#section-5-2-rh-via-surfaces`

The source dependency is:

```text
Hodge index on X x X
  -> nonnegativity for every integral divisor a*Gamma+b*Delta
  -> semipositivity of the associated real binary quadratic form
  -> Hasse--Weil point-count bound over every extension
  -> all-power Frobenius trace bound
  -> reciprocal spectral circle.
```

The repository already proves the last finite-spectral implication from an all-power norm bound
and reciprocal pairing. It does not contain the first four surface/Hodge interfaces.

## Exact fixed endpoint

The production module must prove all of the following without `sorry`.

1. Define the source-normalized real quadratic form

```text
hodgeForm(q,g,N,a,b)
  = 2 * (g*q*a^2 + (q+1-N)*a*b + g*b^2).
```

2. Prove its equality with the expanded intersection expression from the source.
3. Prove that nonnegativity on every integer pair implies nonnegativity on every rational pair
   by common-denominator homogeneity.
4. Prove that rational-pair nonnegativity implies real-pair nonnegativity by density and
   continuity.
5. For `q>0` and `g>=0`, prove that real-pair nonnegativity implies
   `abs (N-(q+1)) <= 2*g*sqrt(q)`.
6. Deduce the same point-count bound directly from integer-lattice nonnegativity.
7. Prove a source-composed finite-spectrum theorem: extension-wise integer-lattice
   inequalities for the point-count expression, real power sums, and reciprocal pairing imply
   that every spectral norm is `sqrt(q)`. The `n=0` power sum must be handled explicitly rather
   than read as a geometric extension count.
8. Compile a finite-box negative control: one explicit homogeneous quadratic form is
   nonnegative on all coefficient pairs in `{-1,0,1}^2` but negative at `(1,2)`.

Exact declaration names may follow local style. The aggregate endpoint must include only proved
declarations.

## Success criteria

`FULL_SOURCE_NUMERICAL_HINGE_SUCCESS` requires all eight clauses, one registered Target, exact
TargetChecks, selected transitive axiom prints with standard axioms only, empty forbidden scans,
warning-as-error compilation, a full build, and every public CI gate.

`MEANINGFUL_PARTIAL` requires clauses 1--6 and 8, with clause 7 left as an exact theorem-shaped
open edge.

`FALSIFIED` applies if integer-lattice nonnegativity does not imply the claimed real
semipositivity or point-count bound under the registered hypotheses.

## Negative controls and claim boundary

- `FINITE_BOX`: checking only finitely many divisor coefficients cannot certify
  semipositivity.
- `GENUS_ZERO`: the conclusion must collapse to `N=q+1`.
- `Q_POSITIVITY`: square-root and minimization steps require `q>0`.
- `SIGN_CONVENTION`: the cross term is `q+1-N`; replacing it by `N-q-1` must not change the
  absolute final bound but must be tracked in intermediate identities.
- `INTEGER_TO_REAL`: no real-coefficient Hodge premise may be silently assumed.
- `POWER_SUM_REALITY`: a bound on the real part of a complex power sum is not a norm bound
  without a compiled reality hypothesis.
- `N_ZERO`: the rigidity theorem's zeroth power sum is algebraic bookkeeping, not a source
  point-count estimate.
- `ACTUAL_GEOMETRY`: no actual intersection pairing, Hodge index theorem, curve point count,
  H10, number-field transfer, or RH result is claimed.

Expected classification:

- `historical_route_coverage_delta=1`;
- `integer_lattice_bridge_delta=1`;
- `source_numerical_hinge_delta=1`;
- `actual_curve_geometry_delta=0`;
- `number_field_transfer_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source, Target, TargetCheck, or axiom-audit entry may be created or edited
until this docs-only preregistration passes public Lean Action CI.

The persistent RH Goal remains active. A local stop returns to fresh cross-family route
selection after the full evidence chain.
