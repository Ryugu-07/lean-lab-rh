# H10 Bombieri--Stepanov Rational Polar Realization Result

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H10-BOMBIERI-STEPANOV-RATIONAL-POLAR-REALIZATION-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_CI_REQUIRED`

## Result

`LeanLab/Riemann/BombieriStepanovRationalPolar.lean` is a 202-line no-sorry
implementation of the preregistered endpoint.

For source indices

`(i,j) in Fin (l+1) x Fin (m+1)`,

Lean defines the polar exponent

`i * pPower + j * q`.

If `pPower>0` and `l*pPower<q`, division by `q` first recovers `j`: the residual term
`i*pPower` is strictly below `q`. Positive multiplication cancellation then recovers `i`.
No coprimality assumption on `pPower` and `q` is used.

The finite coefficient family is embedded at these exponents in `K[X]` and then mapped through
the injective algebra map into `RatFunc K`. Lean proves:

- injectivity of the source exponent map;
- exact polynomial coefficient recovery at every source exponent;
- injectivity of the polynomial realization;
- injectivity of the actual rational-function realization;
- a finite-dimensional descent map with smaller target finrank has a kernel vector whose
  rational realization is nonzero;
- a basis vector has infinity valuation exactly
  `WithZero.exp (i*pPower+j*q)`.

## Sharp negative control

At `l=1` and `pPower=q=1`, the distinct indices `(1,0)` and `(0,1)` both map to exponent one.
Lean constructs their coefficient difference, proves that source vector is nonzero, and proves
its rational realization is exactly zero. Thus the source's strict separation condition cannot
be weakened to equality in this realization.

## Audit

- warning-as-error compilation passes for the module, `Targets.lean`, `TargetChecks.lean`, and
  `AxiomsAudit.lean`;
- six exact campaign TargetChecks pass;
- six selected transitive axiom prints depend only on `propext`, `Classical.choice`, and
  `Quot.sound`;
- placeholder, custom `axiom`/`constant`, and resource-relaxation scans are empty;
- `git diff --check` is empty;
- full `lake build` passes `8812/8812`, with only inherited warnings outside the new module.

## Classification

- `result=RATIONAL_FUNCTION_FIELD_POLAR_REALIZATION_SUCCESS`;
- `historical_route_coverage_delta=1`;
- `actual_function_field_instance_delta=1`;
- `strict_source_condition_sharpness_delta=1`;
- `general_curve_polar_lemma_delta=0`;
- `riemann_roch_delta=0`;
- `point_count_delta=0`;
- `number_field_transfer_delta=0`;
- `rh_frontier_delta=0`.

## Remaining frontier

This result replaces the prior polynomial coefficient-block analogy with an actual valued
function-field instance, but only for the rational curve. The next general-curve producer is a
one-point pole filtration with:

1. bases ordered by distinct pole orders;
2. Frobenius pullback multiplying those orders by `q`;
3. the theorem that a function with no poles is constant, so a nonzero positive-order remainder
   cannot occur;
4. Riemann--Roch dimensions large enough to produce the descent kernel.

The first three clauses constitute the general curve polar-injectivity argument; the fourth is
the separate dimension producer. None is supplied by this result. The Bombieri--Stepanov point
count, its lower-bound Galois step, function-field RH composition, number-field transfer, H10,
and RH remain open.

## Public implementation receipt

Frozen implementation commit `97b055c30194e61853820ab263d949fd49cc12de` passed Lean Action
run `30518731227`, build job `90794240899`, in `2m37s`. The immutable evidence file is
`research/h10_bombieri_stepanov_rational_polar_evidence_20260730.md`; its docs-only commit and
public CI remain required.
