# Height-ten Riemann--Siegel compact endpoint integration preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Mode: `PROOF-ATTEMPT / LITERATURE / HISTORICAL-OMISSION-SEARCH`

Status: `PREREGISTERED / ENDPOINT_MASS_OPEN / GLOBAL_GOAL_ACTIVE`

## Target statements

On the two compact pieces of the fixed cutoff-one Riemann--Siegel endpoint contours, prove
unconditionally in Lean that

```text
integral_{v in (0,1/2]} ||I_(13/2)(v)|| <= 7/20,
integral_{x in (0,1/2]} ||I_10(-x)|| <= 1/10.
```

The intended Lean statements use `Set.Ioc (0 : Real) (1 / 2)` and the literal
`deBruijnNewmanRiemannSiegelLineIntegrand` from the source contour. They must compose with the
existing endpoint masses without replacing the actual integrand by a new definition.

## Decision criterion

Success requires all of the following in one production module:

1. a kernel-checked positive-compact exponent range `0 <= q(v) <= 7/10`;
2. a proof-producing rational polynomial upper bound for `exp(q(v))`;
3. a proof-producing rational polynomial upper bound for the negative compact exponential;
4. the actual quartic denominator suppression transferred to a rational coefficient using the
   compiled lower bound `111/50 <= pi*sqrt(2)/2`;
5. exact interval integrals of both polynomial envelopes;
6. the two stated rational compact-mass bounds;
7. warning-as-error compilation and an axiom audit with no new nonstandard axiom.

A generic exponential inequality, a polynomial integral disconnected from the literal endpoint
integrand, or a numerical approximation does not count as success.

## Proposed certificates

For

```text
q(v) = 361*v/100 - 2063*v^2/450 - 13*v^3/36,
t(x) = 39*x/20 + 28849*x^2/6000,
```

use

```text
exp(q) <= (1 + q/4 + (40/73)*(q/4)^2)^4,
exp(-t) <= (1 - t/4 + (t/4)^2/2)^4.
```

The first follows by applying Mathlib's Padé bound to `q/4 <= 7/40` and raising to the fourth
power. The second follows from the quadratic Taylor upper bound for `exp(-u)` and the identity
`exp(-t) = exp(-t/4)^4`. The denominator correction uses the rational coefficient

```text
(29/100)*(2/3)*(111/50)^4.
```

No decimal approximation is admitted as a theorem premise.

## Falsification and rejected candidates

Navigation only, never a proof premise:

- dropping the quartic denominator correction gives a compact total near `0.46946`, so it cannot
  support the required endpoint budget;
- ten or twenty piecewise-constant bins remain above `0.45` under rigorous-direction rounding;
- the unscaled generic quadratic exponential bound is too weak on the negative compact side;
- the selected fourth-power certificates navigate near `0.34394` and `0.09904`, leaving rational
  margins below `7/20` and `1/10` for an exact Lean check.

## Known obstacle and strict limit

Even if both compact bounds compile, the full proposition
`HeightTenRiemannSiegelOneEndpointMassBound` remains open until the two tails outside
`abs(v) <= 1/2` have total mass at most `3/20`. This campaign may not claim either individual
endpoint mass, total endpoint mass `<=3/5`, the height-ten remainder margin, H12, or RH from the
compact result alone.
