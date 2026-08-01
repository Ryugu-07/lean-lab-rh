# Height-ten Riemann--Siegel endpoint tail integration preregistration

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Mode: `PROOF-ATTEMPT / LITERATURE / HISTORICAL-OMISSION-SEARCH`

Status: `PREREGISTERED / ENDPOINT_MASS_OPEN / GLOBAL_GOAL_ACTIVE`

## Exact target statements

For the literal cutoff-one Riemann--Siegel source-line integrand, prove unconditionally in Lean:

```text
integral_{x in Ioi (1/2)} ||I_10(-x)|| <= 19/2000,
integral_{v in Ioc (1/2) 1} ||I_(13/2)(v)|| <= 27/200,
integral_{v in Ioi 1} ||I_(13/2)(v)|| <= 11/2000.
```

These bounds must compose to a combined tail mass `<=3/20`. Together with the compiled compact
mass `<=9/20`, the same module must prove
`HeightTenRiemannSiegelOneEndpointMassBound` and compose it with the existing prefactor phase
theorem to the literal `HeightTenRiemannSiegelOneRemainderMargin`.

The intended downstream witnesses are actual zeta nonvanishing on `13/2<=y<=10` and the actual
strict-negative right-high Speiser quotient sign already supplied by the conditional consumers.

## Decision criterion

Full success requires all of the following:

1. principal-angle lower bounds on `1/2<=v<=1`, `1<=v<=2`, and `2<=v`;
2. actual pointwise source-integrand tail envelopes using the compiled denominator decay;
3. exact proof-producing integration of all three envelopes;
4. actual three-tail integral declarations with the fixed rational budgets;
5. exact set-integral decompositions of both endpoint masses;
6. unconditional `HeightTenRiemannSiegelOneEndpointMassBound`;
7. unconditional composition to the literal remainder margin and actual right-high consumers;
8. warning-as-error compilation, exact TargetChecks, and a standard-only axiom audit.

A model-envelope integral disconnected from the source integrand, a numerical quadrature, or a
conditional endpoint-mass theorem does not count as success.

## Proposed certificates

On `1/2<=v<=1`, set

```text
P0(v) = 87*v/200 + 69*v^2/200 - 11*v^3/200.
```

Writing the exact angle through `pi/4+arctan(z)`, with
`z=(2*sqrt(2)*v-3)/3` in `(-1,0)`, the three-term alternating upper bound for `arctan(-z)` is
intended to prove `P0(v)<=-arg(w(v))`. Rational bounds on `pi` and `sqrt(2)` reduce the remaining
polynomial to a Bernstein-positive certificate.

On `1<=v<=2`, use

```text
P1(v) = 18*v/25 + (v-1)*(2-v)/5.
```

The same recentering splits at the sign of `z`: for `z<=0`, use `z<=arctan(z)`; for `z>=0`, use
the four-term alternating lower bound. Both residual polynomials have positive Bernstein
coefficients. For `v>=2`, prove the simpler constant bound `6/5<=-arg(w(v))`.

After the compiled denominator factor, the selected rational exponents are

```text
q0(v) = 3233*v/2000 - 673*v^2/125 + 143*v^3/400,
q1(v) = -3683*v^2/2000 - 517*v/125 + 13/5.
```

The functions `exp(q0)` and `exp(q1)` are to be proved convex on their fixed intervals. Eight
trapezoids, with node exponentials bounded by scaled quadratic certificates, navigate below
`27/200` and the bounded part of `11/2000`. The unbounded positive and negative tails use exact
linear exponential integrals.

No decimal approximation is admitted as a theorem premise.

## Falsification and rejected candidates

Navigation only, never a proof premise:

- the actual two tails numerically navigate near `0.1203`, below but not far below `3/20`;
- a constant negative-angle bound on the positive half-line integrates far above the budget;
- the compact cubic angle polynomial ceases to be a lower bound near `v=1` and is not extended;
- coarse left Riemann sums need dozens of bins, while eight convex trapezoids retain rational
  margin;
- the selected rational budgets navigate with strict room: negative tail below `19/2000`,
  positive near tail below `27/200`, and positive far tail below `11/2000`.

## Known obstacle and strict limit

The tight point is the positive interval `1/2<=v<=1`; its angle and exponential certificates must
both retain their rational margins. Failure of either certificate triggers route reranking rather
than weakening the fixed budgets after the fact.

Even if the full endpoint mass and right-high vertical zone compile, the left vertical zones,
right low/middle zones, compact-middle top sign, complete rotated-slit boundary, literal
height-ten certificate, H12, and RH remain open. The global Goal remains active.
