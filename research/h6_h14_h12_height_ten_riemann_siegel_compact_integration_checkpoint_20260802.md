# Height-ten Riemann--Siegel compact integration checkpoint

Date: 2026-08-02

Parent campaign: `PROOF-ATTEMPT-20260801-H14-H12-HEIGHT-TEN-CERTIFICATE-01`

Subattack: `HEIGHT-TEN-ENDPOINT-COMPACT-INTEGRATION-01`

Status: `MEANINGFUL_PARTIAL / COMPACT_OUTPUTS_CLOSED / TAILS_OPEN / GLOBAL_GOAL_ACTIVE`

## Compiled outputs

The production module
`LeanLab/Riemann/LevinsonMontgomeryHeightTenRiemannSiegelCompactIntegral.lean` proves:

1. `heightTenPositiveCompactExponent_range`;
2. `exp_le_heightTenPositivePolynomial_of_range`;
3. `exp_neg_le_heightTenFourthQuadraticPolynomial`;
4. `integral_heightTenPositiveCompactPolynomialEnvelope_le_sevenTwentieths`;
5. `integral_heightTenNegativeCompactPolynomialEnvelope_le_oneTenth`;
6. `integral_norm_heightTenRiemannSiegelLineIntegrand_one_positiveCompact_le`;
7. `integral_norm_heightTenRiemannSiegelLineIntegrand_one_negativeCompact_le`;
8. `sum_integral_norm_heightTenRiemannSiegelLineIntegrand_one_compact_le_nineTwentieths`.

The last three declarations concern the literal source-contour integrand, not a replacement
model. They certify the actual compact contributions by

```text
positive compact <= 7/20,
negative compact <= 1/10,
combined compact <= 9/20.
```

## Proof shape

The positive exponent is trapped in `[0,7/10]`. Mathlib's Pade bound at one quarter of the
exponent is raised to the fourth power, giving an explicit rational polynomial upper bound.
The negative side uses a separate quadratic upper bound for `exp(-t/4)`, also raised to the
fourth power. Both retain the previously compiled quartic denominator correction.

Lean checks the exact rational coefficients of degree-thirty and degree-twenty envelope
polynomials, verifies explicit primitives by formal differentiation, and evaluates both endpoint
differences exactly. No quadrature or floating-point output is a theorem premise.

## Verification

- standalone production module: warning-as-error pass;
- `Targets.lean`: warning-as-error pass;
- `TargetChecks.lean`: warning-as-error pass;
- `AxiomsAudit.lean`: warning-as-error pass;
- `LeanLab.lean`: warning-as-error pass;
- selected axiom audits: only `propext`, `Classical.choice`, and `Quot.sound`;
- full local build: `8833/8833` jobs;
- patch check: clean.

Frozen implementation commit `687d301d60a4c7bcbae0b4cb36f0a015a94a9b34` passed public Lean Action
run `30723016379`, build job `91429744340`, in `2m38s`.

Three exact polynomial normalization theorems use local `maxHeartbeats 4000000` scopes. Their
corresponding `maxRecDepth` scopes are `1000000`, `100000`, and `100000`. These options do not
escape the individual declarations.

## Exact remaining producer

The full endpoint-mass target is `3/5`. Since the compact contribution is at most `9/20`, the
two remaining tails must be proved to have combined mass at most `3/20`.

This checkpoint does not prove either individual endpoint mass, their total `<=3/5`, the literal
Riemann--Siegel remainder margin, interval nonvanishing, a complete height-ten certificate, H12,
or RH. The parent campaign and global Goal remain active.
