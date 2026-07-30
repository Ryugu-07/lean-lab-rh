# H12 Levinson--Montgomery Jensen Top Zero-Count Result

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-JENSEN-TOP-ZERO-COUNT-01`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / IMMUTABLE_EVIDENCE_PUBLIC_GREEN /
CLOSURE_LEDGER_CI_REQUIRED`

## Result

`LeanLab/Riemann/LevinsonMontgomeryJensenTopZeroCount.lean` is a 1552-line no-sorry
implementation of the preregistered actual-zeta Jensen producer.

For each sufficiently large height, it constructs analytic conjugate-reflection
symmetrizations whose values on the real axis are:

```text
Re(zeta(x+i*t))
```

and

```text
Re(exp(i*t*log 2) * zeta'(x+i*t)).
```

The fixed Jensen geometry has center `20`, inner radius `20`, and outer radius `21`, so the
inner ball contains the complete source interval `[0,1]`.

## Actual growth producer

Lean proves a polynomial bound for actual `riemannZeta` on the full fixed strip swept out by
the required circles. The right side uses Abel continuation. The bounded left side uses the
functional equation, a compiled fixed-strip Gamma ratio estimate, and exact cancellation
between Gamma decay/growth and the cosine factor.

A fixed-radius Cauchy estimate then gives the corresponding polynomial bound for
`deriv riemannZeta`.

## Center separation

At the far-right zeta center, absolute convergence gives a fixed lower bound.

For the derivative, the unnormalized real part rotates with height and cannot have a uniform
lower bound. Multiplication by `exp(i*t*log 2)` fixes the first nonzero Dirichlet term:

```text
-log(2) / 2^20.
```

Lean bounds the norm of the complete remaining tail by `2/3^17`, proves strict dominance, and
derives an explicit fixed lower bound for the phase-normalized center.

## Jensen and crossings

`AnalyticOnNhd.sum_divisor_le` now yields constants `C,T0` such that each actual
multiplicity-bearing divisor sum on the inner ball is at most

```text
C * log(t+2)
```

for every `t>=T0`. Every source real-part crossing on `[0,1]` at `t>=23` is proved to belong to
the support of the corresponding divisor.

## Audit

- strict warning-as-error compilation passes for the production module and exact checks;
- seven exact TargetChecks expose geometry, both real-axis identities, both divisor bounds,
  and both crossing-support endpoints;
- seven selected axiom prints depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- the campaign forbidden scan and `git diff --check` are empty;
- full `lake build` passes `8815/8815` with inherited warnings only.

## Classification

- `result=LEVINSON_MONTGOMERY_ACTUAL_JENSEN_TOP_ZERO_COUNT_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `actual_zeta_top_count_delta=1`;
- `actual_zeta_deriv_top_count_delta=1`;
- `argument_variation_delta=0`;
- `levinson_montgomery_count_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

## Remaining frontier

This result closes the actual local zero-count mechanism compressed into the source's
"standard use of Jensen's theorem." It does not yet turn the ordered real-part crossings into
the continuous top-side argument variation.

The live H12 chain is:

1. crossing count to continuous argument variation;
2. admissible cofinal top heights or the complementary strict-negative branch;
3. finite indented boundary and multiplicity-aware argument principle;
4. the global count identity and `N_1^-(T)=N^-(T)+O(log T)`;
5. the complete Levinson--Montgomery dichotomy and Speiser equivalence.

H12 and RH remain open. The persistent RH Goal remains active.

## Public implementation receipt

Frozen implementation commit `12ddf9bb10f68d3826897bb5403a2ac803da45b0` passed Lean Action
run `30530385387`, build job `90831064393`, in `2m52s`. Immutable evidence is recorded in
`research/h12_levinson_montgomery_jensen_top_zero_count_evidence_20260730.md`.

Docs-only immutable-evidence commit `e1c1364405e0d827f8506d9de302e9f8ffd1d735` passed Lean
Action run `30530768264`, build job `90832307094`, in `1m58s`; the frozen proof and
registration blobs are unchanged.
