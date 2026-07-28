# H10 Weil Surface Hodge-Lattice Result

Date: 2026-07-28

Campaign: `LITERATURE-20260728-H10-WEIL-HODGE-LATTICE-01`

Result: `FULL_SOURCE_NUMERICAL_HINGE_SUCCESS`

## Compiled result

The source-normalized form

```text
2 * (g*q*a^2 + (q+1-N)*a*b + g*b^2)
```

is proved equal to the expanded diagonal/Frobenius intersection expression. If it is
nonnegative for every integer pair `(a,b)`, common-denominator homogeneity makes it
nonnegative on rational pairs, and rational density plus continuity makes it nonnegative on
the full real plane.

Testing at `(2*g,N-(q+1))`, with genus zero handled separately, gives

```text
|N-(q+1)| <= 2*g*sqrt(q).
```

For a finite complex spectrum, extension-wise integer-lattice inequalities applied to

```text
N_n = q^n + 1 - Re(sum_i alpha_i^n)
```

together with real power sums and reciprocal pairing imply

```text
norm(alpha_i) = sqrt(q)
```

for every spectral member. The zeroth power sum is bounded separately by the spectrum
cardinality.

## Negative control

The homogeneous form

```text
(b-2*a)^2-a^2/2
```

is nonnegative at every integer pair in `{-1,0,1}^2`, but its value at `(1,2)` is `-1/2`.
Finite coefficient testing therefore cannot certify the universal Hodge lattice premise.

## Strongest declarations

- `weilHodgeForm_eq_intersectionExpression`
- `weilHodgeForm_nonneg_rat_of_int`
- `weilHodgeForm_nonneg_real_of_int`
- `abs_pointCount_sub_le_of_weilHodgeForm_nonneg_int`
- `norm_eq_sqrt_of_weilHodge_lattice_extensions`
- `finiteHodgeBoxModel_nonneg_of_abs_le_one`
- `finiteHodgeBoxModel_one_two_neg`
- `weilHodgeLattice_endpoint`

## Mechanical audit

- production module: 243 lines;
- standalone and warning-as-error compiles: pass;
- one Target and seven exact TargetChecks: pass;
- seven selected axiom prints: only `propext`, `Classical.choice`, `Quot.sound`;
- forbidden/custom-declaration/resource-relaxation scans: empty;
- `git diff --check`: pass;
- full build: `8783/8783`;
- preregistration: `3c8742a23b6b955fa4ea976fd860593d6e052c27`, run `30383689739`,
  job `90357535402`, passed in `2m32s`;
- frozen implementation: `a97593c3609ec6ec3e1a699132c849dffd68a41c`;
- public implementation CI: run `30384610038`, job `90360629352`, passed in `3m1s`;
- proof freeze: empty `LeanLab/` diff from the frozen implementation;
- immutable evidence: `c4fef4621dbed9831a38a5774587672122d45dfd`, run `30384971222`,
  job `90361859234`, passed in `2m3s`;
- final ledger: pending.

## Claim boundary

This closes the numerical hinge and finite-spectral composition in a known function-field
proof. It does not instantiate an actual curve, construct its intersection pairing, prove the
Hodge index theorem, identify Frobenius intersections with point counts, construct a
number-field transfer object, prove H10, or prove RH. The persistent RH Goal remains active.
