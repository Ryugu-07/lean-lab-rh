# Tier 2 Nyman-Beurling restricted finite-approximation integral inventory

Date: 2026-07-10

## Question

Can the existing `unitIntervalL2` norm-square-to-integral bridge be reused for
subtype-indexed restricted finite kernel sums?

The target expression is:

```lean
‖unitIntervalOneL2 -
    (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ ^ 2
```

for `c : nymanBeurlingRestrictedParameterSet →₀ ℝ`.

## Useful API Found

- `unitIntervalL2_norm_sq_eq_integral_mul_self`
  already proves the norm-square-to-integral bridge for every `f : unitIntervalL2`.

- The subtype-indexed restricted finite sum is still an element of `unitIntervalL2`, so no new
  measure-theoretic API is needed for the first bridge.

## Compiled Bridge Chosen

The restricted finite-sum specialization is:

```lean
norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self
```

It proves:

```lean
‖unitIntervalOneL2 -
    (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ ^ 2 =
  ∫ x : ℝ,
    (unitIntervalOneL2 -
        (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))) x *
      (unitIntervalOneL2 -
        (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))) x ∂
        (volume.restrict (Set.Ioo (0 : ℝ) 1))
```

## Remaining Gap

The integral still uses the selected `Lp` representative. The next bridge should identify the
restricted finite sum almost everywhere with:

```lean
fun x : ℝ => c.sum fun a r => r * fractionalPartKernel (a : ℝ) x
```

and then identify the constant-one difference with the corresponding concrete squared-error
integrand.

## Rejected Route

Do not jump directly to the fully concrete integral until the restricted finite-sum representative
bridge has been compiled.
