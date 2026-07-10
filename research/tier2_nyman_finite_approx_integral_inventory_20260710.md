# Tier 2 Nyman-Beurling finite-approximation integral inventory

Date: 2026-07-10

## Question

Can the finite-combination norm approximation

```lean
‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)‖ < ε
```

be moved toward the classical integral-squared form?

## Useful API Found

- `MeasureTheory.L2.inner_def`
  rewrites the `L²` inner product as a Bochner integral of pointwise inner products.

- `InnerProductSpace.norm_sq_eq_re_inner`
  gives `‖f‖ ^ 2 = RCLike.re ⟪f, f⟫`.

- `MeasureTheory.L2.integral_inner_eq_sq_eLpNorm`
  relates the integral of the pointwise self-inner-product to the squared `eLpNorm`.

- `MeasureTheory.Lp.norm_def`
  expresses an `Lp` norm through `eLpNorm`.

## Compiled Bridge Chosen

The smallest robust bridge is the real `L²` self-inner-product route:

```lean
unitIntervalL2_norm_sq_eq_integral_mul_self
```

It proves, for every `f : unitIntervalL2`,

```lean
‖f‖ ^ 2 =
  ∫ x : ℝ, f x * f x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))
```

The finite-combination specialization is:

```lean
norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self
```

## Remaining Gap

The right-hand side still uses the chosen `Lp` representative of

```lean
unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)
```

The next bridge should identify this representative almost everywhere with the concrete finite
sum of representative functions, using `unitIntervalOneL2_coeFn`, `fractionalPartKernelL2_coeFn`,
and `Lp` coercion theorems for finite sums and scalar multiples.

## Rejected Route

Do not directly assert the fully expanded classical integral

```lean
∫ x, (1 - finite_sum_of_fractional_part_kernels x)^2
```

until the almost-everywhere representative bridge for finite sums is compiled.
