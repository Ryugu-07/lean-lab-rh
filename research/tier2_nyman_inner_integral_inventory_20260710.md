# Tier 2 Nyman-Beurling Inner-Integral Inventory

Date: 2026-07-10

## Question

Can the scalar conditions

```lean
⟪fractionalPartKernelL2 a, f⟫_ℝ = 0
```

be rewritten as integral conditions over the restricted unit interval?

## Findings

The relevant mathlib file is:

- `Mathlib/MeasureTheory/Function/L2Space.lean`

Useful API:

- `L2.inner_def`
  rewrites the `L2` inner product as an integral of pointwise inner products.
- `L2.integrable_inner`
  records integrability of the pointwise inner-product function.
- `MemLp.coeFn_toLp`
  identifies the representative of a `MemLp.toLp` package almost everywhere.

For real-valued `L2`, pointwise inner products simplify to ordinary products by `simp`.

## Compiled Bridge

The inventory produced the theorem:

```lean
inner_fractionalPartKernelL2_eq_integral
```

It states:

```lean
⟪fractionalPartKernelL2 a, f⟫_ℝ =
  ∫ x : ℝ, fractionalPartKernel a x * f x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))
```

The proof uses `L2.inner_def`, the almost-everywhere representative theorem
`fractionalPartKernelL2_coeFn`, and real scalar simplification.

## Boundary

This does not prove kernel-span density, the Nyman-Beurling criterion, or any RH implication. It
only moves the scalar orthogonality condition from an abstract `L2` inner product to an integral
against the concrete fractional-part kernel.

## Next Node

Use the bridge theorem to prove an integral form of the density obstruction:

```lean
nymanBeurlingKernelDense ↔
  ∀ f : unitIntervalL2,
    (∀ a : ℝ,
      ∫ x : ℝ, fractionalPartKernel a x * f x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) = 0) →
    f = 0
```
