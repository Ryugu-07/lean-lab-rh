# Tier 2 Inventory: Gap To The Classical Nyman-Beurling Criterion

Date: 2026-07-10

Target: `T2.nyman.classical.criterion.inventory`

## Inventory Question

How close is the project predicate

```lean
nymanBeurlingConcreteApprox
```

to the classical Nyman-Beurling and Baez-Duarte criteria for the Riemann
hypothesis?

## Sources Checked

- Beurling, "A Closure Problem Related to the Riemann Zeta-Function"
  (`https://doi.org/10.1073/pnas.41.5.312`).
- ESI preprint: "The Nyman-Beurling Equivalent Form for the Riemann Hypothesis"
  (`https://www.esi.ac.at/preprints/esi623.pdf`).
- Baez-Duarte, "A strengthening of the Nyman-Beurling criterion for the Riemann
  Hypothesis" (`https://arxiv.org/pdf/math/0202141`).
- Baez-Duarte, "A general strong Nyman-Beurling Criterion for the Riemann
  Hypothesis" (`https://arxiv.org/abs/math/0505453`).

## Current Project Statement

The project predicate says:

```lean
∀ δ : ℝ, 0 < δ →
  ∃ c : ℝ →₀ ℝ,
    ∫ x : ℝ,
      (1 - c.sum fun a r => r * fractionalPartKernel a x) *
        (1 - c.sum fun a r => r * fractionalPartKernel a x) ∂
          (volume.restrict (Set.Ioo (0 : ℝ) 1)) < δ
```

where

```lean
fractionalPartKernel a x = Int.fract (a / x)
```

This is a concrete finite-approximation property on `L²(0,1)` with arbitrary
real parameters.

## Classical Shapes Found

Beurling's original `L²(0,1)` linear manifold uses finite sums of
fractional-part dilations with `0 < α < 1` and the additional condition
`sum c_k * α_k = 0`. The ESI exposition packages the same restriction by
using modified generators `rho(α / x) - α * rho(1 / x)`.

The Baez-Duarte 2002 paper works in `H = L²(0,∞)`, with

```text
ρ_a(x) = ρ(1 / (a * x)),  a ≥ 1
```

and target `χ_(0,1]`. The same source states the stronger natural-parameter
form where `a ∈ ℕ`.

The 2005 general strong criterion replaces the special indicator target by a
more general pair of functions connected through a co-Poisson or Muntz-type
transform. That is a later structural target, not the next local formal node.

## Formal Gaps

1. Coefficient moment / omitted tail:
   the current restricted project predicate uses raw positive kernels but does
   not require `sum c_k * α_k = 0`. In the Baez-Duarte full-line shape, the
   omitted `(1,∞)` tail has squared norm exactly `(sum c_k * α_k)^2`. This is
   the leading statement mismatch.

2. Parameter domain:
   the current predicate allows every real `a`. The classical unit-interval
   shape uses `0 < α < 1` or `0 < α ≤ 1`; the `L²(0,∞)` Baez-Duarte shape uses
   `a ≥ 1`, equivalently `α = 1 / a`.

3. Natural-parameter strengthening:
   Baez-Duarte's strong form restricts the generating family to natural
   parameters. A Lean version should probably use either `ℕ+` or a finitely
   supported family over positive naturals and then map it into real
   parameters by `n ↦ (n : ℝ)⁻¹`.

4. Domain and target function:
   the project currently works on `volume.restrict (Set.Ioo 0 1)` and
   approximates the constant-one representative. Baez-Duarte's paper uses
   `L²(0,∞)` with the indicator of `(0,1]`. These are related variants, but
   the transfer should be a separate formal bridge if that route is chosen.

5. Closure versus integral-tolerance shape:
   Batch `BATCH-20260710-M0-02` proved that the project restricted concrete
   predicate is equivalent to constant-one membership in the project
   restricted closure. This internal mismatch is closed, but that closure is
   still unconstrained and therefore is not Beurling's published closure.

6. Coefficient field:
   project finite coefficients are real. A source-compatible complex formulation, or a Lean proof
   that real parts preserve approximation quality for the real target and generators, remains to
   be compiled in the selected full-line space.

7. Criterion-to-RH bridge:
   no mathlib theorem currently connects a Nyman-Beurling closure statement to
   `RiemannHypothesis`. Proving that bridge would require substantial analytic
   number theory infrastructure, likely Mellin or Hardy-space machinery.

## Corrected V2 Decision

Do not attempt an RH bridge yet.

The old recommendation to add only a positive support restriction was
insufficient. M0 must next formalize either:

- the unit-interval moment-constrained Beurling approximation statement; or
- the Baez-Duarte positive-natural finite-error statement with the full-line
  tail, equivalently the local error plus squared reciprocal moment.

The latter is closer to the existing positive-natural scaffold. No new local
successor node should be created; this remains work on fixed node M0.

Batch `BATCH-20260710-M0-03` implemented that decision as
`nymanBeurlingBaezDuarteFullLineConcreteApprox`, with the full-line error retained in split integral
form and a Lean theorem reducing it to local error plus squared reciprocal moment. Remaining M0
work is whole-space `Lp` closure packaging and endpoint/coefficient-field alignment.

Batch `BATCH-20260710-M0-04` subsequently compiled the actual real `L2(0,infinity)` target,
generators, span, closure, endpoint bridge, and exact closure/tolerance equivalence. The bounded
coefficient-field/source-convention audit is the remaining M0 item.

Batch `BATCH-20260710-M0-05` subsequently completed that audit by proving real and complex closure
membership equivalent for the source target and generators. M0 is complete; the published RH
equivalence remains M1/G1.
