# Tier 2 Inventory: Nyman-Beurling / Baez-Duarte Route

Date: 2026-07-09

Target: `T2.inventory.nyman.beurling`

## Inventory Question

Does the current local project plus mathlib have enough `L2`, closure/density, step-function, and
fractional-part infrastructure to state useful Nyman-Beurling or Baez-Duarte route nodes?

## Useful Infrastructure Found

- `L2` and Hilbert-space structure:
  - `Lp E p μ`
  - `MemLp.toLp`
  - `Lp.memLp`
  - `memLp_two_iff_integrable_sq`
  - `memLp_two_iff_integrable_sq_norm`
  - `L2.inner_def`
  - `L2.integrable_inner`
  - `L2.innerProductSpace`
- Indicator functions inside `Lp`:
  - `indicatorConstLp`
  - `indicatorConstLp_coeFn`
  - `norm_indicatorConstLp`
  - `indicatorConstLp_univ`
  - `L2.inner_indicatorConstLp_one`
  - `L2.inner_indicatorConstLp_one_indicatorConstLp_one`
- Dense simple-function infrastructure:
  - `Lp.simpleFunc`
  - `SimpleFunc.toLp`
  - `Lp.simpleFunc.denseRange`
  - `Lp.simpleFunc.dense`
  - `Lp.simpleFunc.induction`
  - `MemLp.exists_simpleFunc_eLpNorm_sub_lt`
  - `MemLp.induction_dense`
- Continuous functions dense in `Lp`:
  - `BoundedContinuousFunction.toLp_denseRange`
  - `ContinuousMap.toLp_denseRange`
  - `Lp.boundedContinuousFunction_dense`
- Interval and finite-measure support:
  - `measurableSet_Ioo`
  - `Real.volume_Ioo`
  - `Real.volume_real_Ioo`
  - `isFiniteMeasure_restrict_Ioo`
  - `MeasureTheory.isFiniteMeasure_restrict`
- Fractional-part API:
  - `Int.fract`
  - `Int.fract_nonneg`
  - `Int.fract_lt_one`
  - `Int.fract_eq_self`
  - `Int.fract_add_intCast`
  - `Int.fract_div_natCast_eq_div_natCast_mod`
  - `Int.measurable_floor`
  - `measurable_fract`
  - `Measurable.fract`
  - `continuousOn_fract`
  - `ContinuousOn.comp_fract`
- Closure and orthogonality infrastructure for Hilbert subspaces:
  - `Submodule.topologicalClosure_eq_top_iff`
  - `Submodule.orthogonal_eq_bot_iff`
  - `Submodule.orthogonal_orthogonal_eq_closure`
  - `Submodule.orthogonal_closure`

## Missing Pieces For A Direct Criterion Statement

- No direct mathlib statement of the Nyman-Beurling criterion was found.
- No direct mathlib statement of the Baez-Duarte strengthening was found.
- No project-local definition yet exists for the standard fractional-part basis functions, for
  example a function of the shape `x ↦ Int.fract (a / x)` on an interval or half-line.
- No compiled proof yet shows that those fractional-part basis functions belong to the chosen
  `L2` space. This should be the first formal proof node if the route is selected.
- No project-local submodule has yet been defined for the span of the Nyman-Beurling functions.
- No bridge exists from density of that submodule to mathlib's `RiemannHypothesis`.
- The Baez-Duarte arithmetic sequence formulation would also need separate number-theoretic
  definitions and asymptotic estimates; this inventory did not find a ready high-level API for it.

## Recommendation

Prefer this route over Li/Hadamard for the immediate Tier 2 pivot.

This is not because the Nyman-Beurling criterion is already formalized. It is not. The reason is
more practical: the first missing steps are low-level and Lean-sized. A first proof loop can define
one bounded fractional-part function on `(0, 1)` and prove it is measurable and in `L2` with respect
to `volume.restrict (Set.Ioo 0 1)`.

Suggested next proof-engineering nodes:

- define a local fractional-part kernel on `(0, 1)`;
- prove boundedness using `0 ≤ Int.fract _` and `Int.fract _ < 1`;
- prove measurability using `Measurable.fract` away from the division-by-zero endpoint;
- prove a first `MemLp ... 2 (volume.restrict (Set.Ioo 0 1))` theorem;
- define the span submodule only after several basis functions are available as `Lp` elements.

Next route: close `T2.pivot` by choosing the Nyman-Beurling foundation route.
