# H10 Bombieri--Stepanov Polar Injectivity Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H10-BOMBIERI-STEPANOV-POLAR-INJECTIVITY-01`

Selected node: `H10-E-BOMBIERI-STEPANOV-POLAR-INJECTIVITY-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `LOCAL_SUCCESS / IMPLEMENTATION_CI_REQUIRED`

## Primary-source anchor

The fixed source hinge is:

- Enrico Bombieri, *Counting points on curves over finite fields (d'apres S. A. Stepanov)*,
  Bourbaki 430, pages 236--239. The key lemma proves the natural product realization is an
  isomorphism by separating polar orders before the dimension argument:
  `https://www.numdam.org/item/SB_1972-1973__15__234_0.pdf`;
- Kiran Kedlaya, *Two approaches to RH for curves*, Theorem 5.1.5, especially the
  tensor-product isomorphism, Riemann--Roch dimensions, and nontrivial-kernel criterion:
  `https://kskedlaya.org/weil-cohom/chapter-5.html`.

The source dependency is:

```text
polar-order separation
  -> injective realization of the product/tensor source
  -> source dimension greater than descent-target dimension
  -> nonzero descent-kernel vector
  -> nonzero realized auxiliary with zero descent.
```

The previous campaign begins only after the last arrow: given zero descent and a nonzero
polynomial base, it proves rational-point vanishing, high root multiplicity, and the degree
budget. This campaign fixes the missing nonzero-production logic.

## Exact fixed endpoint

The production module must prove all of the following.

1. For finite-dimensional vector spaces `U,W` over a field, if
   `finrank W < finrank U`, every linear map `delta : U -> W` has a nonzero kernel vector.
2. If `realize : U -> F` is injective, the kernel vector can be chosen with
   `realize u != 0`.
3. Construct a coefficient-block linear equivalence
   from `Fin n -> Polynomial.degreeLT K q` to
   `Polynomial.degreeLT K (n*q)`. This is the fixed polynomial analogue of polar-order
   separation: each block occupies its own coefficient interval.
4. Use that equivalence as the realization map and prove a source-shaped theorem:
   if a descent target has finrank less than `n*q`, there exists a descent-kernel block family
   whose realized polynomial is nonzero.
5. Compile a finite countermodel in which `finrank W < finrank U` but a noninjective realization
   kills every vector in the descent kernel. Dimension surplus alone must not imply a nonzero
   realized auxiliary.
6. Compile a small positive witness for the block realization, without `native_decide`, showing
   two nonzero coefficient blocks remain nonzero after realization.

Exact declaration names may follow local style. Clause 3 may use a coefficient-reindexing linear
equivalence rather than a handwritten sum, but exact block coefficient checks are required in
`TargetChecks.lean`.

## Proposed Lean surface

```lean
theorem exists_ne_zero_mem_ker_of_finrank_lt ...
theorem exists_descent_zero_realize_ne_zero_of_finrank_lt ...

def stepanovPolarBlockEquiv ...

theorem exists_stepanovPolarBlock_ne_zero_mem_ker ...
theorem stepanovDimensionSurplus_not_enough_without_injective ...
theorem stepanovPolarBlock_two_witness ...
```

## Falsification tests

- `REALIZATION_CANCELLATION`: dimension surplus without injective realization must fail.
- `ZERO_BLOCK_WIDTH`: no positive-dimensional conclusion may be smuggled through `q=0`.
- `ZERO_BLOCK_COUNT`: no nonzero source may be inferred when `n=0`.
- `DIMENSION_DIRECTION`: equality of source and target finranks is insufficient.
- `ACTUAL_CURVE_BOUNDARY`: the coefficient-block equivalence is not the curve polar-expansion
  theorem and may not be labeled as such.
- `POINT_COUNT_BOUNDARY`: no point-count or RH consequence may be inferred without importing the
  previous nonzero auxiliary theorem and the still-missing curve inputs.

## Success and classification

Success requires:

- every exact endpoint above;
- one proven Target and exact TargetChecks for generic, positive, and negative cases;
- selected transitive axiom prints with standard axioms only;
- empty placeholder, custom-declaration, and resource-relaxation scans;
- warning-as-error production compilation, full build, and all public CI gates.

Expected classification:

- `result=SOURCE_NONCANCELLATION_GATE_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `source_logic_bridge_delta=1`;
- `actual_curve_polar_lemma_delta=0`;
- `curve_theorem_delta=0`;
- `number_field_transfer_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI. Local STOP returns the active global Goal to `ROUTE_SELECTION`.

The production gate passed at preregistration commit
`e4efd3e2c6a2c2cae983b1d3224a8780aaa88f1c`, public Lean Action run `30205991741`,
build job `89804024442`, in `2m15s`.

## Local result

`LeanLab/Riemann/BombieriStepanovPolarInjectivity.lean` is a 174-line no-sorry
implementation of the fixed endpoint. It proves:

- dimension surplus gives a nonzero descent-kernel vector;
- injective realization turns that vector into a nonzero auxiliary;
- finite polynomial coefficient blocks form a linear equivalence with one larger
  degree-bounded polynomial space, with exact coefficient transport;
- the source-shaped dimension-surplus theorem for that block realization;
- a rational two-dimensional countermodel where the descent kernel is nonzero but a
  noninjective realization kills all of it;
- a two-block positive witness with two certified nonzero output coefficients.

The proven Target, six exact TargetChecks, six selected axiom prints, warning-as-error
production/registry/check/audit compilation, empty forbidden scans, and full `8770/8770` build
pass locally. Every selected theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

The countermodel shows that the source's polar/tensor injectivity premise is logically
indispensable. No hidden shortcut from Riemann--Roch dimension surplus directly to a nonzero
function survives this audit. The actual curve polar-order theorem and its possible number-field
analogue remain open.

Local classification:

- `result=SOURCE_NONCANCELLATION_GATE_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `source_logic_bridge_delta=1`;
- `actual_curve_polar_lemma_delta=0`;
- `curve_theorem_delta=0`;
- `number_field_transfer_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.
