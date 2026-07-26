# H10 Bombieri--Stepanov Frobenius Auxiliary Preregistration

Date: 2026-07-26

Campaign: `LITERATURE-20260726-H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01`

Selected node: `H10-BOMBIERI-STEPANOV-FROBENIUS-AUXILIARY-01`

Mode: `LITERATURE / FALSIFICATION`

Status: `IMPLEMENTATION_PUBLIC_GREEN / IMMUTABLE_EVIDENCE_REQUIRED`

## Primary-source anchor

The fixed source mechanism is the auxiliary-function construction in:

- S. A. Stepanov, *On the number of points of a hyperelliptic curve over a finite prime
  field* (1969), especially the construction of a nonzero polynomial with high-multiplicity
  roots and the final degree count:
  `https://www.mathnet.ru/eng/im2197`;
- Enrico Bombieri, *Counting points on curves over finite fields (d'apres S. A. Stepanov)*
  (Bourbaki 430, 1973):
  `https://www.numdam.org/item/SB_1972-1973__15__234_0.pdf`;
- Kiran Kedlaya, *Two approaches to RH for curves*, Theorem 5.1.5 and its proof:
  `https://kskedlaya.org/weil-cohom/chapter-5.html`.

Bombieri writes `f = sum_i nu_i s_i^q`, with `nu_i` in a `p^mu`-power subspace, and imposes
`delta(f)=sum_i nu_i s_i=0`. At rational points `s_i^q=s_i`; because `p^mu` divides `q`, the
auxiliary is a perfect `p^mu`-th power and every zero has multiplicity at least `p^mu`.

## Exact fixed endpoint

Let `K` be a finite field of characteristic `p`, let `mu > 0`, put `m=p^mu`, and assume
`r*m=Fintype.card K`. For a finite family of polynomials `v_i,s_i`, define

```text
B     = sum_i v_i * s_i^r
delta = sum_i v_i^m * s_i
F     = B^m.
```

The campaign must prove all of the following.

1. `F = sum_i v_i^m * s_i^(r*m)` by finite Frobenius additivity.
2. For every `a : K`, `eval a F = eval a delta`.
3. If `delta=0`, then every `a : K` is a root of `F`.
4. If additionally `B != 0`, every `a : K` has root multiplicity at least `m` in `F`.
5. For every finite set of distinct roots with multiplicity at least `m`,
   `m * card(S) <= natDegree(F)`.
6. Hence the full finite field satisfies
   `card(K) <= natDegree(F)/m`; record the equivalent bound before division as well.
7. Compile a saturated `ZMod 2` witness with
   `B=X+X^2`, `delta=0`, and `F=(X+X^2)^2`, checking the two field points and their
   multiplicities without `native_decide`.

The exact declaration names may follow local style, but no clause may be weakened to a bare
evaluation identity or a root-without-multiplicity statement.

## Proposed Lean surface

```lean
def stepanovFrobeniusBase ...
def stepanovFrobeniusDescent ...
def stepanovFrobeniusAuxiliary ...

theorem stepanovFrobeniusAuxiliary_eq_sum ...
theorem stepanovFrobeniusAuxiliary_eval_eq_descent ...
theorem stepanovFrobeniusAuxiliary_rootMultiplicity ...
theorem finset_card_mul_le_natDegree_of_rootMultiplicity ...
theorem stepanovFrobenius_card_le_natDegree_div ...

theorem stepanovFrobenius_zmodTwo_descent ...
theorem stepanovFrobenius_zmodTwo_saturated ...
```

## Source alignment and unavailable inputs

Available in the pinned tree:

- `FiniteField.pow_card`;
- characteristic-`p` finite-sum Frobenius identities `sum_pow_char_pow`;
- polynomial evaluation, powers, roots, and `rootMultiplicity`;
- `Polynomial.hasseDeriv` and Taylor coefficients for cross-checking multiplicity;
- finite root multisets and the degree bound.

Explicitly outside this campaign:

- function fields and rational functions on a smooth projective curve;
- Riemann--Roch dimensions for the spaces `H_l` and `H_m`;
- the polar-expansion proof that the source multiplication map is a tensor-product isomorphism;
- production of a nonzero kernel element with the optimized pole budget;
- the lower point-count argument through Galois covers;
- curve zeta rationality, functional equation, and the already separately formalized finite
  spectral-rigidity conclusion;
- any number-field Frobenius/cohomology object or regularized infinite-spectrum transfer.

These may not be hidden in typeclasses, custom axioms, or a strengthened nonzero hypothesis.

## Falsification tests

- `NONZERO_KERNEL`: exhibit that `delta=0` alone does not syntactically guarantee `B!=0`; keep
  nonzero kernel production explicit.
- `CARDINAL_EXPONENT`: drop `r*p^mu=card(K)` and check that rational-point evaluation transport
  is no longer available.
- `CHARACTERISTIC_ZERO`: do not generalize Frobenius finite-sum additivity to characteristic zero.
- `MU_ZERO`: record that `mu=0` gives no high-multiplicity gain.
- `MULTIPLICITY_LOSS`: reject any proof that counts only distinct roots and loses the factor
  `p^mu`.
- `SATURATION`: the `ZMod 2` witness must attain the degree/multiplicity budget, preventing a
  fictitious strict improvement from this algebra alone.

## Success and classification

Success requires:

- every endpoint theorem above;
- one proven Target and exact TargetChecks including the saturated witness;
- selected transitive axiom prints with standard axioms only;
- empty placeholder, custom-declaration, and resource-relaxation scans;
- warning-as-error production compilation, full build, and all public CI gates.

Expected classification:

- `result=KNOWN_FUNCTION_FIELD_MECHANISM_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `source_algebra_bridge_delta=1`;
- `curve_theorem_delta=0`;
- `number_field_transfer_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

Frozen implementation commit `61bb73ad666e3bdd4ba460bedd93af16256c997d` passed public Lean
Action run `30205411443`, build job `89802493185`, in `2m31s`. Lean proof source is frozen;
the next gate is a docs-only immutable-evidence commit and public CI.

## Production gate

No production Lean source may be created or edited until this docs-only preregistration passes
public Lean Action CI. Local STOP returns the active global Goal to `ROUTE_SELECTION`.

The production gate passed at preregistration commit
`44ecd3bcda10a2687d3eac965c312a00ce90007b`, public Lean Action run `30204699920`,
build job `89800633257`, in `1m53s`.

## Local result

`LeanLab/Riemann/BombieriStepanovFrobeniusAuxiliary.lean` is a 264-line no-sorry
implementation of the fixed endpoint. It proves:

- the finite Frobenius expansion and rational-point descent identity;
- the perfect-power root-multiplicity lower bound with nonzero base kept explicit;
- the multiplicity-weighted finite-root degree budget and full-cardinality quotient bound;
- a nonzero `ZMod 2` descent-kernel witness whose roots at `0` and `1` both have exact
  multiplicity `2`, with `2 * card (ZMod 2) = natDegree F = 4`.

The proven Target, seven exact TargetChecks, six selected axiom prints, warning-as-error
production/registry/check/audit compilation, empty forbidden scans, and full `8769/8769` build
pass locally. Every selected theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`.

The saturated witness rules out a strict improvement from Frobenius descent plus root
multiplicity alone. It does not close the function-field route: Riemann--Roch dimensions,
polar/tensor injectivity, optimized nonzero kernel production, pole-divisor control, the lower
point-count construction, number-field transfer, and RH remain open.

Local classification:

- `result=KNOWN_FUNCTION_FIELD_MECHANISM_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `source_algebra_bridge_delta=1`;
- `curve_theorem_delta=0`;
- `number_field_transfer_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.
