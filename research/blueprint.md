# RH Blueprint

Date: 2026-07-09

This blueprint is a working DAG for the RH proof-engineering project. It is not a claim that the
RH proof is near. It is a guardrail: loops should fill these nodes, reduce the target ledger, or
record why a route is blocked by missing infrastructure.

## Tier 1: Local Xi and Li Scaffold Deliverable

### T1.xi.completed.bridge

Informal statement:

Relate the project-local
`riemannXi s = s * (s - 1) / 2 * completedRiemannZeta0 s + 1 / 2`
to the standard completed zeta expression away from the pole-removal points.

Dependencies:

- mathlib definition and identities for `completedRiemannZeta`;
- existing local definition `riemannXi`;
- edge conditions `s != 0`, `s != 1`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved as `riemannXi_eq_mul_completedRiemannZeta`.

Result:

- local inventory found `completedRiemannZeta_eq`;
- clearing the two pole-removal terms under `s != 0` and `s != 1` proves the bridge.

Next action:

- use this bridge to split `T1.xi.zero.bridge` into precise zero-correspondence statements.

### T1.xi.zero.bridge

Informal statement:

Give a precise correspondence between zeros of `riemannXi` and the project predicate
`IsNontrivialZero`, including the behavior at trivial zeros and pole-removal points.

Dependencies:

- T1.xi.completed.bridge;
- `LeanLab/Riemann/Basic.lean` predicates;
- mathlib trivial-zero and nonzero-in-right-half-plane theorems;
- local value lemmas for `riemannXi`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved as `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial`.

Subnodes:

- `T1.xi.zero.bridge.forward.safe`: proved as `isZetaZero_of_riemannXi_eq_zero`.
  If `s != 0`, `s != 1`, and `riemannXi s = 0`, then `IsZetaZero s`.
- `T1.xi.zero.bridge.reverse.gamma`: proved as
  `riemannXi_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero`. If `s != 0`, `s != 1`,
  `Gammaℝ s != 0`, and `IsZetaZero s`, then `riemannXi s = 0`.
- `T1.xi.zero.bridge.gamma.edge`: proved as
  `eq_zero_or_isTrivialZeroPoint_of_Gammaℝ_eq_zero` and
  `Gammaℝ_ne_zero_of_isNontrivialZero`.
- `T1.xi.zero.bridge.reverse.nontrivial`: proved as
  `riemannXi_eq_zero_of_isNontrivialZero`.
- `T1.xi.zero.bridge.nontrivial`: proved as
  `isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial`. This packages the edge cases into
  `IsNontrivialZero`, with `¬ IsTrivialZeroPoint s` explicit on the `riemannXi` side.

Next action:

- this target is closed. The downstream Tier 1 coefficient and scaffold-note targets are also
  closed, so the next research loop should move to Tier 2 inventory.

### T1.li1.positivity

Informal statement:

Finish positivity of the second local Li candidate:
`0 < (liCoefficientCandidate 1).re`.

Dependencies:

- existing real-valued formula for `liCoefficientCandidate 1`;
- a usable estimate or structural formula for `(deriv completedRiemannZeta0 0).re`;
- existing proof that `(liCoefficientCandidate 1).im = 0`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved as `liCoefficientCandidate_one_re_pos`.

Inventory status:

- mathlib provides `completedRiemannZeta₀_one`, `completedRiemannZeta₀_zero`,
  `completedRiemannZeta₀_one_sub`, and `deriv_riemannZeta_zero`;
- no direct theorem was found for `deriv completedRiemannZeta₀ 0` or its real part;
- the `deriv_riemannZeta_zero` proof only exposes the first derivative of
  `s * completedRiemannZeta₀ s`, where the derivative of `completedRiemannZeta₀` is multiplied by
  `s` and vanishes at `0`.

Subnodes:

- `T1.li1.deriv.bound.reduction`: proved as
  `liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt`.
  It reduces positivity to the upper bound
  `(deriv completedRiemannZeta₀ 0).re <
    ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re)) / 2`.
- `T1.li1.threshold.positive`: proved as
  `liCoefficientCandidate_zero_re_mul_four_sub_pos`, using
  `liCoefficientCandidate_zero_re_pos` and `liCoefficientCandidate_zero_re_lt_four`.
- `T1.li1.mellin.deriv.reduction`: proved as
  `liCoefficientCandidate_one_re_pos_iff_deriv_hurwitzEvenFEPair_Λ₀_zero_re_lt`.
  It rewrites the remaining bound through the definition
  `completedRiemannZeta₀ s = ((hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2`, giving
  `deriv completedRiemannZeta₀ 0 = deriv (hurwitzEvenFEPair 0).Λ₀ 0 / 4`.
- `T1.li1.mellin.log.deriv`: proved as
  `mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero` and
  `deriv_hurwitzEvenFEPair_Λ₀_zero_eq_mellin_log_f_modif_zero`. Mathlib's
  `mellin_hasDerivAt_of_isBigO_rpow` applies to the strong FE pair attached to
  `hurwitzEvenFEPair 0`, so the derivative is the Mellin transform of
  `fun t => Real.log t • (hurwitzEvenFEPair 0).f_modif t`.
- `T1.li1.mellin.log.bound.reduction`: proved as
  `liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt`.
  The remaining positivity goal is now the real bound
  `(mellin (fun t => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re <
    2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re))`.
- `T1.li1.mellin.log.integral.split`: proved as
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real`, with support from
  `ofReal_cpow_zero_sub_one`,
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq`,
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral`, and
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split`. It rewrites the remaining
  log-weighted Mellin term as the sum of the `(0,1)` and `(1,∞)` integrals of
  `x ^ (-1) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re`.
- `T1.li1.mellin.log.left.nonpos`: proved as
  `mellin_log_integral_Ioo_zero_one_nonpos` and
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one`. The first theorem uses
  `Real.log_nonpos` on `(0,1)` and the nonnegativity of the modified kernel's real part; the
  second reduces the remaining upper-bound problem to the `(1,∞)` integral alone.
- `T1.li1.mellin.log.right.exp_tail`: proved as
  `mellin_log_right_integrand_re_le_exp_tail_of_one_lt` and
  `mellin_log_integral_Ioi_one_le_exp_tail`. On `(1,∞)`, the multiplier
  `x ^ (-1) * Real.log x` is nonnegative, so the existing large-side theta-tail comparison
  lifts to the log-weighted integrand; the integral comparison is conditional on integrability of
  the log-weighted exponential majorant.
- `T1.li1.mellin.log.right.exp_tail.integrable`: proved as
  `mellin_log_right_exp_tail_le_const_mul_rexp` and
  `integrableOn_mellin_log_right_exp_tail`. On `x ≥ 1`, `Real.log x ≤ x` gives
  `x ^ (-1) * Real.log x ≤ 1`; combining this with the previous denominator comparison dominates
  the majorant by `(2 * (1 - exp (-π))⁻¹) * exp (-π*x)`. Continuity on `Ici 1` plus
  `integrable_of_isBigO_exp_neg` gives integrability on `Ioi 1`.
- `T1.li1.mellin.log.right.exp_tail.closed_bound`: proved as
  `mellin_log_integral_Ioi_one_le_integral_exp_tail`,
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_exp_tail`,
  `mellin_log_right_exp_tail_integral_le_const_integral_rexp`,
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_const_exp`, and
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound`. This instantiates the Loop 80
  conditional comparison with Loop 81 integrability, composes it with the nonpositive left-side
  reduction, compares the majorant integral to the constant exponential tail, and uses the existing
  closed form for `∫ x in Ioi 1, exp (-π*x)`.
- `T1.li1.mellin.log.right.exp_tail.rational_bound`: proved as
  `mellin_log_const_exp_bound_lt_seventeen_over_one_sixty` and
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`. This combines Loop 61
  `exp (-π) / π < 1/20` and Loop 62 `2 * (1 - exp (-π))⁻¹ < 17/8` to obtain the rational upper
  bound `17/160` for the log-weighted Mellin real part.
- `T1.li1.threshold.rational_lower`: proved as
  `Real.eulerMascheroniConstant_gt_571_over_1000`,
  `Real.log_four_mul_pi_lt_2533_over_1000`,
  `liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty`,
  `liCoefficientCandidate_zero_re_lt_one`, and
  `liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`. The lower bound uses
  `eulerMascheroniSeq 99` and the decimal log bounds for `log 2`, `log 3`, and `log 5`.
- `T1.li1.positivity`: proved as `liCoefficientCandidate_one_re_pos`, by composing
  `mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty`,
  `liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty`, and
  `liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt`.

Next action:

- the scaffold note is complete; perform the Tier 2 inventory for Li criterion/Hadamard or
  Nyman-Beurling support.

### T1.note.li.scaffold

Informal statement:

Write a one-page result note explaining the verified local xi/Li scaffold and its limits.

Dependencies:

- Loops 1-68 log;
- final status of T1.xi.completed.bridge and T1.xi.zero.bridge;
- final status or gap report for T1.li1.positivity.

Lean status:

- documentation target only;
- completed as `research/li_scaffold_note_20260709.md`.

Result:

- the note lists the compiled local xi/completed-zeta bridge, xi/nontrivial-zero bridge, center
  scaffold, and first two local Li-candidate positivity results;
- it explicitly states that the project has not formalized a Li criterion, proved all Li
  coefficients positive, or proved RH.

Next action:

- perform the Tier 2 inventories for the Li/Hadamard and Nyman-Beurling routes before choosing
  `T2.pivot`.

## Tier 2: Structural Route Selection

### T2.inventory.li.hadamard

Inventory question:

Does mathlib currently have enough entire-function, zero-multiset, Hadamard-product, and
log-derivative infrastructure to state a useful Li-criterion direction?

Output:

- a short inventory note with theorem names and missing pieces;
- a yes/no recommendation for choosing this route.

Status:

- completed as `research/tier2_li_hadamard_inventory_20260709.md`.

Result:

- mathlib has strong local analytic, meromorphic divisor, canonical decomposition on balls,
  Jensen/log-counting, zeta-zero-set, and log-derivative infrastructure;
- no direct Li-criterion theorem, global xi Hadamard product, global zero enumeration with
  multiplicity, or coefficient-to-zero-sum bridge was found;
- recommendation: do not choose Li/Hadamard as the immediate Tier 2 route.

Next action:

- complete `T2.inventory.nyman.beurling`, then decide `T2.pivot`.

### T2.inventory.nyman.beurling

Inventory question:

Does mathlib currently have enough `L2`, closure/density, step-function, and fractional-part
infrastructure to state a useful Nyman-Beurling or Baez-Duarte route?

Output:

- a short inventory note with theorem names and missing pieces;
- a yes/no recommendation for choosing this route.

Status:

- completed as `research/tier2_nyman_beurling_inventory_20260709.md`.

Result:

- mathlib has strong `Lp`/`L2`, Hilbert inner-product, indicator-in-`Lp`, simple-function density,
  interval finite-measure, fractional-part measurability, and Hilbert-subspace closure tools;
- no direct Nyman-Beurling or Baez-Duarte criterion statement was found;
- recommendation: prefer this route for the immediate Tier 2 pivot because the first missing nodes
  are small measurability, boundedness, and `MemLp` lemmas.

Next action:

- close `T2.pivot` by choosing the Nyman-Beurling foundation route.

### T2.pivot

Decision node:

After both inventories, choose exactly one Tier 2 route for sustained work. Do not return to
coefficient-by-coefficient computation unless it discharges a Tier 1 deliverable.

Status:

- completed in Loop 88.

Decision:

- choose the Nyman-Beurling foundation route.

Reason:

- the Li/Hadamard inventory exposed missing global product, zero-enumeration, and zero-sum
  coefficient bridges;
- the Nyman-Beurling inventory exposed smaller first formal nodes around bounded fractional-part
  kernels, measurability, `MemLp`, and Hilbert-space span/closure infrastructure.

Rejected route:

- do not state the full Nyman-Beurling criterion yet;
- do not use Baez-Duarte arithmetic strengthening as the first formal target.

Next action:

- build the Nyman-Beurling foundation nodes in `LeanLab.Riemann.NymanBeurling`, starting from the
  compiled `L2` kernel theorem and then the span scaffold.

### T2.nyman.kernel.l2

Informal statement:

For every real `a`, the fractional-part kernel `x ↦ Int.fract (a / x)` is a member of `L2` on the
unit interval with respect to `volume.restrict (Set.Ioo 0 1)`.

Dependencies:

- `Measurable.fract`;
- `Int.fract_nonneg` and `Int.fract_lt_one`;
- finite measure for the restricted unit interval;
- `MemLp.of_bound`.

Lean status:

- proved in `LeanLab.Riemann.NymanBeurling`;
- main theorem: `fractionalPartKernel_memLp_two_unitInterval`;
- stronger helper: `fractionalPartKernel_memLp_unitInterval`;
- packaged `L2` element: `fractionalPartKernelL2`;
- almost-everywhere representative theorem: `fractionalPartKernelL2_coeFn`.

Result:

- this closes the first formal foundation node after the route pivot;
- the theorem is local and does not state any density criterion or RH implication.

Next action:

- define the real submodule generated by `fractionalPartKernelL2` and prove each generator belongs
  to it.

### T2.nyman.span.scaffold

Informal statement:

Define the real span of the packaged fractional-part kernels inside `L2(0,1)` and prove the basic
membership lemma for its generators.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- span definition: `nymanBeurlingKernelSpan`;
- generator membership theorem: `fractionalPartKernelL2_mem_nymanBeurlingKernelSpan`;
- range inclusion theorem: `range_fractionalPartKernelL2_subset_nymanBeurlingKernelSpan`;
- minimality theorem: `nymanBeurlingKernelSpan_le`.

Result:

- this creates the first project-local linear object for the Nyman-Beurling foundation route;
- it still does not state closure density, the Nyman-Beurling criterion, or an RH bridge.

Next action:

- define the topological closure of `nymanBeurlingKernelSpan` and prove the span is contained in
  its closure.

### T2.nyman.closure.scaffold

Informal statement:

Define the topological closure of the Nyman-Beurling kernel span inside `L2(0,1)` and prove the
basic inclusion from the span into its closure.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- closure definition: `nymanBeurlingKernelClosure`;
- span inclusion theorem: `nymanBeurlingKernelSpan_le_closure`;
- closedness theorem: `isClosed_nymanBeurlingKernelClosure`;
- set-closure equality: `nymanBeurlingKernelClosure_coe`;
- generator membership theorem: `fractionalPartKernelL2_mem_nymanBeurlingKernelClosure`.

Result:

- this creates the topological object needed for a future density formulation;
- it still does not assert that the closure is the whole space.

Next action:

- define the project-local density predicate for the kernel span and prove its equivalence with
  `nymanBeurlingKernelClosure = ⊤`.

### T2.nyman.density.predicate

Informal statement:

Package the Hilbert-space-side density statement for the Nyman-Beurling kernel span.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- predicate definition: `nymanBeurlingKernelDense`;
- closure equivalence theorem: `nymanBeurlingKernelDense_iff_closure_eq_top`;
- pointwise closure theorem: `nymanBeurlingKernelDense_iff_forall_mem_closure`.

Result:

- the local Hilbert-space density statement is now an explicit compiled predicate;
- no Nyman-Beurling criterion or RH bridge is asserted.

Next action:

- reformulate `nymanBeurlingKernelDense` through the orthogonal complement of
  `nymanBeurlingKernelSpan`.

### T2.nyman.orthogonal.reformulation

Informal statement:

Use Hilbert-space infrastructure to show that density of the kernel span is equivalent to its
orthogonal complement being bottom.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `nymanBeurlingKernelDense_iff_orthogonal_eq_bot`.

Result:

- the local Hilbert-space density predicate is now equivalent to the absence of a nonzero
  orthogonal obstruction to the kernel span;
- no Nyman-Beurling criterion or RH bridge is asserted.

Next action:

- unpack membership in `nymanBeurlingKernelSpanᗮ` into vanishing inner products against every
  packaged fractional-part kernel.

### T2.nyman.orthogonal.pointwise

Informal statement:

For `f : unitIntervalL2`, express `f ∈ nymanBeurlingKernelSpanᗮ` as the statement that the inner
product of `f` with every generator `fractionalPartKernelL2 a` vanishes.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `mem_nymanBeurlingKernelSpan_orthogonal_iff`.

Result:

- membership in the orthogonal complement of the kernel span is now equivalent to vanishing inner
  products against every packaged fractional-part kernel;
- the proof uses span induction from the generator family.

Next action:

- combine this theorem with `nymanBeurlingKernelDense_iff_orthogonal_eq_bot` to express density as
  the absence of a nonzero vector orthogonal to every packaged kernel.

### T2.nyman.density.pointwise

Informal statement:

Reformulate `nymanBeurlingKernelDense` as the statement that every `f : unitIntervalL2` with
`⟪fractionalPartKernelL2 a, f⟫_ℝ = 0` for all real `a` must be zero.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`.

Result:

- the local Hilbert-space density predicate is now equivalent to the statement that every vector
  orthogonal to all packaged fractional-part kernels is zero;
- this remains an equivalence and does not assert density.

Next action:

- perform a bounded inventory of mathlib support for rewriting these `L²` inner products as
  integrals over the restricted unit interval.

### T2.nyman.inner.integral.inventory

Informal statement:

Inspect mathlib support for turning `⟪fractionalPartKernelL2 a, f⟫_ℝ` into an integral expression
involving the almost-everywhere representatives of `fractionalPartKernelL2 a` and `f`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- inventory note: `research/tier2_nyman_inner_integral_inventory_20260710.md`;
- theorem: `inner_fractionalPartKernelL2_eq_integral`.

Result:

- mathlib's `L2.inner_def` gives the expected inner-product-to-integral bridge;
- the packaged kernel can be replaced almost everywhere by `fractionalPartKernel a`;
- the compiled theorem rewrites `⟪fractionalPartKernelL2 a, f⟫_ℝ` as an integral over
  `volume.restrict (Set.Ioo 0 1)`.

Next action:

- combine `inner_fractionalPartKernelL2_eq_integral` with
  `nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`.

### T2.nyman.density.integral

Informal statement:

Reformulate `nymanBeurlingKernelDense` as the statement that every `f : unitIntervalL2` with
`∫ x, fractionalPartKernel a x * f x` equal to zero for every real `a` must be zero.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero`.

Result:

- the density obstruction can now be stated entirely with integrals against the concrete
  fractional-part kernels;
- this remains an equivalence and does not assert density.

Next action:

- package the constant-one function as an element of `unitIntervalL2`.

### T2.nyman.constant.one.l2

Informal statement:

Define the constant-one function as an element of `unitIntervalL2` and prove its almost-everywhere
representative theorem.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- constant function definition: `unitIntervalOne`;
- packaged `L²` element: `unitIntervalOneL2`;
- membership theorem: `unitIntervalOne_memLp_two_unitInterval`;
- almost-everywhere representative theorem: `unitIntervalOneL2_coeFn`;
- constant representative theorem: `unitIntervalOneL2_coeFn_const`.

Result:

- the target vector for the local Nyman-Beurling closure formulation is now a compiled object in
  the same Hilbert space as the fractional-part kernel span;
- this does not assert density or a criterion bridge.

Next action:

- prove the conditional closure bridge
  `nymanBeurlingKernelDense -> unitIntervalOneL2 ∈ nymanBeurlingKernelClosure`.

### T2.nyman.density.one.closure

Informal statement:

If the project-local Nyman-Beurling kernel span is dense, then the packaged constant-one vector
belongs to its topological closure.

Dependencies:

- `unitIntervalOneL2`;
- `nymanBeurlingKernelClosure`;
- `nymanBeurlingKernelDense_iff_forall_mem_closure`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense`.

Result:

- the abstract density predicate now gives the classical target-vector closure membership as a
  compiled conditional statement;
- this does not assert density.

Next action:

- reformulate `unitIntervalOneL2 ∈ nymanBeurlingKernelClosure` as an epsilon-distance
  approximation statement with approximants in `nymanBeurlingKernelSpan`.

### T2.nyman.one.closure.epsilon

Informal statement:

Express membership of `unitIntervalOneL2` in the kernel-span closure as: for every positive
epsilon, there exists an approximant in `nymanBeurlingKernelSpan` whose distance from
`unitIntervalOneL2` is smaller than epsilon.

Dependencies:

- `nymanBeurlingKernelClosure_coe`;
- mathlib closure-neighborhood or metric-closure API;
- `unitIntervalOneL2`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- closure equivalence theorem: `unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt`;
- density-conditioned corollary:
  `exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense`.

Result:

- constant-one closure membership is now equivalent to epsilon-distance approximation by elements
  of `nymanBeurlingKernelSpan`;
- under `nymanBeurlingKernelDense`, the epsilon approximants exist for every positive epsilon.

Next action:

- unpack membership in `nymanBeurlingKernelSpan` into finite real linear combinations of packaged
  fractional-part kernels.

### T2.nyman.span.finite.approx

Informal statement:

Turn the abstract approximant `g ∈ nymanBeurlingKernelSpan` into an explicit finite real linear
combination of vectors `fractionalPartKernelL2 a`.

Dependencies:

- `nymanBeurlingKernelSpan = Submodule.span ℝ (Set.range fractionalPartKernelL2)`;
- mathlib span membership API, specifically `Finsupp.mem_span_range_iff_exists_finsupp`;
- the epsilon approximation theorem from `T2.nyman.one.closure.epsilon`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- span membership theorem: `mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum`;
- finite-combination closure equivalence:
  `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt`;
- density-conditioned finite-combination approximation theorem:
  `exists_finsupp_sum_fractionalPartKernelL2_dist_unitIntervalOneL2_lt_of_dense`.

Result:

- constant-one closure membership is now equivalent to approximation by finite real linear
  combinations of packaged fractional-part kernels;
- under `nymanBeurlingKernelDense`, such finite-combination approximants exist for every positive
  epsilon.

Next action:

- rewrite the finite-combination distance statement as a norm inequality for
  `unitIntervalOneL2 - finiteCombination`.

### T2.nyman.finite.approx.norm

Informal statement:

Express the finite-combination epsilon approximation using the norm of the difference between
`unitIntervalOneL2` and the finite kernel combination.

Dependencies:

- `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt`;
- metric/norm identity `dist_eq_norm`;
- the same `Finsupp` finite-combination expression.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- norm-form closure equivalence:
  `unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt`;
- density-conditioned norm approximation theorem:
  `exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`.

Result:

- the finite-combination approximation is now expressed as the norm of
  `unitIntervalOneL2 - finiteCombination`;
- this is the local Hilbert-space norm form of the approximation target.

Next action:

- perform a bounded inventory of `L²` norm-square-to-integral formulas before trying to rewrite
  this norm as an integral of squared representatives.

### T2.nyman.finite.approx.integral.inventory

Inventory question:

Does mathlib provide a usable theorem to rewrite the `L²` norm of
`unitIntervalOneL2 - finiteCombination` as an integral over `volume.restrict (Set.Ioo 0 1)`?

Expected output:

- a short inventory note with candidate theorem names;
- either a compiled norm-square-to-integral bridge theorem or a recorded dependency gap.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- inventory note: `research/tier2_nyman_finite_approx_integral_inventory_20260710.md`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- generic norm-square bridge: `unitIntervalL2_norm_sq_eq_integral_mul_self`;
- finite-combination specialization:
  `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self`.

Result:

- the `unitIntervalL2` norm-square can be rewritten as an integral of the pointwise representative
  times itself;
- for finite kernel combinations, the theorem applies to the `Lp` representative of the
  difference.

Remaining gap:

- the representative of
  `unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)` still needs to be related
  almost everywhere to the concrete finite sum of fractional-part functions.

Next action:

- prove an almost-everywhere representative theorem for finite `Finsupp` sums of
  `fractionalPartKernelL2`.

### T2.nyman.finite.approx.representatives

Informal statement:

For finite coefficients `c : ℝ →₀ ℝ`, identify
`c.sum fun a r => r • fractionalPartKernelL2 a` almost everywhere with the pointwise finite sum
`c.sum fun a r => r * fractionalPartKernel a x`.

Dependencies:

- `fractionalPartKernelL2_coeFn`;
- `unitIntervalOneL2_coeFn` for the subsequent difference theorem;
- `Lp` coercion theorems for finite sums and scalar multiplication;
- `Filter.EventuallyEq` finite-sum congruence.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- finite-combination representative theorem: `finsupp_sum_fractionalPartKernelL2_coeFn`;
- constant-one-minus-finite-combination representative theorem:
  `unitIntervalOneL2_sub_finsupp_sum_fractionalPartKernelL2_coeFn`;
- concrete norm-square integral theorem:
  `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete`.

Result:

- finite packaged kernel combinations are now identified almost everywhere with concrete finite
  sums of fractional-part kernels;
- the squared `L²` norm of `unitIntervalOneL2 - finiteCombination` is now rewritten as the
  integral of `(1 - concreteFiniteSum) * (1 - concreteFiniteSum)`.

Next action:

- fill `T2.nyman.finite.approx.integral.epsilon`, deriving a concrete squared-error integral
  bound from the density-conditioned norm approximation.

### T2.nyman.finite.approx.integral.epsilon

Informal statement:

Assuming `nymanBeurlingKernelDense` and `0 < ε`, find finite coefficients `c : ℝ →₀ ℝ` such that
the concrete squared-error integral associated to
`1 - c.sum fun a r => r * fractionalPartKernel a x` is below `ε ^ 2`.

Dependencies:

- `exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`;
- `norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete`;
- elementary ordered-ring facts converting `‖v‖ < ε` and `0 < ε` into `‖v‖ ^ 2 < ε ^ 2`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- density-conditioned concrete squared-error theorem:
  `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense`.

Result:

- under `nymanBeurlingKernelDense`, every positive `ε` gives a finite coefficient family whose
  concrete squared-error integral is below `ε ^ 2`;
- the proof uses the norm approximation theorem, the concrete norm-square integral identity, and
  `sq_lt_sq₀` on nonnegative real quantities.

Next action:

- fill `T2.nyman.finite.approx.integral.tolerance`, removing the square from the tolerance to
  match the usual `∀ δ > 0` approximation shape.

### T2.nyman.finite.approx.integral.tolerance

Informal statement:

Assuming `nymanBeurlingKernelDense` and `0 < δ`, find finite coefficients `c : ℝ →₀ ℝ` such that
the concrete squared-error integral associated to
`1 - c.sum fun a r => r * fractionalPartKernel a x` is below `δ`.

Dependencies:

- `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense`;
- `Real.sqrt_pos_of_pos`;
- `Real.sq_sqrt` or an equivalent real square-root simplification.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- positive-tolerance theorem:
  `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance`.

Result:

- under `nymanBeurlingKernelDense`, every positive tolerance `δ` has a finite coefficient
  family whose concrete squared-error integral is below `δ`;
- the proof instantiates the `ε ^ 2` theorem with `Real.sqrt δ` and simplifies by
  `Real.sq_sqrt`.

Next action:

- fill `T2.nyman.concrete.approx.predicate`, packaging this positive-tolerance statement as a
  reusable project-local approximation predicate.

### T2.nyman.concrete.approx.predicate

Informal statement:

Define a project-local predicate for the concrete Nyman-Beurling finite-approximation property:
for every positive tolerance, there is a finite real coefficient family whose squared-error
integral against the concrete fractional-part finite sum is below that tolerance. Then prove
`nymanBeurlingKernelDense` implies this predicate.

Dependencies:

- `exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance`;
- the concrete integral expression already stabilized in the previous nodes.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- predicate: `nymanBeurlingConcreteApprox`;
- density-to-predicate theorem: `nymanBeurlingConcreteApprox_of_dense`.

Result:

- the concrete finite-approximation property now has a short project-local name;
- `nymanBeurlingKernelDense` implies this predicate by direct use of the positive-tolerance
  theorem.

Next action:

- fill `T2.nyman.classical.criterion.inventory`, comparing this project-local predicate with the
  classical Nyman-Beurling/Baez-Duarte criterion before attempting any RH bridge.

### T2.nyman.classical.criterion.inventory

Inventory question:

How does `nymanBeurlingConcreteApprox` differ from the exact classical Nyman-Beurling or
Baez-Duarte criterion statements, and which formal bridges would be needed before connecting it to
mathlib's `RiemannHypothesis`?

Expected output:

- a short inventory note listing the statement-shape differences;
- a decision on the next Lean target after the inventory;
- no use of an unproved criterion as a premise.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- closed by inventory note `research/tier2_nyman_classical_criterion_inventory_20260710.md`.

Result:

- current project predicate has arbitrary real parameters and lives on `L²(0,1)` with a
  concrete integral-tolerance statement;
- classical sources point toward restricted unit-interval parameters, Baez-Duarte's natural
  parameter strengthening, and a separate bridge between closure-style statements and the
  concrete integral-tolerance predicate;
- no local theorem now connects a Nyman-Beurling closure criterion to mathlib's
  `RiemannHypothesis`.

M0 correction after Batch 02:

- Beurling's unit-interval space has the additional condition `sum c_k * theta_k = 0`;
- Balazard-Saias encode it with modified generators;
- the project restricted predicate omits that condition, and the project positive-natural local
  predicate omits the equivalent Baez-Duarte full-line tail;
- `restricted_finsupp_tail_error_eq_moment_sq` computes the missing tail in Lean.

Next action:

- fill `T2.nyman.restricted.concrete.approx.predicate`, defining a restricted-parameter concrete
  approximation predicate and proving it implies the current unrestricted predicate.

### T2.nyman.restricted.concrete.approx.predicate

Informal statement:

Define a concrete approximation predicate where every finite coefficient support lies in
`0 < a ∧ a ≤ 1`, then prove that this restricted predicate implies
`nymanBeurlingConcreteApprox`.

Dependencies:

- `nymanBeurlingConcreteApprox`;
- `Finsupp` support membership or coefficient-zero outside support API;
- the existing concrete integral expression from `LeanLab.Riemann.NymanBeurling`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- predicate: `nymanBeurlingRestrictedConcreteApprox`;
- theorem: `nymanBeurlingConcreteApprox_of_restricted`.

Result:

- the project now has a named concrete approximation predicate with finite support contained in
  `0 < a ∧ a ≤ 1`;
- this restricted predicate implies the previous unrestricted concrete predicate by reusing the
  same finite coefficient family and dropping only the support condition.
- M0 Batch 02 proved this predicate is exactly membership of `unitIntervalOneL2` in the project
  restricted closure, but it is not the published Beurling closure because the coefficient moment
  is unconstrained.

Next action:

- fill `T2.nyman.restricted.span.scaffold`, defining the span generated by the restricted kernel
  family and proving that this span is contained in `nymanBeurlingKernelSpan`.

### T2.nyman.restricted.span.scaffold

Informal statement:

Define a submodule generated by `fractionalPartKernelL2 a` for parameters satisfying
`0 < a ∧ a ≤ 1`, then prove that it is contained in the existing unrestricted
`nymanBeurlingKernelSpan`.

Dependencies:

- `fractionalPartKernelL2`;
- `nymanBeurlingKernelSpan`;
- `Submodule.span_le` and the existing generator membership theorem
  `fractionalPartKernelL2_mem_nymanBeurlingKernelSpan`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- definitions: `nymanBeurlingRestrictedParameterSet`, `nymanBeurlingRestrictedKernelSet`,
  `nymanBeurlingRestrictedKernelSpan`;
- theorems: `fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSet`,
  `fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSpan`,
  `nymanBeurlingRestrictedKernelSpan_le`.

Result:

- restricted unit-interval parameters now have a named set;
- the restricted packaged kernel family has a named set and span;
- every restricted generator belongs to that span;
- the restricted span is contained in the unrestricted `nymanBeurlingKernelSpan`.

Next action:

- fill `T2.nyman.restricted.closure.scaffold`, defining the topological closure of
  `nymanBeurlingRestrictedKernelSpan` and relating it to `nymanBeurlingKernelClosure`.

### T2.nyman.restricted.closure.scaffold

Informal statement:

Define `nymanBeurlingRestrictedKernelClosure` as the topological closure of
`nymanBeurlingRestrictedKernelSpan`; prove the restricted span is contained in this closure, prove
the closure is closed, and prove it is contained in `nymanBeurlingKernelClosure`.

Dependencies:

- `nymanBeurlingRestrictedKernelSpan`;
- `nymanBeurlingKernelClosure`;
- `nymanBeurlingRestrictedKernelSpan_le`;
- topological-closure monotonicity for submodules.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- definition: `nymanBeurlingRestrictedKernelClosure`;
- theorems: `nymanBeurlingRestrictedKernelSpan_le_closure`,
  `isClosed_nymanBeurlingRestrictedKernelClosure`,
  `nymanBeurlingRestrictedKernelClosure_coe`, `nymanBeurlingRestrictedKernelClosure_le`,
  `fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelClosure`.

Result:

- the restricted span now has a named topological closure;
- the restricted span is contained in its closure;
- the restricted closure is closed and has the expected set-level closure coercion;
- the restricted closure is contained in the unrestricted `nymanBeurlingKernelClosure`;
- every packaged kernel with `0 < a ∧ a ≤ 1` lies in the restricted closure.

Next action:

- fill `T2.nyman.restricted.density.predicate`, defining density of
  `nymanBeurlingRestrictedKernelSpan` and proving the same closure-top and pointwise-closure
  forms used earlier for the unrestricted route.

### T2.nyman.restricted.density.predicate

Informal statement:

Define `nymanBeurlingRestrictedKernelDense` as density of the restricted kernel span in
`unitIntervalL2`; prove equivalence to `nymanBeurlingRestrictedKernelClosure = ⊤` and to every
`unitIntervalL2` vector lying in the restricted closure.

Dependencies:

- `nymanBeurlingRestrictedKernelSpan`;
- `nymanBeurlingRestrictedKernelClosure`;
- `Submodule.dense_iff_topologicalClosure_eq_top`;
- `nymanBeurlingRestrictedKernelClosure_coe`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- predicate: `nymanBeurlingRestrictedKernelDense`;
- theorems: `nymanBeurlingRestrictedKernelDense_iff_closure_eq_top`,
  `nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`.

Result:

- restricted kernel-span density now has a named project-local predicate;
- the predicate is equivalent to `nymanBeurlingRestrictedKernelClosure = ⊤`;
- the predicate is also equivalent to every vector in `unitIntervalL2` lying in the restricted
  closure.

Next action:

- fill `T2.nyman.restricted.density.implies.unrestricted`, proving that restricted density implies
  the existing unrestricted density predicate.

### T2.nyman.restricted.density.implies.unrestricted

Informal statement:

Prove `nymanBeurlingRestrictedKernelDense → nymanBeurlingKernelDense`.

Dependencies:

- `nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`;
- `nymanBeurlingKernelDense_iff_forall_mem_closure`;
- `nymanBeurlingRestrictedKernelClosure_le`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `nymanBeurlingKernelDense_of_restricted`.

Result:

- restricted kernel-span density now conditionally implies the existing unrestricted density
  predicate;
- the proof uses the pointwise restricted-closure form and the inclusion
  `nymanBeurlingRestrictedKernelClosure_le`.

Next action:

- fill `T2.nyman.restricted.density.concrete.approx`, deriving `nymanBeurlingConcreteApprox` from
  `nymanBeurlingRestrictedKernelDense` by composing with the existing unrestricted concrete
  approximation theorem.

### T2.nyman.restricted.density.concrete.approx

Informal statement:

Prove `nymanBeurlingRestrictedKernelDense → nymanBeurlingConcreteApprox`.

Dependencies:

- `nymanBeurlingKernelDense_of_restricted`;
- `nymanBeurlingConcreteApprox_of_dense`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `nymanBeurlingConcreteApprox_of_restrictedKernelDense`.

Result:

- restricted density conditionally implies the existing unrestricted concrete approximation
  predicate;
- this bridge composes `nymanBeurlingKernelDense_of_restricted` with
  `nymanBeurlingConcreteApprox_of_dense`.

Next action:

- fill `T2.nyman.restricted.density.one.closure`, proving that restricted density places
  `unitIntervalOneL2` in `nymanBeurlingRestrictedKernelClosure`.

### T2.nyman.restricted.density.one.closure

Informal statement:

Prove `nymanBeurlingRestrictedKernelDense → unitIntervalOneL2 ∈
nymanBeurlingRestrictedKernelClosure`.

Dependencies:

- `nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`;
- `unitIntervalOneL2`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense`.

Result:

- restricted density now places the constant-one target vector in the restricted closure;
- this is the restricted analogue of the earlier unrestricted theorem
  `unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense`.

Next action:

- fill `T2.nyman.restricted.one.closure.epsilon`, reformulating restricted closure membership as
  epsilon-distance approximation by elements of `nymanBeurlingRestrictedKernelSpan`.

### T2.nyman.restricted.one.closure.epsilon

Informal statement:

Prove `unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure` is equivalent to: for every
positive `ε`, there exists `g ∈ nymanBeurlingRestrictedKernelSpan` with
`dist unitIntervalOneL2 g < ε`.

Dependencies:

- `nymanBeurlingRestrictedKernelClosure_coe`;
- `Metric.mem_closure_iff`;
- `nymanBeurlingRestrictedKernelSpan`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt`;
- corollary:
  `exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense`.

Result:

- restricted closure membership of the constant-one target is equivalent to epsilon-distance
  approximation by elements of `nymanBeurlingRestrictedKernelSpan`;
- under `nymanBeurlingRestrictedKernelDense`, every positive tolerance has a restricted-span
  approximant within that tolerance.

Next action:

- fill `T2.nyman.restricted.span.finite.approx`, unpacking restricted-span membership into finite
  sums indexed by restricted parameters.

### T2.nyman.restricted.span.finite.approx

Informal statement:

Prove membership in `nymanBeurlingRestrictedKernelSpan` is equivalent to a finite real linear
combination of packaged kernels indexed by the restricted-parameter subtype.

Dependencies:

- `nymanBeurlingRestrictedKernelSpan`;
- `nymanBeurlingRestrictedKernelSet`;
- `Finsupp.mem_span_range_iff_exists_finsupp`;
- the equivalence between `fractionalPartKernelL2 '' nymanBeurlingRestrictedParameterSet` and
  the range of the subtype-indexed kernel map.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- definition: `restrictedFractionalPartKernelL2`;
- theorems: `nymanBeurlingRestrictedKernelSet_eq_range`,
  `mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum`.

Result:

- the restricted kernel set is represented as the range of a subtype-indexed packaged kernel map;
- membership in `nymanBeurlingRestrictedKernelSpan` is equivalent to a finite real linear
  combination of `fractionalPartKernelL2 (a : ℝ)` over
  `a : nymanBeurlingRestrictedParameterSet`.

Next action:

- fill `T2.nyman.restricted.finite.approx.dist`, deriving subtype-indexed finite-sum distance
  approximants from `nymanBeurlingRestrictedKernelDense`.

### T2.nyman.restricted.finite.approx.dist

Informal statement:

Assuming `nymanBeurlingRestrictedKernelDense` and `0 < ε`, prove there is
`c : nymanBeurlingRestrictedParameterSet →₀ ℝ` such that
`dist unitIntervalOneL2 (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ)) < ε`.

Dependencies:

- `exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense`;
- `mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`.

Result:

- under `nymanBeurlingRestrictedKernelDense`, every positive tolerance has a subtype-indexed
  finite coefficient family whose packaged finite sum is within that tolerance of
  `unitIntervalOneL2` in distance.

Next action:

- fill `T2.nyman.restricted.finite.approx.norm`, rewriting this restricted finite-sum distance
  approximation as a norm inequality.

### T2.nyman.restricted.finite.approx.norm

Informal statement:

Assuming `nymanBeurlingRestrictedKernelDense` and `0 < ε`, prove there is
`c : nymanBeurlingRestrictedParameterSet →₀ ℝ` such that
`‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ < ε`.

Dependencies:

- `exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`;
- `dist_eq_norm`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `exists_restricted_finsupp_sum_norm_sub_lt_of_dense`.

Result:

- under `nymanBeurlingRestrictedKernelDense`, every positive tolerance has a subtype-indexed
  finite coefficient family whose packaged finite sum differs from `unitIntervalOneL2` by norm
  below that tolerance.

Next action:

- fill `T2.nyman.restricted.finite.approx.integral.inventory`, checking whether the generic
  norm-square-to-integral bridge applies directly to subtype-indexed restricted finite sums.

### T2.nyman.restricted.finite.approx.integral.inventory

Inventory question:

Does the existing `unitIntervalL2` norm-square-to-integral bridge apply cleanly to
`unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))` for
`c : nymanBeurlingRestrictedParameterSet →₀ ℝ`?

Expected output:

- a short inventory note with candidate theorem names;
- either a compiled restricted norm-square bridge theorem or a recorded dependency gap.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- inventory note: `research/tier2_nyman_restricted_finite_approx_integral_inventory_20260710.md`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- restricted finite-sum norm-square bridge:
  `norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self`.

Result:

- the generic `unitIntervalL2` norm-square-to-integral bridge applies directly to subtype-indexed
  restricted finite kernel combinations.

Remaining gap:

- the integral still uses the selected `Lp` representative of the difference;
- the next bridge must identify restricted finite sums almost everywhere with concrete finite
  sums of `fractionalPartKernel (a : ℝ)`.

Next action:

- fill `T2.nyman.restricted.finite.approx.representatives`.

### T2.nyman.restricted.finite.approx.representatives

Informal statement:

For finite coefficients `c : nymanBeurlingRestrictedParameterSet →₀ ℝ`, identify
`c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ)` almost everywhere with the pointwise finite
sum `c.sum fun a r => r * fractionalPartKernel (a : ℝ) x`, and then identify the
`unitIntervalOneL2` difference.

Dependencies:

- `fractionalPartKernelL2_coeFn`;
- `unitIntervalOneL2_coeFn`;
- `Lp` coercion theorems for finite sums and scalar multiplication;
- `Filter.EventuallyEq` finite-sum congruence.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- restricted finite-sum representative theorem:
  `restricted_finsupp_sum_fractionalPartKernelL2_coeFn`;
- restricted constant-one difference representative theorem:
  `unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn`;
- restricted concrete norm-square integral theorem:
  `norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete`.

Result:

- subtype-indexed restricted finite sums are now identified almost everywhere with concrete
  finite sums of `fractionalPartKernel (a : ℝ)`;
- the restricted finite-sum norm-square integral is rewritten as a concrete squared-error
  integral.

Next action:

- fill `T2.nyman.restricted.finite.approx.integral.epsilon`.

### T2.nyman.restricted.finite.approx.integral.epsilon

Informal statement:

Assuming `nymanBeurlingRestrictedKernelDense` and `0 < ε`, prove there is
`c : nymanBeurlingRestrictedParameterSet →₀ ℝ` such that
`∫ x, (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
  (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) < ε ^ 2`.

Dependencies:

- `exists_restricted_finsupp_sum_norm_sub_lt_of_dense`;
- `norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete`;
- `sq_lt_sq₀`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `exists_restricted_finsupp_integral_sq_lt_of_dense`.

Result:

- under `nymanBeurlingRestrictedKernelDense`, every positive `ε` has a subtype-indexed
  restricted finite coefficient family whose concrete squared-error integral is below `ε ^ 2`.

Next action:

- fill `T2.nyman.restricted.finite.approx.integral.tolerance`.

### T2.nyman.restricted.finite.approx.integral.tolerance

Informal statement:

Assuming `nymanBeurlingRestrictedKernelDense` and `0 < δ`, prove there is
`c : nymanBeurlingRestrictedParameterSet →₀ ℝ` whose concrete squared-error integral is below
`δ`.

Dependencies:

- `exists_restricted_finsupp_integral_sq_lt_of_dense`;
- `Real.sqrt_pos_of_pos`;
- `Real.sq_sqrt`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `exists_restricted_finsupp_integral_lt_of_dense_tolerance`.

Result:

- under `nymanBeurlingRestrictedKernelDense`, every positive tolerance has a subtype-indexed
  restricted finite coefficient family whose concrete squared-error integral is below that
  tolerance.

Next action:

- fill `T2.nyman.restricted.finite.approx.real.support`.

### T2.nyman.restricted.finite.approx.real.support

Informal statement:

Convert a coefficient family indexed by `nymanBeurlingRestrictedParameterSet` into a coefficient
family indexed by `ℝ`, preserving the concrete finite sum and proving every active real parameter
satisfies `0 < a ∧ a ≤ 1`.

Dependencies:

- `Finsupp` support/image or emb-domain tools;
- the subtype property inside `nymanBeurlingRestrictedParameterSet`;
- finite-sum reindexing for `fractionalPartKernel`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- coefficient bridge: `exists_real_finsupp_of_restricted_finsupp`;
- integral bridge: `exists_real_finsupp_integral_lt_of_restricted`.

Result:

- subtype-indexed restricted coefficient families can be pushed to real-indexed coefficient
  families with explicit support condition `0 < a ∧ a ≤ 1`;
- the concrete finite sum, and therefore the concrete squared-error integral bound, is preserved.

Next action:

- fill `T2.nyman.restricted.concrete.approx.of.dense`.

### T2.nyman.restricted.concrete.approx.of.dense

Informal statement:

Assuming `nymanBeurlingRestrictedKernelDense`, prove `nymanBeurlingRestrictedConcreteApprox`.

Dependencies:

- `exists_restricted_finsupp_integral_lt_of_dense_tolerance`;
- `exists_real_finsupp_integral_lt_of_restricted`;
- definition of `nymanBeurlingRestrictedConcreteApprox`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- proved in `LeanLab.Riemann.NymanBeurling`;
- theorem: `nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense`.

Result:

- `nymanBeurlingRestrictedKernelDense` now implies the project-local predicate
  `nymanBeurlingRestrictedConcreteApprox`;
- by the existing theorem `nymanBeurlingConcreteApprox_of_restricted`, this also feeds the
  unrestricted project-local concrete approximation predicate.

Next action:

- fill `T2.nyman.restricted.route.summary`.

### T2.nyman.restricted.route.summary

Expected output:

- a short route summary recording the compiled chain from restricted density to restricted
  concrete approximation;
- a list of remaining gaps before a classical Báez-Duarte/Nyman-Beurling criterion bridge.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- route summary: `research/tier2_nyman_restricted_route_summary_20260710.md`;
- completed as a documentation/checkpoint node.

Result:

- recorded the compiled project-local chain
  `nymanBeurlingRestrictedKernelDense → nymanBeurlingRestrictedConcreteApprox`;
- separated this local result from the remaining classical Báez-Duarte/Nyman-Beurling gaps.
- later M0 correction: the leading gap is the missing zero-moment/full-line-tail term, not natural
  indexing or the endpoint convention.

Next action:

- fill `T2.nyman.baez.duarte.natural.index.inventory`.

### T2.nyman.baez.duarte.natural.index.inventory

Inventory question:

Which Lean index type and reciprocal map should represent Baez-Duarte natural-parameter finite
approximants before attempting a formal bridge to the restricted real-parameter predicate?

Expected output:

- a short inventory note comparing candidate index types;
- a selected next formal target for natural-indexed finite-sum reindexing.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- inventory note recorded as
  `research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md`;
- completed as a documentation/checkpoint node.

Result:

- selected `{n : Nat // 0 < n}` as the first Lean index shape for Baez-Duarte
  natural-parameter approximants;
- selected the reciprocal map `n ↦ ((n : Real)⁻¹)` into
  `nymanBeurlingRestrictedParameterSet` as the next formal bridge;
- rejected plain `Nat` indexing because the zero case would pollute each finite-sum statement.

Next action:

- close `T2.nyman.baez.duarte.reciprocal.map`.

### T2.nyman.baez.duarte.reciprocal.map

Formal bridge question:

Can the reciprocal map from positive natural indices be bundled as a map into
`nymanBeurlingRestrictedParameterSet`, and preferably as an embedding usable by `Finsupp.embDomain`?

Expected output:

- a Lean definition or theorem verifying `0 < ((n : Nat) : Real)⁻¹` and
  `((n : Nat) : Real)⁻¹ <= 1` for positive natural `n`;
- if the proof stays small, an embedding from `{n : Nat // 0 < n}` into
  `nymanBeurlingRestrictedParameterSet`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- Lean names:
  - `baezDuartePositiveNatIndex`;
  - `baezDuarte_reciprocal_mem_restricted`;
  - `baezDuarteReciprocalParameter`;
  - `baezDuarteReciprocalEmbedding`;
- completed as a bounded formal bridge.

Result:

- positive natural indices are represented by `{n : Nat // 0 < n}`;
- each index maps to the restricted parameter `((n : Nat) : Real)⁻¹`;
- the map is packaged as an embedding, ready for finite-support coefficient transport.

Next action:

- close `T2.nyman.baez.duarte.natural.finsupp.bridge`.

### T2.nyman.baez.duarte.natural.finsupp.bridge

Formal bridge question:

Can finite coefficients indexed by positive natural numbers be transported along
`baezDuarteReciprocalEmbedding` to restricted-parameter coefficients without changing the concrete
finite sum?

Expected output:

- a theorem using `Finsupp.embDomain` along `baezDuarteReciprocalEmbedding`;
- preservation of the concrete sum
  `c.sum fun n r => r * fractionalPartKernel (((n : Nat) : Real)⁻¹) x`;
- a bridge theorem suitable for the later Baez-Duarte natural-parameter approximation predicate.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- Lean name: `exists_restricted_finsupp_of_baezDuarte_finsupp`;
- completed as a finite-sum transport bridge.

Result:

- positive-natural-indexed coefficients can be transported along
  `baezDuarteReciprocalEmbedding` to restricted-parameter coefficients;
- the concrete finite sum
  `c.sum fun n r => r * fractionalPartKernel (((n : Nat) : Real)⁻¹) x`
  is preserved for every `x`.

Next action:

- close `T2.nyman.baez.duarte.natural.integral.bridge`.

### T2.nyman.baez.duarte.natural.integral.bridge

Formal bridge question:

Can a positive-natural-indexed concrete squared-error integral bound be transported to a
restricted-parameter concrete squared-error integral bound?

Expected output:

- a theorem taking an existential natural-indexed integral bound as input;
- a restricted-parameter existential integral bound as output;
- proof by applying `exists_restricted_finsupp_of_baezDuarte_finsupp` and rewriting the integrand.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- Lean name: `exists_restricted_finsupp_integral_lt_of_baezDuarte`;
- completed as a bounded corollary.

Result:

- an existential positive-natural reciprocal squared-error integral bound transports to an
  existential restricted-parameter squared-error integral bound;
- the proof only uses the finite-sum bridge and integrand rewriting.

Next action:

- close `T2.nyman.baez.duarte.natural.concrete.approx.predicate`.

### T2.nyman.baez.duarte.natural.concrete.approx.predicate

Formal bridge question:

Can the positive-natural reciprocal finite approximation property be packaged as a reusable
predicate and connected back to the existing restricted concrete approximation predicate?

Expected output:

- a definition quantifying over all positive tolerances with coefficients indexed by
  `baezDuartePositiveNatIndex`;
- a theorem proving this predicate implies `nymanBeurlingRestrictedConcreteApprox`;
- proof by composing `exists_restricted_finsupp_integral_lt_of_baezDuarte` with the existing
  restricted-subtype-to-real-support bridge.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- Lean names:
  - `nymanBeurlingBaezDuarteConcreteApprox`;
  - `nymanBeurlingRestrictedConcreteApprox_of_baezDuarte`;
- completed as a predicate packaging step.

Result:

- the positive-natural reciprocal approximation property is now a reusable predicate;
- the predicate implies `nymanBeurlingRestrictedConcreteApprox` by composing the natural integral
  bridge with the restricted-subtype-to-real-support bridge.

M0 correction:

- this predicate measures only `(0,1)` error and is weaker than the published Baez-Duarte
  full-line statement;
- Batch `BATCH-20260710-M0-03` added
  `nymanBeurlingBaezDuarteFullLineConcreteApprox`, whose split error restores the tail and is
  definitionally separate from this local scaffold;
- only the full-line predicate is eligible for later M1 work.
- Batch `BATCH-20260710-M0-04` packages this predicate as exact target membership in the closure of
  the positive-natural kernels in real `L2(0,infinity)` and closes the endpoint mismatch. The
  coefficient-field/source-convention audit remains before M0 can be declared complete.
- Batch `BATCH-20260710-M0-05` proves the corresponding complex closure is equivalent to the real
  closure and the same finite-error predicate. The primary-source completion audit closes M0. M1
  must now formalize Baez-Duarte Theorem 1.1 against `Mathlib.RiemannHypothesis`; no local scaffold
  predicate may replace that equivalence.

Next action:

- protocol v2 reclassifies `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted` as a
  mechanical batch item, not a standalone research loop.

### T2.nyman.baez.duarte.natural.concrete.approx.unrestricted

Formal bridge question:

Can the packaged positive-natural predicate be connected to the existing unrestricted concrete
approximation predicate?

Expected output:

- a short theorem proving
  `nymanBeurlingBaezDuarteConcreteApprox → nymanBeurlingConcreteApprox`;
- proof by composing `nymanBeurlingRestrictedConcreteApprox_of_baezDuarte` with
  `nymanBeurlingConcreteApprox_of_restricted`.

Lean status:

- target recorded in `LeanLab/Riemann/Targets.lean`;
- planned one-step corollary; under protocol v2 it should be batched with adjacent engineering
  checks.
- M0 audit `AUDIT-20260710-M0-01` subsequently proved `nymanBeurlingConcreteApprox`
  unconditionally using parameters `1` and `-1`; this target is therefore obsolete and parked.

## M1: Baez-Duarte Theorem 1.1

The eligible theorem carrier after M0 is
`baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure`.

Audit `AUDIT-20260710-M1-01` splits the proof into two fixed-gap routes:

- forward: RH zero-free half-plane, Balazard-Saias quantitative Mobius estimate, kernel Mellin
  identity, weighted-log Fourier-Mellin `L2` isometry, and two convergence arguments;
- reverse: inclusion into the full Beurling closure followed by the base Nyman-Beurling criterion,
  whose classical proof uses half-plane Hardy-space factorization.

The RH-to-zero-free-half-plane interface is compiled. The quantitative Mobius estimate and base
criterion are theorem-level missing dependencies; neither may be replaced by the existing
absolute-convergence identity on `re(s) > 1`.

Batch `BATCH-20260710-M1-02` closes the fractional-kernel Mellin node with the compiled theorem
`hasMellin_fractionalPartKernel_one`; `hasMellin_baezDuarteKernel` supplies the exact
positive-natural scaling used in the paper. This removes one named G2 block but does not establish
either implication of Theorem 1.1.

Batch `BATCH-20260711-M1-03` closes the weighted-log Fourier-Mellin `L2` node with the compiled
equivalence `weightedLogPullback`, its forward and inverse representative formulas, and the
Fourier composition `baezDuarteFourierMellinL2`. The theorem `mellin_criticalLine_eq_fourier`
checks the source/mathlib frequency conversion `tau/(2*pi)`. The remaining forward route still
requires the quantitative Mobius and RH-to-Lindelof estimates plus source-specific convergence;
the reverse base criterion remains open.

Batch `BATCH-20260711-M1-04` resolves the broad source-convergence label into two source-accurate
chains. `baezDuarteVerticalMajorant_memLp` proves that `(1+|tau|)^(-1+beta)` is in `L2(R)` for
`beta < 1/2`, and its `2*epsilon` specialization closes the integrability step in the first chain.
For the unconditional `epsilon -> 0` chain, Lean proves that critical-line zeta-zero ordinates are
countable and null and that the source zeta ratio tends almost everywhere to one.

This batch does not close either convergence theorem. The fixed-epsilon chain still needs the
Balazard-Saias Mobius estimate and RH-to-Lindelof bound. The epsilon-to-zero chain still needs the
uniform zeta-ratio estimate of Baez-Duarte Lemma 2.2, whose proof requires a complex-Gamma
vertical-strip ratio estimate absent from current mathlib. Both chains still need the source's
weighted-to-unweighted tail transfer. The source TeX contains a malformed displayed Gamma ratio
and an exponent ambiguity in that tail passage, so the intended statements must be reconstructed
from definitions before they are eligible Lean premises. Result: `DEPENDENCY_GAP_IDENTIFIED`.

Batch `BATCH-20260711-M1-05` closes the shared weighted-to-unweighted tail-transfer block. Directly
from the source definition, Lean verifies that `f_(2*epsilon,n)` has exponent `1+2*epsilon` above
one, so the printed `1+epsilon` is not used. For any actual real `L2(0,infinity)` error with tail
`m/x`, Lean proves

```text
norm(f)^2 <= (1 + 2*epsilon) * norm(x^(-epsilon) * f)^2.
```

The theorem is formulated modulo almost-everywhere equality, yields the varying-epsilon convergence
transfer, and is instantiated on the project's natural-kernel finite sums. F3 is therefore closed.
The forward route is now concentrated on F1, the Balazard-Saias/RH-to-Lindelof estimate, and F2,
Baez-Duarte Lemma 2.2 plus complex-Gamma vertical-strip control. Result: `HARD_GAP_REDUCED`.

Batch `BATCH-20260711-M1-06` closes F2. An unchanged Apache-2.0 digamma-series module from
`PrimeNumberTheoremAnd` supplies logarithmic digamma growth on vertical strips. Continuous
Gronwall then gives a Gamma quotient bound with exponent `C*epsilon`; the completed-zeta
functional equation, conjugation, and the denominator-zero case convert it to the source zeta
ratio. Choosing an explicit smaller `epsilon0` makes `C*epsilon0 < 1/2`, and Lean proves all
transformed quotients on `[0,epsilon0]` are dominated by one explicit `L2(R)` power majorant. The
sharp but malformed printed Gamma display is not used. The forward route now has only F1,
Balazard-Saias plus RH-to-Lindelof; the reverse base criterion remains open. Result:
`HARD_GAP_REDUCED`.

Audit `AUDIT-20260711-M1-07` corrects the final forward dependency F1. Baez-Duarte's presentation
uses RH-to-Lindelof after the Balazard-Saias partial-sum estimate, but Burnol's published
`math/0202166` proof instead uses the unconditional critical-line convexity estimate
`|zeta(1/2+it)| = O(|t|^(1/4))`. Together with the arbitrary positive exponent in
Balazard-Saias, this gives an `L2` error majorant whenever that exponent is below `1/4`. Thus the
forward route does not intrinsically require formalizing Lindelof from RH. The corrected F1 consists
of the Balazard-Saias theorem and a critical-line zeta convexity bound with any exponent below
`1/2`. Neither theorem currently exists in pinned mathlib or a reusable licensed Lean project.
Result: `DEPENDENCY_GAP_IDENTIFIED`.

Batch `BATCH-20260711-M1-10` formalizes the exact remaining F1 interface without asserting it.
`BalazardSaiasEstimate` records all source quantifiers and constant dependencies, and RH supplies
its zero-free premise at `alpha=1/2`. Conditional on that explicit proposition, Lean proves
Burnol's transformed error is bounded by

```text
K * N^(-delta/3) * (1+|t|)^(-5/8+eta).
```

Lean separately proves this height majorant is in `L2(R)` for `eta<1/8` and that the `N` factor
tends to zero. The source theorem itself remains unproved, so the batch is
`FORMALIZATION_ONLY` with `hard_gap_delta=0`; the fixed frontier does not move.

Batch `BATCH-20260711-M1-11` audits the source-proof route against Titchmarsh Sections 3.12, 14.2,
and 14.25. The quantitative Mobius estimate decomposes into a truncated Perron formula, a
zero-free-region subpower bound for reciprocal zeta, and a rectangular contour shift with balanced
edge errors. Lean now upgrades mathlib's continuous logarithm lift to a holomorphic branch on any
simply connected zero-free open domain and instantiates it for zeta while explicitly excluding its
pole at `1`. The next source edge is the Borel-Caratheodory/Hadamard derivation of the reciprocal
zeta bound; Perron and contour balancing follow. Result: `DEPENDENCY_GAP_IDENTIFIED` with
`hard_gap_delta=0`; Balazard-Saias remains open.

Batch `BATCH-20260711-M1-12` compiles the RH reciprocal-zeta arbitrary-subpower bound on closed
critical substrips using the analytic logarithm, Borel-Caratheodory, Hadamard three-circles,
strictly sublinear logarithmic growth, and a compact low-height patch. This removes only the
reciprocal-zeta subedge of F1.

Batch `BATCH-20260711-M1-14` compiles the source-specialized truncated Perron formula with an
absolute `C*(N+1)^2/T` error. The proof includes the crossing-pole rectangle residue, both scalar
kernel bounds, dominated Mobius series integration, and half-integral logarithmic spacing. This
removes only the truncated-Perron subedge.

Batch `BATCH-20260711-M1-15` compiles the remaining RH-specialized contour shift and error balance.
The source reciprocal is represented by a holomorphic extension through `s=1`, not by Mathlib's
raw field inverse at its regularized point value. The residue-subtracted rectangle identity,
logarithmic left-edge integral, horizontal-edge estimates, and the choice
`T=(N+1/2)^3*(1+|Im(s)|)` yield the exact preregistered power bound. The compiled Burnol consumer
no longer assumes `BalazardSaiasEstimate`; RH-specialized F1 is closed. The stronger general-alpha
proposition and the reverse base criterion remain open, so M1 and RH are not proved.

Batch `BATCH-20260711-M1-16` compiles the reverse implication of the exact M0-aligned strong
Baez-Duarte carrier. Instead of asserting the more general Nyman-Beurling theorem, Lean applies the
source Mellin identity directly to full-line finite errors. The `(0,1)` part is controlled by
Holder, while the exact `m/x` tail is controlled by the reciprocal moment already present in the
M0 error formula. This excludes right-half-strip zeta zeros; completed-zeta reflection supplies the
full Mathlib RH statement. The remaining M1 theorem is the forward convergence assembly from RH to
closure; the separately compiled F1/F2/F3 components do not yet constitute that theorem.

## Tier 3: Horizon

### M1-18 Strong Baez-Duarte Criterion

Batch `BATCH-20260711-M1-18` compiles the remaining forward implication. It works directly with
finite weighted Mobius sums, proves their exact Mellin/Fourier formula, controls their transformed
error, performs an explicit diagonal epsilon limit, and removes the weight using the exact tail
estimate. The theorem `riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure` closes M1
and D. This is the published criterion formalized as an equivalence, not an unconditional proof
of RH.

`RiemannHypothesis` remains the orientation point. It is not an admissible immediate proof-loop
target.
