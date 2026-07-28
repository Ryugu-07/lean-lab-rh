# H8 Conrey--Li RKHS-Shift Preregistration

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H8-CONREY-LI-RKHS-SHIFT-01`

Node: `H8-CONREY-LI-RKHS-SHIFT-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED`

## Primary-source anchor

The fixed source is Conrey--Li (1998), Theorem 2 and the proof immediately following it:

`https://arxiv.org/abs/math/9812166`

For an analytic nonvanishing function `W` on the upper half-plane, the source uses

```text
K(w,z) = W(z) * conj(W(w)) / (2*pi*i*(conj(w)-z)).
```

If a linear operator `T` sends `K(w,-)` to `K(w+i,-)` and
`Re <F,T F> >= 0` for every RKHS vector `F`, the source first derives positivity of

```text
K(w+i,z) + K(w,z+i),
```

then `Re(W(z)/W(z+i)) >= 0` and

```text
B(z) = (W(z)-W(z+i))/(W(z)+W(z+i)),  |B(z)| <= 1
```

on the original upper half-plane. A second Hardy-RKHS argument extends these conclusions to
`Im z > -1/2`.

## Exact fixed endpoint

The production module must prove the following without `sorry`.

1. Define the upper-half-plane shift `w |-> w+i`, the source-normalized Conrey--Li kernel, the
   shifted-ratio predicate, and the Cayley transform.
2. State a scalar Mathlib `RKHS` alignment in which
   `RKHS.kernel H z w 1` is exactly the source expression `K(w,z)`.
3. For a complex-linear operator `T` satisfying
   `T (RKHS.kerFun H w 1) = RKHS.kerFun H (w+i) 1`, prove that
   `Re <F,T F> >= 0` implies the source finite-combination positivity statement for the
   symmetrized shifted kernel.
4. Specialize the positivity to one kernel vector and prove, using the explicit kernel formula
   and nonvanishing of `W`, that
   `Re(W(w)/W(w+i)) >= 0` for every `w` in the upper half-plane.
5. Prove a generic Cayley lemma: if `r.re >= 0`, then `r+1` is nonzero and
   `norm ((r-1)/(r+1)) <= 1`.
6. Identify the generic Cayley expression with the source `B` and deduce `norm(B(w)) <= 1`.
7. Compile an aggregate endpoint containing only the proved assumptions and conclusions.

Exact declaration names may follow local style. Mathlib's inner product is conjugate-linear in
the first argument; the source notation uses the opposite convention. Since only real parts
are compared, the translation must be proved rather than handled by an informal convention
swap.

## Success criteria

`FULL_UPPER_HALF_PLANE_PRODUCER_SUCCESS` requires all seven clauses, one registered Target,
exact TargetChecks, selected transitive axiom prints with standard axioms only, empty forbidden
scans, warning-as-error compilation, a full build, and every public CI gate.

`MEANINGFUL_PARTIAL` requires clauses 1, 2, and 4--7, with the finite-combination expansion in
clause 3 or the first unavailable second-stage Hardy-RKHS edge isolated in exact theorem form.

`FALSIFIED` applies if the source-aligned RKHS, shift, positivity, explicit-kernel, and
nonvanishing hypotheses do not imply upper-half-plane ratio nonnegativity. The failure must
record the first invalid orientation, sign, or functional-analytic step.

## Negative controls and claim boundary

- `SOURCE_QUANTIFIER`: the paper assumes `>= 0`, not strict positivity. No zero-vector defect is
  claimed.
- `INNER_CONVENTION`: source and Mathlib inner products use opposite linearity conventions; only
  a compiled real-part identity may bridge them.
- `SHIFT_DIRECTION`: `w -> w+i` and `z -> z+i` are not interchangeable in the kernel.
- `DENOMINATOR_SIGN`: on the diagonal shifted kernel,
  `2*pi*i*(conj(w)-w-i)` is a positive real scalar after simplification; the proof must expose
  this sign.
- `NONVANISHING`: Mathlib division is totalized. The ratio theorem must retain
  `W(w+i) != 0` rather than obtaining a vacuous statement at a zero.
- `WEAK_VS_STRICT`: semipositivity yields `Re ratio >= 0` and `norm B <= 1`, not strict
  inequalities.
- `FINITE_COMBINATION`: a diagonal inequality alone is weaker than positive-definiteness of the
  complete symmetrized shifted kernel.
- `HALF_STRIP`: upper-half-plane contraction does not imply analytic extension to
  `Im z > -1/2`. The source's second RKHS, multiplier, density, adjoint, and identity-theorem
  argument remain explicit open inputs unless independently compiled.
- `ACTUAL_XI`: no concrete `F(W)` for `W(z)=1/xi(1-i*z)`, positive shift operator, unconditional
  counterexample, H8, or RH result is claimed.

Expected classification:

- `historical_route_coverage_delta=1`;
- `rkhs_source_bridge_delta=1`;
- `upper_half_plane_ratio_delta=1`;
- `half_strip_extension_delta=0`;
- `actual_xi_operator_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Production gate

No production Lean source, Target, TargetCheck, or axiom-audit entry may be created or edited
until this docs-only preregistration passes public Lean Action CI.

The persistent RH Goal remains active. A local stop returns to fresh cross-family route
selection after the full evidence chain.
