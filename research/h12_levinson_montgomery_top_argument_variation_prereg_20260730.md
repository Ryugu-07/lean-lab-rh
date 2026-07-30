# H12 Levinson--Montgomery Top Argument Variation Preregistration

Date: 2026-07-30

Campaign:
`LITERATURE-20260730-H12-LEVINSON-MONTGOMERY-TOP-ARGUMENT-VARIATION-01`

Selected node:
`H12-LM-JENSEN-TOP-VARIATION-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `FULL_FIXED_ENDPOINT_SUCCESS / LOCAL_AUDIT_GREEN /
PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Historical statement

Levinson--Montgomery 1974, page 52, says that a standard application of Jensen's theorem
shows that the changes in argument of `zeta(sigma+i*t)` and `zeta'(sigma+i*t)` from
`sigma=1` to `sigma=0` are `O(log t)`.

Primary source:

`https://doi.org/10.1007/BF02392141`

The preceding campaign has compiled the actual Jensen divisor counts and crossing-support
inclusions. This campaign reconstructs the omitted crossing-to-continuous-argument conversion.

## M0 definitions

Define a full top-height admissibility predicate with the literal source segment:

```lean
def LevinsonMontgomeryTopAdmissible (t : Real) : Prop :=
  0 < t ∧
    ∀ sigma ∈ Set.Icc (0 : Real) 1,
      riemannZeta (sigma + t * Complex.I) ≠ 0 ∧
      deriv riemannZeta (sigma + t * Complex.I) ≠ 0
```

The canonical continuous argument changes will be represented by

```lean
((∫ sigma : Real in (0 : Real)..1,
    logDeriv riemannZeta (sigma + t * Complex.I))).im
```

and

```lean
((∫ sigma : Real in (0 : Real)..1,
    logDeriv (deriv riemannZeta) (sigma + t * Complex.I))).im.
```

Reversing the source orientation from `1 -> 0` changes only the sign. The absolute bound is
unchanged.

For the derivative crossing count, retain

```text
exp(i*t*log 2) * zeta'(sigma+i*t).
```

The phase is constant in `sigma`, and the omitted factor `2^sigma` in the source normalization
is positive real. Thus neither changes the continuous argument variation along the horizontal
segment, while the phase is essential for the already compiled crossing count.

## Fixed proof chain

Full success must compile all of the following.

1. Prove that common zero-free top heights for both actual divisors on `[0,1]` occur above
   every prescribed height. The proof must use local finiteness of the actual zeta and
   derivative divisors, not a numerical zero table.
2. Prove interval integrability on `[0,1]` of the two actual logarithmic derivatives at every
   admissible height.
3. Prove a generic one-gap theorem. If a differentiable nonvanishing path has no real-part
   crossing in the interior of `[a,b]`, its logarithmic-derivative integral has imaginary part
   of absolute value at most `pi`.
4. The one-gap proof must choose the appropriate right or left half-plane on that gap and use
   a valid local logarithm. It may use `Complex.log g` or `Complex.log (-g)` on each gap.
   It may not identify a global continuous change with the discontinuous principal argument.
5. Prove the finite-crossing theorem by sorting or recursively partitioning an arbitrary
   finite crossing superset. Endpoint crossings must be handled, and the bound must be
   `pi * (card S + 1)` or stronger.
6. For each actual symmetrization, construct a finite real crossing superset from the real
   projection of its Jensen divisor support. Use the existing pointwise crossing-support
   theorem.
7. Prove that the cardinality of that real support projection is at most the
   multiplicity-bearing divisor sum. The proof must use analyticity to exclude poles and show
   that every support value contributes at least one.
8. Compose the generic finite-crossing theorem with the existing actual Jensen
   `O(log(t+2))` estimates and absorb the additive one.
9. Produce a cofinal selected-height corollary satisfying both actual top-side bounds
   simultaneously.

## Required actual endpoint

The final API may separate constants, but exact TargetChecks must expose an equivalent of:

```lean
∃ C T0 : Real, 0 ≤ C ∧
  ∀ t : Real, T0 ≤ t →
    LevinsonMontgomeryTopAdmissible t →
      abs ((∫ sigma : Real in (0 : Real)..1,
        logDeriv riemannZeta (sigma + t * Complex.I)).im) ≤
          C * Real.log (t + 2) ∧
      abs ((∫ sigma : Real in (0 : Real)..1,
        logDeriv (deriv riemannZeta) (sigma + t * Complex.I)).im) ≤
          C * Real.log (t + 2)
```

and a cofinal corollary:

```lean
∀ B : Real, ∃ t : Real, B < t ∧
  LevinsonMontgomeryTopAdmissible t ∧
  -- both preceding O(log(t+2)) inequalities
  True
```

The actual theorem may use two constants before taking their maximum.

## Lean shape of the generic bridge

The implementation should expose a theorem equivalent to:

```lean
theorem abs_im_intervalIntegral_deriv_div_le_of_crossings_subset
    {g g' : Real → Complex} {a b : Real} (hab : a ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hint : IntervalIntegrable (fun x => g' x / g x) volume a b)
    (hne : ∀ x ∈ Set.Icc a b, g x ≠ 0)
    (S : Finset Real)
    (hcross : ∀ x ∈ Set.Icc a b, (g x).re = 0 → x ∈ S) :
    abs ((∫ x : Real in a..b, g' x / g x).im) ≤
      Real.pi * (S.card + 1)
```

Harmless changes in coercions or a stronger bound are allowed. Supplying an already ordered
partition as an unproved extra premise is not full success.

## Falsification and boundary tests

1. A nonvanishing path can wind many times while its endpoint principal arguments agree.
   Therefore a global principal-log endpoint subtraction is invalid without a half-plane
   partition.
2. Removing nonvanishing permits a logarithmic-derivative singularity at a crossing and cannot
   yield the actual integral statement.
3. Distinct crossings are controlled by divisor support cardinality, while Jensen gives a
   multiplicity sum. The direction `card support <= multiplicity sum` must be proved; silently
   replacing one by the other is forbidden.
4. The preceding uniform Jensen center-lower-bound mechanism fails for the unnormalized
   derivative real part because its dominant term rotates with `t`; the compiled phase
   normalization must be retained.
5. A finite crossing theorem alone is infrastructure. Full success requires both actual zeta
   instantiations and cofinal admissible heights.
6. An `O(log t)` bound on principal endpoint arguments is vacuous and is not the continuous
   source variation.

## Known obstacles

- Mathlib has no packaged crossing-count-to-argument-variation theorem.
- The finite support must be converted to a sorted or recursively consumed real partition.
- Adjacent gaps may have crossings at both endpoints; the local logarithm proof must allow
  weak half-plane containment at endpoints while preserving nonvanishing.
- The derivative path needs a real-parameter derivative for `deriv riemannZeta` and exact
  cancellation of the constant phase in its logarithmic derivative.
- The divisor is integer-valued; the cardinality comparison and later real coercions must not
  lose positivity or multiplicity.

## Success and local stop

`FULL_FIXED_ENDPOINT_SUCCESS` requires all nine proof-chain steps, exact TargetChecks,
standard-only axiom audit, empty forbidden scans, full build, and public immutable evidence.

`MEANINGFUL_PARTIAL` requires the no-sorry generic finite-crossing theorem, the exact first
failed actual instantiation, and a recorded obstruction. A theorem conditional on a supplied
ordered partition is infrastructure and does not close the node.

`LOCAL_STOP` occurs after one of:

1. full endpoint success and public closure;
2. three materially different failed attacks on the same exact generic or actual bridge, with
   the first unavailable theorem recorded;
3. a Lean counterexample falsifies the proposed generic bridge.

Any local stop returns to cross-family route selection. The persistent RH Goal remains active.

## Claim boundary

Expected full-success classification:

- `result=LEVINSON_MONTGOMERY_ACTUAL_TOP_ARGUMENT_VARIATION_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `generic_crossing_variation_bridge_delta=1`;
- `actual_zeta_top_variation_delta=1`;
- `actual_zeta_deriv_top_variation_delta=1`;
- `global_argument_principle_delta=0`;
- `levinson_montgomery_count_delta=0`;
- `speiser_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

The global indented argument principle, the exact bottom orientation needed by one branch,
both Levinson--Montgomery count outputs, Speiser equivalence, H12, and RH remain open unless
separately compiled.

## Production gate

No `LeanLab/`, `LeanLab/Riemann/Targets.lean`, `LeanLab/Riemann/TargetChecks.lean`,
`LeanLab/Riemann/AxiomsAudit.lean`, or `LeanLab.lean` edit is allowed until this docs-only
preregistration passes public Lean Action CI.

The production gate passed at commit `01a51d79a350f4dd4d9a8bf46bd3458b9ec44ff2`,
Lean Action run `30532626405`, build job `90838279704`, in `1m37s`.

## Local outcome

All nine fixed proof-chain steps compile in the 946-line no-sorry
`LeanLab/Riemann/LevinsonMontgomeryTopArgumentVariation.lean`.

The generic theorem partitions a nonvanishing differentiable path at a finite real-part
crossing superset and proves

```text
abs(Im integral(g'/g)) <= pi * (card crossings + 1).
```

Each crossing-free gap uses its own valid right- or left-half-plane logarithm. The actual
zeta and phase-normalized zeta-derivative crossings are charged to their Jensen divisor
supports, support cardinality is charged to multiplicity, common zero-free heights on
`[0,1]` occur cofinally, and the phase cancels exactly from `zeta''/zeta'`.

Nine exact TargetChecks and eight selected axiom prints pass warning-as-error. The selected
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. The forbidden scan and
`git diff --check` are empty; full `lake build` passes `8816/8816` with inherited warnings only.

The implementation must now pass public Lean Action CI before immutable evidence is published.
The global indented argument principle, bottom orientation, both Levinson--Montgomery count
outputs, Speiser equivalence, H12, and RH remain open.
