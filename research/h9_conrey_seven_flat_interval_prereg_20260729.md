# H9 Conrey Actual Seven Flat-Interval Preregistration

Date: 2026-07-29

Campaign: `FALSIFICATION-20260729-H9-CONREY-SEVEN-FLAT-INTERVAL-01`

Node: `H9-CONREY-ACTUAL-SEVEN-FLAT-INTERVAL-01`

Mode: `LITERATURE / FALSIFICATION / OMISSION_AUDIT`

Status: `FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS / FINAL_LEDGER_CI_REQUIRED`

## Baseline

- `parent_commit`: `490e779c23a7bc3f32a40624dfdfb1f7a13c2b91`.
- `parent_public_ci`: Lean Action run `30398241143`, build job `90406445477`, passed in
  `1m30s`.
- `previous_campaign`: H14 Turing completeness consumer, publicly closed at full local endpoint.
- `existing_H9_edge`: `ConreyCharacterSumRationality.lean` proves the exact weighted-prefix
  identity, the exhaustive flat-or-rational dichotomy, and a generic irrational countermodel.
- `material_difference`: this campaign uses the actual Legendre symbol modulo seven and the
  actual infinite Fourier series. It is not another generic affine countermodel.
- `global_goal`: active.

## Primary source and statement boundary

Primary source: Brian Conrey,
[*Character sums and the Riemann Hypothesis*](https://doi.org/10.4064/aa230530-13-11), Acta
Arithmetica 214 (2024), 327-342, registered as `SRC-CONREY-2024`.

The paper defines

```text
f_q(x) = sum_{n>=1} chi_q(n) * sin(2*pi*n*x) / n^2.
```

Proposition 1 states that `f_q(x)=0` implies `x` rational. The proof invokes Corollary 1, whose
printed hypotheses are `q>3`, squarefree, and `q congruent to 3 mod 8`. It overlooks the zero
first-moment case in the displayed affine expression. The paper later records the flat
alternative and calls it unlikely without excluding it.

This campaign tests the omitted mechanism at `q=7`. Since `7 congruent to 7 mod 8`, full success
does not refute the contextually scoped proposition, Conjecture 1, Theorem 3, or RH. It proves
that the flat branch occurs for a genuine neighboring quadratic character and that the modular
scope is mathematically material.

## Exact fixed endpoint

After the public preregistration gate, extend the H9 Conrey module or create one dedicated module
and compile the following without `sorry`.

1. Define the actual coefficient sequence from `legendreSym 7 n`.
2. Prove the exact period-seven table
   `0,1,1,-1,1,-1,-1` for every natural `n`.
3. Prove the actual prefix certificate

   ```text
   conreyPrefixMass chi_7 3 = 1
   conreyPrefixMoment chi_7 3 = 0.
   ```

4. Define the source-aligned infinite Fourier series

   ```text
   conreySevenFourier x =
     sum' n : Nat, chi_7(n) * sin(2*pi*n*x) / n^2.
   ```

   The natural-zero term must be shown harmless; no finite truncation may replace the series.
5. Define

   ```text
   K_7 = sin(2*pi/7) + sin(4*pi/7) - sin(6*pi/7)
   ```

   and prove the exact discrete sine-transform identity

   ```text
   K_7 * chi_7(n)
     = sin(2*pi*n/7) + sin(4*pi*n/7) - sin(6*pi*n/7).
   ```

6. Prove `K_7 != 0`, preferably by a kernel-checked positivity argument.
7. Use product-to-sum and Mathlib's Bernoulli cosine Fourier theorem to prove

   ```text
   x in [3/7,4/7] -> conreySevenFourier x = 0.
   ```

   All shifted Fourier arguments must be proved to lie in `[0,1]`; the Bernoulli-polynomial
   cancellation must be exact.
8. Give a concrete irrational witness in this interval, for example `sqrt(2)/3`, and prove

   ```text
   Irrational x and conreySevenFourier x = 0.
   ```

9. Prove the scope certificate `7 % 8 = 7` and `7 % 8 != 3`.
10. Package only these facts in an aggregate endpoint theorem.

Exact declaration names may follow local style.

## Success and partial criteria

`FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS` requires all ten clauses, a proven Target, an exact
open successor Target for the main `3 mod 8` family, exact TargetChecks, selected transitive
axiom prints with standard axioms only, empty forbidden scans, warning-as-error compilation, a
full build, and every public CI gate.

`MEANINGFUL_ACTUAL_CHARACTER_PARTIAL` requires clauses 1-6 and an exact compiled reduction of
clause 7 to one named unavailable Fourier/Bernoulli identity. A finite prefix alone is
infrastructure and does not satisfy meaningful partial.

`NO_FLAT_INTERVAL` applies if exact Fourier analysis disproves the navigation prediction. The
counter-result must compile and the false conjecture must be recorded.

`SCOPE_REPAIR` applies if the actual analysis reveals a source-valid theorem excluding the flat
branch for every permitted `q congruent to 3 mod 8`. Such a repair must be stated and compiled
separately; the `q=7` result cannot be promoted into the permitted family.

## Analytic plan and known obstacles

The intended proof multiplies the Fourier series by `K_7`, applies the discrete transform
identity termwise, and uses

```text
sin(a)*sin(b) = (cos(a-b)-cos(a+b))/2.
```

For `x in [3/7,4/7]`, the six shifts `x +/- j/7`, `j=1,2,3`, lie in `[0,1]`. Mathlib's
`hasSum_one_div_nat_pow_mul_cos` at exponent two evaluates each cosine series by the second
Bernoulli polynomial. The weighted shifts cancel because `1+2-3=0`.

Known formal obstacles are periodic trigonometric normalization, exact manipulation of `HasSum`
and `tsum`, simplification of the mapped Bernoulli polynomial, and proving `K_7` nonzero without
numeric approximation.

## Negative controls and claim boundary

- `ACTUAL_SERIES_REQUIRED`: the generic affine theorem and the finite prefix do not prove a zero
  of `f_7`.
- `NO_FLOATING_PREMISE`: numerical scans and partial sums are navigation only.
- `DOMAIN`: `q=7` is outside the `q congruent to 3 mod 8` RH-imitation family.
- `NO_SOURCE_REFUTATION`: full success does not classify the contextually scoped Proposition 1
  as false.
- `NO_MAIN_FAMILY_PROMOTION`: no flat prefix or irrational zero is claimed for any permitted
  `q congruent to 3 mod 8`.
- `NO_RH_DELTA`: Theorem 3, Conjecture 1, H9, and RH remain open.

Expected classification on full success:

- `historical_omission_mechanism_delta=1`;
- `actual_quadratic_character_delta=1`;
- `main_family_flat_branch_delta=0`;
- `source_refutation_delta=0`;
- `hard_gap_delta=0`;
- `rh_frontier_delta=0`.

## Runtime disclosure

- `model`: Codex, GPT-5 family; exact serving variant is not exposed.
- `reasoning_effort`: not exposed.
- `budget`: V4.1 has no numerical quota; no serving token budget is exposed.
- `compaction_state`: inherited-summary recovery occurred before route selection. Governance,
  historical-survey ruling, H9 prior attempt, current handoff, census, source registry, obstacle
  DAG, primary source, and worktree state were re-read.
- `protected_files`: the six inherited files remain untouched and unstaged.

## Production gate

No production Lean source, Target, TargetCheck, axiom-audit entry, or aggregate import may be
created or edited until this docs-only preregistration passes public Lean Action CI.

The persistent RH Goal remains active. Local completion returns to fresh cross-family historical
route selection, while a separately source-locked main-family repair may be ranked immediately.

## Implementation backfill

- `preregistration_commit`: `37852c81e2d71f1ee95520f62929204f094f34d5`.
- `preregistration_public_ci`: Lean Action run `30399568275`, build job `90410810937`, passed in
  `2m19s`.
- `local_result`: `FULL_ACTUAL_ADJACENT_FAMILY_FLAT_SUCCESS / LOCAL_AUDIT_PASS`.
- `compiled_endpoint`: all ten clauses compile, including the actual infinite Fourier series,
  full flat interval, irrational zero, and strict `7 mod 8` scope.
- `full_build`: `8788/8788`, passed locally.
- `implementation_commit`: `e259b79773d290435b332c119ad5c81ff0ac16dc`.
- `implementation_public_ci`: Lean Action run `30400822025`, build job `90414919121`, passed in
  `2m55s`.
- `proof_source_state`: frozen; diff at immutable-evidence creation is empty.
- `evidence_commit`: `d629fbd2fdacf1adf866831761f8e127ae3330c7`.
- `evidence_public_ci`: Lean Action run `30401127310`, build job `90415928990`, passed in
  `1m32s`.
- `next_gate`: publish one docs-only final ledger and require public CI.
