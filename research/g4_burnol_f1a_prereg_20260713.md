# G4-F1a Burnol Explicit A Pre-Registration

Date: 2026-07-13

Batch ID: `BATCH-20260713-G4-F1A`

## Fixed Target

- `node_id`: `B1`
- `gap_id`: `G4/F1a`
- `work_class`: `SOURCE_FORMALIZATION`
- `novelty_label`: `KNOWN_MATHEMATICS`
- `status`: complete

This batch must formalize Burnol's explicit source function `A` as one indivisible source edge. It
may not stop after a definition, support lemma, `L2` estimate, or local integral identity.

## Exact Lean Surface

The batch will add a `BurnolA.lean` module containing at least:

```text
burnolA
burnolA_eq_zero_of_one_lt
burnolA_eq_tailIntegral_sub_fractionalPart
burnolA_memLp_two_positiveHalfLine
burnolComplexAL2
burnolComplexAL2_coeFn
hasMellin_burnolA
```

For positive `t`, the source-facing definition is

```text
n = floor(1/t)
A(t) = n*log(t) + log(n!) + n.
```

The central transform statement is

```text
HasMellin (fun t : Real => (burnolA t : Complex)) s
  ((s-1) * riemannZeta s / s^2)
```

for `0 < Re(s) < 1`.

## Proof Route

The implementation will use the exact tail-Hardy representation

```text
A(t) = integral_(u>t) rho(1/u)/u du - rho(1/t),   t>0.
```

This representation fixes the source floor formula, including the contribution
`integral_(1,infinity) u^-2 du = 1` that supplies the apparent endpoint constant.

1. Prove the tail integral formula by reciprocal substitution and a finite partition at the
   integers up to `floor(1/t)`.
2. Use `0 <= rho < 1` to derive `|A(t)| <= 2 + |log t|` on `(0,1]`; use the exact support lemma
   for `t>1`. This proves `L2` membership.
3. Prove the Mellin transform of the tail integral by Fubini on
   `{(t,u) : 0<t<u}`. Mellin convergence of `rho(1/t)` supplies absolute integrability, and the
   inner power integral contributes `1/s`.
4. Combine with `hasMellin_fractionalPartKernel_one` to obtain Burnol's `Z(s)`.

The earlier Stirling decomposition remains a fallback bound, but success is judged only by the
compiled source-facing statements above.

## Frontier

- `hard_gap_before`: G4/F1a open; F1b-F5 open; M2/G3 unchanged.
- `assumption_frontier_before`: the explicit formula and exact transform are external source facts.
- `expected_hard_gap_delta`: close F1a only and select F1b next.
- `anti_tautology_gate`: defining `A` as an abstract unitary image does not satisfy the target.

## Result Rules

- `KNOWN_THEOREM_FORMALIZED`: every central statement compiles and is present in exact
  `TargetChecks`/axiom witnesses.
- `DEPENDENCY_GAP_IDENTIFIED`: Lean exposes a missing source-level analytic theorem and the batch
  records its exact statement without claiming F1a complete.
- `BRANCH_FALSIFIED`: the explicit source formula, sign, or transform is inconsistent.
- `NO_PROGRESS`: only definitions or generic wrappers compile.

## Runtime Record

- `model`: Codex, GPT-5 family (exact backend identifier not exposed)
- `reasoning_effort`: not exposed
- `loop_budget`: unbounded persistent-goal budget
- `compaction_since_previous_loop`: yes; one automatic compaction occurred during implementation,
  after the explicit tail identity and before the `L2`/Fubini stages. Work resumed from the
  retained summary without changing the preregistered target.

## Result

- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `hard_gap_after`: G4/F1a complete; F1b selected next; F2-F5 and M2/G3 unchanged.
- `hard_gap_delta`: the fixed source edge F1a is closed. This is formalization of Burnol's known
  proposition, not an unconditional RH advance.
- `assumption_frontier_after`: no source formula remains assumed for `A`. Lean checks the explicit
  floor formula, support, Hardy-tail identity, square-integrability, complex `L2` representative,
  absolute two-variable Fubini kernel, and exact Mellin transform.
- `Lean_surface`: `burnolA`, `burnolA_eq_zero_of_one_lt`,
  `burnolA_eq_tailIntegral_sub_fractionalPart`, `burnolA_memLp_two_positiveHalfLine`,
  `burnolComplexAL2`, `burnolComplexAL2_coeFn`, `hasMellin_burnolA`.
- `axiom_audit`: only `propext`, `Classical.choice`, and `Quot.sound`.
- `commit_SHA`: pending
- `public_CI`: pending
