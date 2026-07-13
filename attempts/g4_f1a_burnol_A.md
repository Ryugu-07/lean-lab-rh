# G4-F1a Burnol Explicit A

Date: 2026-07-13

- `batch_id`: `BATCH-20260713-G4-F1A`
- `node_id`: `B1`
- `gap_id`: `G4/F1a`
- `work_class`: `SOURCE_FORMALIZATION`
- `result_class`: `KNOWN_THEOREM_FORMALIZED`
- `hard_gap_before`: F1a selected; F1b-F5 open; M2/G3 unchanged.
- `hard_gap_after`: F1a complete; F1b selected; F2-F5 and M2/G3 unchanged.
- `hard_gap_delta`: closed the fixed explicit-function source edge only.

## Target

Formalize as one indivisible batch Burnol's explicit

```text
A(t) = floor(1/t)*log(t) + log(floor(1/t)!) + floor(1/t)
```

together with support, `L2(0,infinity)` membership, and

```text
HasMellin A s ((s-1)*zeta(s)/s^2),  0 < Re(s) < 1.
```

## Successful Route

1. Partition the reciprocal variable at integer intervals and integrate `fract(x)/x` exactly.
   Reciprocal substitution proves the source-facing Hardy-tail identity. The contribution from
   `u>1` is exactly `1`, which supplies the floor formula's final constant.
2. Bound the tail on `(0,1]` by `1-log(t)` and use `0<=rho<1` to prove
   `|A(t)|<=2+|log(t)|`. Mathlib's `abs_log_mul_self_rpow_lt` with exponent `1/4` gives the
   square majorant `36*t^(-1/2)`; support makes the function zero on `(1,infinity)`.
3. Define the two-variable complex kernel on `{(t,u):0<t<u}`. Its norm slice is exactly
   `(1/Re(s))*u^(Re(s)-1)*rho(1/u)`, so the already verified Mellin convergence of the fractional
   kernel proves absolute product integrability.
4. Apply Bochner Fubini. Integrating first in `u` gives the Mellin transform of the Hardy tail;
   integrating first in `t` gives `1/s` times the fractional-kernel Mellin transform. Subtracting
   the base kernel yields `(s-1)*zeta(s)/s^2`.

## Rejected Or Corrected Routes

- Defining `A` as an abstract unitary image was rejected by the preregistered anti-tautology gate.
- A Stirling decomposition was retained only as fallback; the exact tail formula gave a shorter
  source-facing `L2` proof.
- An initial tail reading omitted `u>1`; Lean-level evaluation exposed the missing contribution
  `integral_1^infinity u^-2 du=1`, correcting the apparent constant mismatch before it propagated.
- No ready-made Hardy-tail Mellin theorem exists in the pinned mathlib, so the required Fubini
  argument was proved locally with explicit absolute integrability rather than assumed.

## Lean Surface And Audit

- Module: `LeanLab/Riemann/BurnolA.lean`.
- Central names: `burnolA_eq_zero_of_one_lt`,
  `burnolA_eq_tailIntegral_sub_fractionalPart`, `burnolA_memLp_two_positiveHalfLine`,
  `burnolComplexAL2_coeFn`, `mellin_burnolComplexFractionalPartTail_eq`,
  `hasMellin_burnolA`.
- Exact witnesses compile in `TargetChecks.lean`.
- Trusted dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `sorryAx`, project `axiom`, or project `constant` is permitted.
- `model`: Codex, GPT-5 family (exact backend identifier not exposed).
- `reasoning_effort`: not exposed.
- `budget`: unbounded persistent-goal budget.
- `compaction_state`: one automatic compaction occurred during implementation; work resumed from
  the retained state without changing the target.
- `commit_SHA`: `6800d29b2b197e8d2ae33a3c3dd6c0298a05ad73`.
- `public_CI`: success, run `29228962278`, build job `86748844527`.
