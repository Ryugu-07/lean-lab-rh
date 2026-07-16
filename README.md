# LeanLab: Riemann Hypothesis proof engineering in Lean 4

This public repository formalizes and stress-tests equivalent criteria and analytic infrastructure
around the Riemann hypothesis (RH). It is an ongoing research project. **It does not prove or
disprove RH.** Every claimed intermediate theorem is checked by Lean without `sorry`, project
axioms, or relaxed resource limits.

The formal target is mathlib's `RiemannHypothesis`. Current work concentrates on exact criterion
statements, their reverse implications, explicit-formula infrastructure, and falsification of
promising but invalid positivity mechanisms.

## Kernel-checked criterion spines

The following top-level equivalences compile in the current public tree. Names and quantifiers in
this table are intentionally close to the Lean statements; the links lead to their proofs.

| Criterion | Exact Lean conclusion |
| --- | --- |
| [Strong positive-natural Baez-Duarte closure](LeanLab/Riemann/BaezDuarteForwardLimit.lean#L1645) | `RiemannHypothesis ↔ baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure` |
| [All-index Li nonnegativity](LeanLab/Riemann/LiReverseCriterion.lean#L709) | `RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (liCoefficientCandidate n).re` |
| [Finite real Li-Weil Gram positivity](LeanLab/Riemann/LiWeilGram.lean#L319) | `RiemannHypothesis ↔ ∀ c : ℕ →₀ ℝ, 0 ≤ liWeilQuadratic c` |
| [Compact-support Weil arithmetic positivity](LeanLab/Riemann/WeilCompactPositivityCriterion.lean#L842) | For every finite zero-free `F : Finset ℂ` containing `0` and `1`, RH is equivalent to nonnegativity of `(compactWeilArithmeticQuadratic g).re` for every smooth compactly supported `g` whose compact Laplace transform vanishes on `F`. |

The compact criterion uses the project's arithmetic-side sign convention. Its proof includes the
compact explicit formula and a reverse separator argument; it does not establish the still-open
unconditional arithmetic positivity statement.

These are formalizations of known equivalence mechanisms, not a solution of RH. A bounded
[novelty and exposure audit](research/exposure_novelty_audit_20260716.md) records the literature
mapping and the repositories searched. No first-formalization priority claim is made.

## Reproduce the checks

The project is pinned to Lean `v4.31.0` and mathlib `v4.31.0` at commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.

```sh
lake exe cache get
lake build
lake env lean LeanLab/Riemann/Targets.lean
lake env lean LeanLab/Riemann/TargetChecks.lean
lake env lean LeanLab/Riemann/AxiomsAudit.lean
```

`AxiomsAudit.lean` prints the transitive axioms of the selected proof spine. The audited final
criteria use only Lean/mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
Recorded repository scans check for `sorry`, `admit`, `native_decide`, custom `axiom`/`constant`
declarations, `opaque`, and `unsafe` in the RH development. GitHub Actions runs the build on every
push and pull request.

## Vendored analytic foundations

Some analytic-number-theory dependencies are an audited source snapshot from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
at upstream commit `d963a6e694a05cd82e5f9b9ae7f4d94123e85393` (Apache-2.0). The snapshot was
introduced on 2026-07-10 and expanded through 2026-07-15. Its exact scope and update protocol are
documented in [PrimeNumberTheoremAnd/README.md](PrimeNumberTheoremAnd/README.md).

## Research status

Completed criterion edges do not reduce the mathematical truth of RH by themselves: each reverse
criterion turns a different positivity or approximation assertion back into RH. The principal open
frontiers are:

- extending the compact explicit-formula route to the intended full Weil test class (`W1`);
- proving an unconditional arithmetic positivity theorem rather than another RH-equivalent
  reformulation (`W2/G7`);
- attacking the open projection/Gram route (`G3/M2`);
- proving or disproving `RiemannHypothesis` itself.

See [the hard-gap DAG](research/hard_gap_dag.md), [route portfolio](research/route_portfolio.md),
and [attempt logs](attempts/README.md) for the proof ledger, eliminated branches, and public CI
evidence.

## Review status

The repository is being exposed for statement-level and definition-level review in parallel with
proof work. Clean-context reviews now cover both the earlier Baez-Duarte/contour surface and the
newer Li/Weil spine. A human-authored Zulip review request remains pending; exact review status is
tracked in the [exposure audit](research/exposure_novelty_audit_20260716.md).
