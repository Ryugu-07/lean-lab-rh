# R5 Polson GGC Continuation Audit Preregistration

Audit: `AUDIT-20260716-R5-POLSON-GGC-CONTINUATION-01`

Date: 2026-07-16

Status: `PUBLICLY_CLOSED`

## Source Claim Under Audit

Polson's 2018 arXiv v7 paper derives, initially for positive real `s`, a Levy-Frullani exponent
whose single exponential component is

```text
(exp(-s^2*t/2) - 1) * exp(-gamma^2*t) / t.
```

The paper later substitutes parameters with large imaginary part while continuing to use the same
integral. Its 2026 SSRN successors state the safer conclusion that the right-half-plane density is
unconditionally nonnegative while critical-line Thorin positivity is RH-equivalent. This audit
tests only the 2018 integral-domain passage; it does not reject that later equivalence framework.

Primary sources:

- Polson, *Riemann Hypothesis: a GGC factorisation*, arXiv:1806.07964v7:
  https://arxiv.org/abs/1806.07964v7
- Polson, *On Hilbert's 8th Problem: II*, SSRN 6898580:
  https://ssrn.com/abstract=6898580
- Polson, *Thorin Positivity, GGC Factorization and the Riemann Xi Function*, SSRN 6932859:
  https://ssrn.com/abstract=6932859

## Candidate Screen

1. **Unconditional centre-line GGC from the right-half-plane formula.** Rejected: the 2026 source
   describes centre-line Thorin positivity as RH-equivalent, not an unconditional consequence.
2. **Pointwise nonnegativity implies complete monotonicity abstractly.** Rejected: complete
   monotonicity contains all derivative-sign conditions and does not follow from pointwise sign.
3. **Every completely monotone density is a discrete unit-weight exponential sum.** Rejected:
   Bernstein representation gives a positive measure, not necessarily a discrete counting measure.
4. **Analytic continuation of the closed form preserves the original integral representation.**
   Rejected in the proposed test regime: the continued function may exist after the defining
   integral has ceased to converge.
5. **Single-component imaginary-axis divergence.** Survives the initial sign, boundary, and
   finite-component tests. It is selected as the exact source-specific falsification endpoint.

## Fixed Proposition

For `gamma>0` and `y^2>2*gamma^2`, substituting `s=i*y` into one exponential component gives

```text
(exp((y^2/2-gamma^2)*t) - exp(-gamma^2*t)) / t,
```

which is not integrable on `(1,infinity)`. The proposed Lean surface is

```lean
def polsonImaginaryFrullaniIntegrand (gamma y t : ℝ) : ℝ :=
  (Real.exp ((y ^ 2 / 2 - gamma ^ 2) * t) -
      Real.exp (-(gamma ^ 2) * t)) / t

theorem not_integrableOn_polsonImaginaryFrullaniIntegrand
    {gamma y : ℝ} (hgamma : 0 < gamma) (hy : 2 * gamma ^ 2 < y ^ 2) :
    ¬ IntegrableOn (polsonImaginaryFrullaniIntegrand gamma y) (Set.Ioi 1)
```

The formal module must also identify this real function with the real part of the exact complex
source component at `s=i*y`. Harmless naming and reassociation changes are allowed.

## Proof Plan

1. Set `c=y^2/2-gamma^2` and prove `c>0`.
2. Prove the growing exponential term divided by `t` tends to `+infinity`.
3. Prove the decaying correction divided by `t` tends to zero.
4. Deduce the source integrand tends to `+infinity` and is eventually at least one.
5. Use nonintegrability of the constant-one tail to contradict integrability of the component.
6. Lean-check the exact complex-to-real specialization.

## Adversarial Boundaries

- At `y^2=2*gamma^2`, the integrand behaves like `1/t` and still diverges, but this logarithmic
  boundary is not needed for the source-domain counterexample.
- For `y^2<2*gamma^2`, both exponentials decay at infinity; this audit makes no nonintegrability
  claim there.
- The theorem does not say that the analytic continuation of the resulting logarithm is absent.
  It says only that the original integral cannot represent it outside its convergence domain.
- No statement about the truth or falsity of RH follows.

## DAG Accounting

- `hard_gap_before`: G6/W1 and G7/W2 open; G3/M2 parked
- `hard_gap_after_if_complete`: unchanged
- `hard_gap_delta`: 0
- `assumption_frontier_before`: the 2018 continuation step has no checked convergence domain
- `assumption_frontier_after_if_complete`: that integral step is rejected beyond
  `y^2>2*gamma^2`; later RH-equivalent Thorin formulations remain available
- `classification_if_complete`: `BRANCH_ELIMINATED`

## Rejection Conditions

- Do not claim that the 2026 Thorin equivalence is false.
- Do not infer RH or its negation.
- Do not use numerical quadrature as proof.
- Reject any `sorry`, `admit`, `native_decide`, new axiom, unsafe declaration, or resource-limit
  relaxation.

## Lean Result

The fixed proposition is proved in `LeanLab/Riemann/PolsonGGCContinuationAudit.lean`. The module
also defines the exact complex source component and proves

```lean
theorem polsonImaginaryFrullaniComponent_eq_ofReal
theorem not_integrableOn_polsonImaginaryFrullaniIntegrand
theorem not_integrableOn_polsonImaginaryFrullaniComponent
```

under the preregistered hypotheses. The proof obtains a positive growth exponent, proves the
growing exponential quotient tends to `+infinity`, proves the correction tends to zero, and
contradicts integrability using the infinite measure of a real tail. Integrability of the complex
component would imply integrability of its real part, giving the complex endpoint.

## Local Verification

- Standalone module compilation and the dedicated module build pass without warnings.
- Exact `Targets.lean` and `TargetChecks.lean` checks pass.
- The three selected transitive axiom prints contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-token, declaration, resource-relaxation, and scratch-name scans are empty.
- `git diff --check` and the full 8,675-job build pass.

The local classification is `BRANCH_ELIMINATED`. This removes only the tested 2018
integral-retention mechanism. The RH hard-gap delta is zero, and the persistent RH Goal remains
active.

Implementation commit `0c174e82713c18be16ae9ea3afd5197b77ab4347` passed public Lean Action CI
run `29455171888`, build job `87486632024`, in `1m50s`. Immutable evidence is now backfilled; the
evidence commit must pass its own public CI before the audit closes.

Evidence commit `d277252fa21de89e228a2d1db6addd727d975d99` passed public Lean Action CI
run `29455360041`, build job `87487225276`, in `2m2s`. The audit is publicly closed as
`BRANCH_ELIMINATED`. Do not reopen the tested 2018 integral-retention mechanism without new source
evidence; return to fresh independent route selection under the still-active RH Goal.
