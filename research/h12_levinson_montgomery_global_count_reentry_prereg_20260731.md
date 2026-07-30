# H12 Levinson--Montgomery Global Count Re-entry Preregistration

Date: 2026-07-31

Campaign:
`LITERATURE-20260731-H12-LEVINSON-MONTGOMERY-GLOBAL-COUNT-REENTRY-01`

Selected node: `H12-LM-GLOBAL-INDENTED-COUNT-01`

Mode: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`

Status: `PREREGISTERED / PUBLIC_CI_REQUIRED / PRODUCTION_GATE_CLOSED`

## Primary source and fixed endpoint

The fixed source is Norman Levinson and Hugh L. Montgomery, *Zeros of the derivatives of the
Riemann zeta-function*, Acta Mathematica 133 (1974), 49--65, Theorem 1 and section 2:

`https://doi.org/10.1007/BF02392141`

The required endpoint remains the actual project formulation of the two source outputs:

```lean
theorem levinsonMontgomeryTheoremOne_actual :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy
```

The final theorem is an open target and is not an allowed premise.

## Material difference from the failed contour mechanism

The prior admissible-contour campaign proved that common zero-free horizontal segments and a
fixed `O(1)` bottom exist, but also proved that nonvanishing alone does not control winding.

This re-entry has two new inputs:

1. strict-left-half-plane winding and the actual `zeta'/zeta` endpoint formula now compile;
2. both actual top-side logarithmic-derivative argument variations now compile with a common
   `O(log(t+2))` bound at admissible heights.

It also targets a previously unproved source implication. The cofinal branch of
`levinsonMontgomery_integer_height_logDeriv_dichotomy` supplies strict negativity at every
nonzero interior point. Local zero factorization should force the entire open segment to be
zeta-zero-free, because the logarithmic derivative immediately to the right of an interior zero
has positive real part. Thus the source branch may produce the missing strict-negative
orientation rather than importing a numerical low-zero table.

## M0 definition alignment

1. `zeta` is Mathlib's `riemannZeta`; `zeta'` is `deriv riemannZeta`.
2. `logDeriv f s` is totalized as `deriv f s / f s`. No sign conclusion may be read at a zero.
   Every contradiction must use punctured nonzero points from an analytic factorization.
3. Integer-height points are exactly
   `levinsonMontgomeryIntegerPoint sigma n = sigma + n*I`.
4. The source open counting region is
   `0 < Im(s)`, `0 < Re(s)`, `Re(s) < 1/2`, with strict height cutoff `Im(s) < T`.
5. Zeta and derivative zeros retain the existing analytic multiplicities
   `burnolZetaZeroMultiplicity` and `riemannZetaDerivZeroMultiplicity`.
6. Critical-line zeta zeros are not counted by the open-left count. They must be excluded by a
   left indentation carrying their actual multiplicity; zero simplicity is not allowed.
7. `LevinsonMontgomeryLogCountBound`, `LevinsonMontgomeryExactCountSequence`, and
   `LevinsonMontgomeryCountDichotomy` retain their existing definitions.
8. The actual top variation uses the continuous logarithmic-derivative integrals, not endpoint
   principal arguments.

## Fixed proof chain

Full success must compile the following chain.

1. Generalize the existing critical-line zeta factorization to every actual nontrivial zero:

   ```lean
   exists_riemannZeta_zero_analytic_factor
   ```

   with positive multiplicity, analytic nonzero residual, and an eventual exact factorization.

2. Prove the punctured positive-right control: for an analytic zero factor of positive
   multiplicity, sufficiently small positive real displacements have nonzero function value and
   strictly positive real logarithmic derivative.

3. Deduce that `LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n` excludes every zeta zero
   with `0 < Re(s) < 1/2` and `Im(s)=n`. Deduce actual derivative nonvanishing and strict
   negativity throughout the open horizontal segment.

4. Add the left-boundary theorem and split at the critical endpoint. If zeta is nonzero there,
   obtain an actual `SpeiserStrictNegativeHorizontal`. If it is zero, instantiate the compiled
   multiplicity-aware negative left semicircle. Package this as the actual negative-height top
   geometry.

5. Combine step 4 with the existing integer-height dichotomy:

   ```text
   cofinally many actual strict-negative/indented heights
   or
   eventually speiserUpperLeftZetaZeroCount(T) > T/2.
   ```

6. Prove a multiplicity-aware argument principle for the actual zeta and zeta-derivative
   divisors on a finite rectangle or equivalent finite indented contour. The proof may divide out
   the finite zero polynomial and integrate the analytic nonvanishing residual. It may not assume
   a generic argument principle that is absent from Mathlib.

7. Prove the exact contour count-difference identity. Critical-line zeta-zero indentations must
   contribute the correct multiplicity and open-left convention; no boundary zero may be silently
   discarded.

8. Use the compiled actual top `O(log(t+2))` bounds and fixed-bottom `O(1)` contribution to prove
   `LevinsonMontgomeryLogCountBound`. Extend from admissible heights to every sufficiently large
   real cutoff by proving a zero-free short-height transfer for both finite counts.

9. In the cofinal strict-negative/indented branch, use the compiled principal-log winding result
   and step 7 to prove `LevinsonMontgomeryExactCountSequence`. In the other branch use the already
   compiled dense-count theorem. Conclude `LevinsonMontgomeryCountDichotomy`.

10. Return the exact full endpoint
    `LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy`.

## Required intermediate API

Names may change, but exact TargetChecks must expose equivalents of:

```lean
theorem levinsonMontgomery_negativeIntegerHeight_interiorZeroFree
    {n : ℕ} (hn : 10 ≤ n)
    (hneg : LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) :
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 / 2 →
      riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0

theorem levinsonMontgomery_negativeIntegerHeight_interiorGeometry
    {n : ℕ} (hn : 10 ≤ n)
    (hneg : LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) :
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 / 2 →
      riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
      deriv riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
      (speiserZetaDerivRatio
        (levinsonMontgomeryIntegerPoint sigma n)).re < 0
```

The source-branch aggregate must retain enough data to construct either a complete strict-negative
horizontal or a single actual critical-endpoint indentation at each selected height.

## Success, meaningful partial, and falsification

`FULL_SUCCESS` requires all ten proof-chain steps, exact TargetChecks, selected standard-only
axiom prints, empty forbidden scans, a full build, public implementation CI, and immutable public
evidence.

`MEANINGFUL_PARTIAL` is allowed only after steps 1--5 compile and the campaign makes three
materially different attacks on the first exact unavailable theorem among steps 6--10. The first
unavailable theorem must be recorded in theorem-shaped form. Steps 1--5 alone do not close the
selected global-count node.

The proposed omission repair is falsified if a no-sorry Lean model satisfies the exact
negative-height predicate while carrying an interior zeta-shaped analytic zero, or if the
positive-right principal part can be canceled by an analytic nonzero residual arbitrarily close
to the zero.

The full campaign is blocked, but not falsified, if the actual finite divisor cannot be globally
factored with the available analytic API, if indentation bookkeeping cannot preserve the source
open-boundary convention, or if the all-real-cutoff transfer needs a new local zero-count estimate.

## Negative controls

- Do not evaluate `logDeriv` at a zero.
- Do not assume zero simplicity.
- Do not replace continuous argument variation by principal endpoint arguments.
- Do not infer zero winding from nonvanishing alone.
- Do not identify support cardinality with multiplicity without proof.
- Do not prove only a generic analytic theorem and claim the actual zeta instantiation.
- Do not weaken the full endpoint to the new interior-zero exclusion theorem.
- Do not use `LevinsonMontgomeryLogCountBound`,
  `LevinsonMontgomeryCountDichotomy`, Speiser equivalence, derivative-zero-freeness, or RH as a
  premise.

## Claim boundary

Expected full-success classification:

- `result=LEVINSON_MONTGOMERY_THEOREM_ONE_FORMALIZED`;
- `historical_route_coverage_delta=1`;
- `negative_height_zero_exclusion_delta=1`;
- `global_argument_principle_delta=1`;
- `levinson_montgomery_count_delta=1`;
- `speiser_equivalence_delta=1` through the existing consumer;
- `derivative_zero_free_delta=0`;
- `rh_frontier_delta=0`;
- `rh_proved=0`.

Even full success formalizes a known route and the equivalence consumer. It does not establish the
zero-free side of Speiser's criterion.

## Production gate

No edit is allowed to `LeanLab/`, `LeanLab/Riemann/Targets.lean`,
`LeanLab/Riemann/TargetChecks.lean`, `LeanLab/Riemann/AxiomsAudit.lean`, or `LeanLab.lean` until
this docs-only preregistration passes public Lean Action CI.

The protected inherited files remain untouched and unstaged. The persistent RH Goal remains
active.
