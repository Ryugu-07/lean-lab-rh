# R5 Weil Gaussian Height-Limit Preregistration

Campaign: `CAMPAIGN-20260716-R5-WEIL-GAUSSIAN-HEIGHT-LIMIT-01`

Date: 2026-07-16

Status: `PUBLIC_IMPLEMENTATION_VERIFIED_PENDING_EVIDENCE_CI`

## Source Boundary

Lagarias Appendix A defines the Weil zero functional by a symmetric height cutoff and requires an
unconditional test class analytic across the complete closed critical strip. The preceding project
campaign proves the exact finite-height weighted xi argument principle, but not its height limit.
The previously considered generic `A_delta` successor was correctly deferred because boundedness
on a closed strip gives no vertical decay.

This campaign introduces genuinely new route evidence by fixing the symmetric entire Gaussian

```text
G_a(s) = exp(a * (s - 1/2)^2),    a > 0.
```

It has exact reflection symmetry and Gaussian decay on horizontal lines. The intended proof uses
only the already compiled squared-reciprocal xi-zero summability to obtain a coarse polynomial
zero count, select quantitatively separated heights, bound the compensated Hadamard logarithmic
derivative there, and let the Gaussian dominate that polynomial bound.

Primary sources:

- https://www.numdam.org/item/10.5802/aif.2311.pdf, Appendix A (A.3)-(A.5)
- https://arxiv.org/abs/2312.00108, especially its Gaussian Mellin weight in formula (3)

The second source assumes RH and simple zeros for a shifted zero-isolation application. This
campaign does neither: it targets an unconditional global multiplicity-bearing zero sum centered
at the critical line.

## Route Map And Candidate Audit

| Candidate | Exact adversarial result | Decision |
|---|---|---|
| C1: generic `A_delta` height limit | Closed-strip boundedness does not control either horizontal edge; this repeats the normalized frontier already deferred. | Reject without new decay evidence. |
| C2: symmetric Gaussian xi height limit | `G_a(x+iT)` contributes `exp(-a*T^2)` uniformly on the fixed horizontal segment. Existing `sum norm(rho)^(-2)` can supply both absolute Gaussian zero summability and a coarse polynomial boundary estimate along selected heights. | Select. |
| C3: a new q=3 Baez-Duarte convolution criterion | It would be another known RH equivalence transported from q=1/q=2 and would not prove unconditional target membership. | Reject with `hard_gap_delta=0`. |
| C4: Hankel or Toeplitz operator built from the compiled Li matrix | Positivity of the complete operator would merely repackage the already compiled all-index Li criterion; boundedness and domain closure are additional missing edges. | Reject as a stronger wrapper around the same RH-hard frontier. |
| C5: a compressed self-adjoint scaling operator | The project has no proved spectrum-to-xi-zero correspondence, and compression need not preserve self-adjointness. | Reject before proof attempt. |
| C6: an unconditional explicit approximant with error tending to zero | On the exact Baez-Duarte carrier this directly proves RH; no new coefficient estimate survived the Burnol lower-bound audit. | Reject as secretly carrying the open endpoint. |

C2 is unconditional and strictly weaker than RH. It evaluates one rapidly decaying test transform
on the spectral zero side and reduces the W1c1 finite-height-to-global-height edge for that fixed
test. It does not prove the complete test-class explicit formula, Weil positivity, or RH.

## Fixed Lean Endpoint

The implementation module will be `LeanLab/Riemann/WeilGaussianHeight.lean`. Harmless naming and
equivalent normalization changes are allowed, but the final theorem must retain the following
mathematical content.

```lean
def riemannXiGaussianWeight (a : Real) (z : Complex) : Complex :=
  Complex.exp ((a : Complex) * (z - 1 / 2) ^ 2)

theorem summable_riemannXiGaussianWeight {a : Real} (ha : 0 < a) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))

theorem exists_gaussianXiAvoidingHeights_and_tendsto_verticalIntegral
    {a c : Real} (ha : 0 < a) (hc : 1 < c) :
    exists T : Nat -> Real,
      Tendsto T atTop atTop /\
      (forall n p,
        not (riemannXiZeroOnRectangleBoundary
          (1 - c) c (-T n) (T n) p)) /\
      Tendsto
        (fun n => integral y in (-T n)..(T n),
          riemannXiGaussianWeight a (c + y * Complex.I) *
            logDeriv riemannXi (c + y * Complex.I))
        atTop
        (nhds (Real.pi *
          tsum (fun p : RiemannXiDivisorZeroIndex =>
            riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))))
```

The endpoint may instead expose the selected-height theorem and the final convergence theorem as
two declarations, provided both compile and the latter consumes the former without an assumed
horizontal-decay premise. The factor `pi`, rectangle orientation, and reflection normalization
must be checked against the finite one-pole formula.

## Proof DAG

1. Prove `G_a` is entire, `G_a(1-s)=G_a(s)`, and compute its exact norm.
2. Use `0 < Re(rho) < 1` and squared-reciprocal zero summability to prove absolute summability of
   `G_a(rho)` with analytic multiplicity.
3. Derive `logDeriv xi (1-s) = -logDeriv xi s` from the xi functional equation.
4. For each large scale, bound the cardinality of near zeros by the reciprocal-square mass and
   select a height in a unit interval separated from all near zero ordinates.
5. Bound the near and far compensated Hadamard terms on both horizontal edges by a polynomial in
   the selected scale; include the degree-at-most-one polynomial derivative.
6. Prove both Gaussian-weighted horizontal integrals tend to zero.
7. Show the finite interior Gaussian zero sums tend to the absolute `tsum`, reflect the two
   vertical edges into twice the right edge, apply the finite-height theorem, and cancel `2*i`.

## Adversarial Checks And Stop Conditions

- `a = 0` must be rejected; the global zero weight is then not absolutely summable by this proof.
- The theorem must not require RH, zero simplicity, a zero enumeration, or the Riemann-von
  Mangoldt asymptotic.
- Merely choosing heights unequal to zero ordinates is insufficient; a quantitative separation or
  an independently justified averaged horizontal estimate is mandatory.
- Far-zero estimates must use the compensated genus-one term and the compiled reciprocal-square
  summability. An uncompensated reciprocal series is inadmissible.
- Multiplicity must remain represented by `RiemannXiDivisorZeroIndex`.
- The limit of finite zero cutoffs must be the proved absolute `tsum`, not an undefined ordering.
- Check the one-pole orientation: the symmetric vertical contribution is `2*i` times the right
  integral, hence the final factor is `pi`.
- Reject any project axiom, `sorry`, `admit`, `native_decide`, unsafe/opaque declaration, or
  resource-limit relaxation.
- If selected-height separation plus horizontal decay cannot be proved from existing standard
  theorems in two proof mechanisms, close this campaign as `NO_PROGRESS` and return to route
  selection. Do not shrink the endpoint to Gaussian algebra or summability alone.

## Fixed Accounting

- `research_activity`: active
- `rh_progress`: unchanged unless a later unconditional positivity edge is actually reduced
- `hard_gap_before`: W1c1 stops at the exact finite-height weighted xi zero cutoff
- `hard_gap_after`: if successful, one unconditional rapidly decaying test has a complete global
  zero-side contour limit; generic class-E limits and regularization remain
- `hard_gap_delta`: 1 fixed-test W1c1 height-limit subedge if successful, 0 for RH
- `assumption_frontier_before`: selected heights, horizontal decay, global zero cutoff,
  prime/archimedean integration, W1c2 regularization, W2 positivity
- `assumption_frontier_after`: prime/archimedean evaluation for the Gaussian test, generic class
  extension, W1c2 regularization, W2 positivity
- `normalized_tuple`: `(symmetric entire Gaussian xi weight, a>0 and c>1, selected zero-separated
  symmetric heights plus genus-one reciprocal-square control, right-vertical truncated integral
  tends to pi times the absolute multiplicity-bearing Gaussian zero tsum, generic test-class
  height limits and regularization)`

## Verification Gate

No declaration becomes a later premise until the fixed endpoint, exact TargetChecks, selected
transitive axiom prints, forbidden/declaration/resource scans, standalone and full builds,
`git diff --check`, and public CI all pass.

## Proof Attempt A Result

Loop 4 compiles the first three proof-DAG nodes in `WeilGaussianHeight.lean`:

- the weight is entire, reflection invariant, and has the exact norm
  `exp(a*((Re(s)-1/2)^2-Im(s)^2))`;
- the xi functional equation differentiates to
  `logDeriv xi (1-s) = -logDeriv xi s`;
- for every `a>0`, the multiplicity-bearing Gaussian zero family is absolutely summable.

The comparison proof uses only `0<Re(rho)<1`, the elementary bound `u*exp(-u)<=1`, and the compiled
reciprocal-square divisor summability. It introduces no RH, simplicity, zero count, or enumeration.
The fixed campaign endpoint remains open. Loop 5 must prove the global cutoff limit and then either
complete the quantitative selected-height/horizontal-decay mechanism or close under the stated
stop condition.

## Proof Attempt B Result

Loop 5 closes the fixed endpoint without shrinking it. Lean proves uniform selected-edge Gaussian
decay, the fourth-power-times-Gaussian majorant tends to zero, and therefore the selected top
horizontal integral tends to zero. Functional-equation reflection gives bottom equals negative
top and left equals negative right. The finite rectangle theorem then yields the exact identity

```text
Right_n = -i * Top_n + pi * ZeroCutoff_n.
```

Combining `Top_n -> 0` with the independently proved absolute zero-cutoff convergence produces
`exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral`, with the preregistered factor
`pi`, zero-free boundaries, selected heights tending to infinity, and analytic multiplicity.

## Independent Audit Result

Loop 6 rechecks the near/far split, the explicit separation denominator, the use of the compensated
genus-one term, the absolute `tsum`, and all four rectangle orientations. The new module compiles
without warnings; exact TargetChecks pass; five selected declarations use only `propext`,
`Classical.choice`, and `Quot.sound`; five forbidden scans and `git diff --check` are clean; and
the complete 8,669-job project build passes. Replayed warnings belong only to pre-existing modules.

The campaign is locally closed as `BRIDGE_REDUCED`, with `hard_gap_delta=1` for the fixed-test W1c1
subedge and `hard_gap_delta=0` for RH. Public implementation CI was the next mandatory gate.

Implementation commit `00410cc2a6919acfa5835b121c47489c5105e0de` passed public Lean Action CI
run `29436179027`, build job `87423295204`, in `2m23s`. The immutable evidence backfill and its own
public CI remain before final campaign closure.
