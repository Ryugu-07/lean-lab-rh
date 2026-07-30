# H7 Connes Weighted Ground-State Comparison Preregistration

Date: 2026-07-30

Campaign:
`PROOF-ATTEMPT-20260730-H7-CONNES-WEIGHTED-GROUNDSTATE-COMPARISON-01`

Node: `H7-CONNES-ACTUAL-GROUNDSTATE-COMPARISON-01`

Mode: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`

Status: `PREREGISTERED / PUBLIC_CI_PENDING`

## Exact mathematical target

Let `lambda_n -> infinity`. Let `theta_n` be the coherently normalized centered logarithmic
form of the true lowest eigenfunction of the source Weil operator on
`[lambda_n^(-1),lambda_n]`, and let `k_n` be the correspondingly normalized explicit prolate
packet. Both are extended by zero outside
`[-log(lambda_n),log(lambda_n)]`.

Prove, for every real `A` with `0<=A<1/2`,

```text
integral_R exp(A*abs(x))*abs(theta_n(x)-k_n(x)) dx -> 0.
```

Compose this result with:

1. a Lean reconstruction of Connes' source theorem that `Fourier(k_n)` converges to `Xi`
   uniformly on every closed substrip of `abs(Im z)<1/2`; and
2. the compiled theorem `weilGroundStateCenteredFourier_uniform_transfer`.

The full campaign endpoint is the literal source comparison, not an abstract conditional
transfer. The packet-to-`Xi` theorem is known in the source but unavailable as a project
premise until it compiles and passes the normal audit.

## Proposed Lean statements

Equivalent names and a source-faithful parameterization are allowed.

```lean
def ConnesGroundStateWeightedComparison
    (lambda : Nat -> Real) (theta k : Nat -> Real -> Complex) : Prop :=
  ∀ A : Real, 0 <= A -> A < 1 / 2 ->
    Filter.Tendsto
      (fun n =>
        weilGroundStateFourierStripError A (theta n) (k n))
      Filter.atTop (nhds 0)
```

The quantitative producer should have the shape:

```lean
def ConnesGroundStateRayleighGapRate
    (lambda ratio : Nat -> Real) : Prop :=
  ∀ A : Real, 0 < A -> A < 1 / 2 ->
    Filter.Tendsto
      (fun n => Real.rpow (lambda n) (2 * A) * ratio n)
      Filter.atTop (nhds 0)
```

Since real powers may lead to an equivalent `rpow` formulation, the final Lean statement may
replace the display by `Real.rpow`. The `A=0` endpoint must retain the support-length factor
`sqrt(2*log(lambda_n))`.

The source instantiation must identify

```text
ratio_n =
  RayleighExcess(sourceWeilMatrix_n, sourceGroundValue_n, sourceProlate_n)
    / sourceGroundGap_n.
```

It may not introduce this rate as a hypothesis and then register the conditional consumer as
the full target.

## Hard-gap position

```text
literal finite-prime Weil form and prolate packet
  -> actual Rayleigh excess and certified ground gap
  -> lambda^(2*A) * excess/gap -> 0 for every A<1/2
  -> weighted ground-state comparison
  -> compact-uniform true-ground transform -> Xi
  + simple isolated even ground state
  -> all limiting zeros real by Hurwitz
  -> RH
```

This campaign attacks the third and fourth arrows. The simple-even branch is independent and
remains open.

## Source alignment

Primary sources:

- Connes, arXiv:2602.04022, Sections 6.1--6.6 and Fact 6.4:
  <https://arxiv.org/abs/2602.04022>.
- Connes--Consani--Moscovici, arXiv:2511.22755, Theorem 5.10 and Section 7:
  <https://arxiv.org/abs/2511.22755>.
- Connes--van Suijlekom, arXiv:2511.23257:
  <https://arxiv.org/abs/2511.23257>.

The source support has multiplicative radius `lambda`, hence centered additive radius
`log(lambda)`. The source packet-transform estimate on a horizontal line
`Im z=alpha` decays like

```text
lambda^(-1/2-alpha)/(1-2*alpha),
```

while the true-ground comparison is left as "sufficiently good" and supported numerically.
No source theorem is read as proving the selected rate.

## Nearest prior attempts

1. `LITERATURE-20260730-H7-CONNES-FOURIER-TOPOLOGY-01` proves that exponentially weighted
   `L1` error suffices and falsifies support-blind unweighted `L1` and `L2` promotion.
2. `DISCOVERY-20260723-H7-PROLATE-RAYLEIGH-GAP-01` proves
   `projectiveDefect <= RayleighExcess/gap` and falsifies absolute-excess promotion under a
   collapsing gap.
3. `LITERATURE-20260722-H7-WEIL-HERGLOTZ-CRITERION-01` isolates a finite simple-even scalar
   criterion but does not prove its arithmetic inequality.
4. The actual pole, finite-prime, archimedean-density, and finite-dictionary blocks compile,
   but no current declaration assembles the literal prolate coefficients and both source
   limits.

## Materially new attack angle

The previous topology campaign answered which function-space convergence would be sufficient.
This campaign attacks the source quantitative producer. It combines the escaping support
`log(lambda)` with the Rayleigh-gap estimate and tests the exact scaled ratio
`lambda^(2*A)*excess/gap`, rather than the previously rejected unweighted or absolute-error
conditions.

## Success criteria

Full success requires all of the following:

1. define the source-normalized support, true ground state, prolate packet, Rayleigh excess,
   and ground gap without replacing them by arbitrary sequences;
2. prove the exact support-sensitive weighted Cauchy--Schwarz estimate, including `A=0`;
3. prove coherent phase/sign orientation converts projective control into actual function
   error;
4. prove the literal source scaled excess/gap rate for every `A<1/2`;
5. derive `ConnesGroundStateWeightedComparison`;
6. separately reconstruct the source `k_lambda -> Xi` theorem in Lean before using it;
7. compose the two compiled limits through the public Fourier-topology theorem;
8. add exact TargetChecks, selected axiom prints, forbidden scans, and full build evidence.

No success is recorded if criterion 4 remains a premise.

## Falsification criteria

The target is falsified or materially obstructed if one of these is kernel-checked or proved
from the source formulas:

1. the normalized source ratio fails the required `lambda^(-2*A)` scale for some
   `A<1/2`;
2. coherent orientation cannot be maintained because the source normalization vanishes or
   changes sign;
3. a literal source finite matrix/prolate instance violates the proposed quantitative
   inequality;
4. the source support or Fourier normalization differs materially from the registered
   `[-log(lambda),log(lambda)]` model;
5. the source only controls a quantity that the compiled escaping-packet counterexample shows
   insufficient.

Numerical disagreement may select a falsification target but is not itself a Lean premise.

## Known obstacles

- The project does not yet define the complete literal source matrix together with prolate
  coefficient vectors and both `N -> infinity` and `lambda -> infinity` limits.
- The source gives numerical, not proved, ground/prolate comparison.
- The ground gap may collapse, so small absolute Rayleigh excess is irrelevant.
- Projective control loses phase/sign; coherent orientation is mandatory.
- The support weight costs approximately `lambda^A`, so ratio convergence without rate is
  insufficient.
- Simple-even ground-state structure is a separate unresolved branch.

## Assumption frontier

Allowed downstream premises are only already compiled public-green theorems, standard
Lean/mathlib facts, and source statements reconstructed and proved in this campaign.

Forbidden as hidden premises:

- the actual weighted comparison;
- the scaled source Rayleigh-gap rate;
- simple-even structure;
- compact-uniform convergence of the true ground-state transform;
- the uncompiled source packet-to-`Xi` theorem;
- RH or Weil positivity.

## Claim boundary

A support-sensitive conditional reduction is route infrastructure. It is not the actual source
comparison. Even the actual source comparison would not prove RH without simple-even structure,
the source real-zero theorem, and the final Hurwitz transfer.

The persistent RH Goal remains active.
