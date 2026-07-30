# H7 Connes Weighted Ground-State Comparison Result

Date: 2026-07-30

Campaign:
`PROOF-ATTEMPT-20260730-H7-CONNES-WEIGHTED-GROUNDSTATE-COMPARISON-01`

Node: `H7-CONNES-ACTUAL-GROUNDSTATE-COMPARISON-01`

Classification:
`MEANINGFUL_PARTIAL / EXACT_CONSUMER_AND_OBSTRUCTION / ACTUAL_SOURCE_RATE_OPEN`

## Compiled result

The no-sorry module
`LeanLab/Riemann/ConnesGroundStateWeightedComparison.lean` proves the exact common-support
estimate

```text
StripError(A,f,g)
  <= sqrt((exp(2*A*R)-1)/A) * sqrt(L2Error(f,g))
```

for `A>0` and support in `[-R,R]`.  At `A=0`, Lean proves the separate endpoint

```text
StripError(0,f,g) <= sqrt(2*R) * sqrt(L2Error(f,g)).
```

For continuous compactly supported normalized functions with coherently oriented real inner
product, Lean also proves

```text
L2Error(f,g) <= 2 * ProjectiveDefect(f,g).
```

Consequently, on source support `R=log(lambda)`, if `ratio` bounds projective defect and

```text
lambda_n^(2*A) * ratio_n -> 0
```

for every `0<A<1/2`, then the exponentially weighted comparison holds for every
`0<=A<1/2`.  The `A=0` endpoint follows from any positive-power rate using
`log(lambda)<=lambda^epsilon/epsilon`; it is not an extra premise.

The theorem
`connesGroundStateFourier_uniform_transfer_of_rayleighGapRate` composes this comparison with an
independently proved packet-transform limit.  The packet-to-`Xi` source theorem remains an
explicit premise until separately reconstructed in Lean.

## Negative control

Lean constructs the expanding scale and collapsing gap

```text
lambda_n = exp(n),
gap_n = exp(-n).
```

In the existing two-dimensional symmetric ground-state family, the test-vector absolute
Rayleigh excess is also `exp(-n)`.  Lean proves

```text
lambda_n^(2*A) * absoluteExcess_n -> 0   for every A<1/2,
absoluteExcess_n / gap_n = 1,
projectiveDefect_n = 1.
```

Thus an extremely small packet Rayleigh value, even at every support-weighted absolute rate
needed by the Fourier topology, cannot replace a bound on excess divided by the actual gap.

## Source audit

Connes 2026 gives the explicit packet `k_lambda`, states its transform convergence to `Xi`, and
leaves the comparison with the true minimizer `theta_x` as a remaining step.

Connes--Consani 2023 gives the underlying numerical comparison.  Its source TeX:

- reports roughly `lambda^2` simultaneous minuscule even Weil eigenvalues;
- defines prolate candidate vectors by approximate Fourier symmetry and Gram--Schmidt;
- displays numerical graph agreement with the low Weil eigenvectors;
- gives no theorem bounding the actual packet Rayleigh excess, the first Weil spectral gap, or
  their ratio.

The multiplicity of the minuscule cluster makes the missing gap estimate substantive.  Small
absolute excess alone is formally insufficient.

## Local stop

The preregistered full success criterion is not met because the actual source
Rayleigh-excess-to-gap rate remains unproved.  The current attack is locally stopped at the
exact producer

```text
lambda^(2*A) *
  RayleighExcess(actualWeilOperator, actualProlatePacket) /
  actualGroundGap
  -> 0.
```

A materially different H7 reentry may either prove this ratio directly or bypass the tiny
internal Weil gap by proving approximate commutation with a prolate label operator whose
spectrum separates the desired packet.  This second possibility is a proposed attack angle,
not a proved source fact.

## Local verification

- production module, Targets, TargetChecks, AxiomsAudit, and root import compile;
- five exact campaign TargetChecks compile;
- eleven selected transitive axiom prints use only `propext`, `Classical.choice`, and
  `Quot.sound`;
- three forbidden declaration/proof/resource scans are empty;
- `git diff --check` is empty;
- full repository build passes `8811/8811`; its warnings are inherited from older modules.
- implementation commit `f55c334050cf135997308a287701ed5239978a86` passed Lean Action run
  `30517091377`, build job `90789265240`, in `2m14s`.

No actual ground/prolate comparison, packet-to-`Xi` Lean theorem, simple-even ground-state
theorem, H7, or RH is proved.  The global RH Goal remains active.
