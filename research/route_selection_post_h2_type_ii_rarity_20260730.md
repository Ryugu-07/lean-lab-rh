# Route Selection after H2 Maynard--Pratt Type-II Rarity

Date: 2026-07-30

Status: `H7_CONNES_ACTUAL_GROUNDSTATE_WEIGHTED_COMPARISON_SELECTED`

## Closed local parent

Campaign `LITERATURE-20260730-H2-MAYNARD-PRATT-TYPE-II-RARITY-01` is locally parked at
`OBS-H2-SOURCE-MOBIUS-TWISTED-FOURTH-MOMENT-01`. Its final-ledger commit
`e9a1831952cc3983f9a1a272e961c05af270b26e` passed Lean Action run `30514927416`, build job
`90782516677`, in `1m43s`.

The H2 route is not falsified. Its exact fixed short-Mobius twisted fourth moment remains open.
Direct finite mean square, a square-root approximate functional equation, Watt's
length-times-maximum theorem, and the HRS fallback were audited before the local stop.

## Selection rule

Historical-route work is an omission search. The next campaign must attack a named
RH-relevant human-source inference with a mathematically discriminating failure mode. Ease,
family adjacency, and numerical constant optimization are not selection reasons.

Original conjectures, falsification, and direct RH attacks remain open at every stage.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H7 Connes finite-prime ground states | Prove that the true normalized Weil ground state approaches the explicit prolate packet strongly enough to transfer its Fourier transform on every closed substrip. | The source already proves the prolate-packet transform tends to `Xi`; the real-zero theorem applies to a simple isolated even true ground state. The project has now identified the exact weighted topology and the Rayleigh-gap consumer on the two sides of the missing comparison. The source still says only "sufficiently good" and gives numerical evidence. | **Select.** |
| H12 Levinson--Montgomery / Speiser | Complete the global indented argument-principle count, strict base orientation, and top variation. | Several local boundary and count interfaces compile, but the surviving edge is a broad global contour package rather than a newly weakened premise. | Retain open. |
| H10 function fields | Construct actual curve intersections, Hodge index, and Frobenius point-count identities, then test a number-field transfer. | The successful finite numerical hinge compiles, but the geometric producer and characteristic-zero transfer remain absent. This is required historical coverage, but no smaller overlooked inference is currently exposed. | Retain open. |
| H11 zero statistics | Amplify one finite or density-zero off-line orbit into nonvanishing pair or moving-window mass. | Compiled sparse-exception models show density-one and pair-statistical error terms can absorb such an orbit. No source-backed amplifier is presently available. | Retain open and conjecture-capable. |
| H1 Selberg / Levinson--Conrey | Prove the actual long mollified moment and multiplicity-aware auxiliary count. | This remains a major historical route, but its next producer is a broad off-diagonal mean-value theorem already recorded exactly. | Retain open. |
| H2 Type I / Type II | Prove the actual Type-I large-value estimate or the parked fixed Type-II twisted fourth moment. | Both are exact and valuable, but immediate continuation would be family adjacency after a deep H2 campaign. No new smaller producer appeared in the final audit. | Retain open. |
| H8 de Branges / entire geometry | Construct the concrete actual-xi Hardy space and prove source-valid shift positivity. | Abstract consumers and a phase obstruction compile; the actual positivity producer is still global. | Retain open. |

## Primary-source lock

The fixed sources are:

- Alain Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*,
  Sections 6.1--6.6 and Fact 6.4:
  <https://arxiv.org/abs/2602.04022>.
- Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Spectral Triples*,
  Theorem 5.10 and Section 7:
  <https://arxiv.org/abs/2511.22755>.
- Alain Connes and Walter van Suijlekom,
  *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*:
  <https://arxiv.org/abs/2511.23257>.

For `lambda>1`, the source true minimizer and explicit prolate packet are supported in
`[lambda^(-1),lambda]`. In centered logarithmic coordinates their support is

```text
[-log lambda, log lambda].
```

The source proves that the Fourier transforms of the explicit packets `k_lambda` converge to
`Xi` uniformly on closed substrips of `abs(Im z)<1/2`. It leaves two independent steps open:

1. simple-even structure for the true lowest Weil eigenfunction;
2. a sufficiently accurate comparison of that eigenfunction with `k_lambda`.

The previous H7 topology campaign proves that the second step is discharged if, for every
fixed `0<=A<1/2`,

```text
integral_R exp(A*abs(x))*abs(theta_lambda(x)-k_lambda(x)) dx -> 0.
```

## Quantitative omission probe

On the source support, Cauchy--Schwarz gives, for `A>0`,

```text
weighted_L1_error(A)
  <= sqrt((exp(2*A*log(lambda))-1)/A) * L2_error
  <= lambda^A / sqrt(A) * L2_error.
```

The existing Rayleigh-gap consumer bounds squared projective error by

```text
RayleighExcess(k_lambda) / spectralGap(lambda).
```

After coherent normalization and orientation, a sufficient source-rate target is therefore

```text
lambda^(2*A) *
  RayleighExcess(k_lambda) / spectralGap(lambda) -> 0
```

for every fixed `0<A<1/2`, together with the corresponding `A=0` logarithmic endpoint.
Merely proving the ratio tends to zero is insufficient because the support escapes.

This rate is not asserted by the source. It is the selected proof and falsification target.
The source packet-to-`Xi` theorem is also not yet compiled in this repository; it must be
reconstructed in Lean before any final transform composition may be registered.

## Fixed next campaign

- `campaign`: `PROOF-ATTEMPT-20260730-H7-CONNES-WEIGHTED-GROUNDSTATE-COMPARISON-01`.
- `node`: `H7-CONNES-ACTUAL-GROUNDSTATE-COMPARISON-01`.
- `mode`: `LITERATURE / PROOF-ATTEMPT / FALSIFICATION`.
- `full_endpoint`: for the literal source-normalized true ground states and prolate packets,
  prove the exponentially weighted comparison for every `A<1/2`. Compose it with the public
  Fourier-topology theorem only after the source prolate-to-`Xi` limit has itself been
  reconstructed in Lean.
- `first_attack`: prove the exact support-sensitive `L2`-to-weighted-`L1` rate theorem, connect
  coherent ground-line orientation to function error, then instantiate and attack the literal
  source Rayleigh-excess/gap rate.
- `negative_controls`: unweighted `L1` or `L2`; absolute Rayleigh excess; an unscaled
  excess/gap ratio; numerical agreement; or a theorem assuming the source rate.
- `independent_open_edge`: simple-even ground-state structure remains separately necessary
  before the real-zero theorem can be applied.
- `strict_boundary`: a conditional rate reduction is not the actual comparison; the actual
  comparison alone is not H7 or RH without simple-even structure and the final Hurwitz
  transfer.
- `production_gate`: no `LeanLab/` proof or registration edit before docs-only
  preregistration passes public CI.

The persistent RH Goal remains active.
