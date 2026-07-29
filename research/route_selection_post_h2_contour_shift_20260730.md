# Route Selection after H2 Classical Detector Contour Shift

Date: 2026-07-30

Status: `H7_CONNES_FOURIER_TOPOLOGY_SELECTED / PREREGISTRATION_LOCAL`

## Closed parent

Campaign `LITERATURE-20260730-H2-CLASSICAL-DETECTOR-CONTOUR-SHIFT-01` is publicly closed at
receipt commit `a141b4acd1a606c815e7f179a703e882a27fd8bb`, Lean Action run
`30485670826`, build job `90690587648`, passed in `1m56s`.

The closed node proves the actual Maynard--Pratt Appendix C infinite contour shift, including
both horizontal limits, both vertical integrability statements, the exact retained residue, the
shifted smoothed series, and the coefficient-gap identity. The quantitative dyadic
Type-I/Type-II detector is the first H2 successor.

## Selection rule

Historical work remains an omission search. Adjacency to a closed node gives no route automatic
priority. A new campaign should identify a decisive human inference whose required topology,
premise, singularity, or limit order can be tested exactly.

Original conjectures, falsification, and direct RH attacks remain open at every selection.
Numerical optimization is not selected unless it crosses a logical threshold.

## Fresh cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H7 Connes finite-prime Weil ground states | Turn approximation of the true smallest-eigenvalue vector by the prolate packet into compact-uniform convergence of its Fourier transform to `Xi`. | Connes proves the prolate packet transform converges to `Xi` on closed substrips, but Section 6.6 says only that the packet must be a "sufficiently good" approximation to the true minimizer. The project has a Rayleigh-gap `L2` consumer but no theorem identifying the transform topology. Expanding support makes this a genuine rate issue. | **Select.** |
| H2 classical detector | Prove the source dyadic Type-I/Type-II block and tail estimates after the compiled coefficient gap. | This is a known quantitative density producer, but by itself it still permits sparse off-line exceptions. Retain as the first H2 successor without selecting it by adjacency. | Retain open. |
| H1 Hardy--Littlewood / Selberg | Prove the actual uniform eta remainder or Selberg's global sign-producing moments. | Both are genuine historical producers, but each is currently a broad oscillatory or global mean-value theorem. | Retain open. |
| H8 de Branges / Conrey--Li | Construct the concrete half-strip Hardy RKHS and then prove actual-xi shift positivity. | The abstract producer and consumer compile; the first concrete space is useful infrastructure but does not yet test the actual positivity premise. | Retain open. |
| H10 function fields | Construct a regularized number-field trace with prime, archimedean, and uniform-tail terms. | Finite spectral, Hodge, Stepanov, and polar-injectivity mechanisms compile; the missing number-field object remains broad. | Retain open. |
| H11 zero statistics | Amplify one sparse off-line orbit into an absolute statistical defect. | Existing countermodels show density-scale convergence cannot do this; no source-backed amplifier is available. | Retain open. |

## Primary-source reconstruction

Primary sources:

- Alain Connes, *The Riemann Hypothesis: Past, Present and a Letter Through Time*,
  Sections 6.4--6.6: <https://arxiv.org/abs/2602.04022>.
- Alain Connes and Walter D. van Suijlekom,
  *Quadratic Forms, Real Zeros and Echoes of the Spectral Action*:
  <https://arxiv.org/abs/2511.23257>.

Connes's Fact 6.4 states that the Fourier transforms of the explicit prolate packets
`k_lambda` converge to the Riemann `Xi` function uniformly on closed substrips of
`abs(Im z)<1/2`, with a quantitative boundary-sensitive rate. Section 6.6 retains two missing
steps:

1. prove the smallest Weil eigenvalue is simple with an even eigenvector `theta_x`;
2. prove `k_lambda` is a sufficiently good approximation of `theta_x`.

The 2025 theorem supplies the real-zero conclusion once the true ground state is simple,
isolated, and even. The project's earlier Rayleigh-gap theorem turns a small excess-to-gap ratio
into an unweighted finite-dimensional projective defect. It does not prove that this defect is
strong enough for compact-uniform convergence of Fourier transforms when support grows.

## Fixed next campaign

- `campaign`: `LITERATURE-20260730-H7-CONNES-FOURIER-TOPOLOGY-01`.
- `node`: `H7-CONNES-GROUNDSTATE-FOURIER-TOPOLOGY-01`.
- `mode`: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`.
- `fixed_endpoint`: define the exponential-strip error for centered source functions; prove it
  uniformly bounds Fourier-transform error on every fixed closed substrip; prove a sequence
  transfer theorem that combines prolate-to-`Xi` convergence with true-ground-state-to-prolate
  weighted convergence; and construct a smooth compactly supported escaping packet whose
  unweighted mass tends to zero while its transform stays nonzero at one point strictly inside
  the source strip.
- `negative_control`: unweighted `L1`, unweighted `L2`, finite-dimensional Rayleigh excess, or
  projective convergence alone may not be promoted to compact-uniform strip convergence.
- `strict_boundary`: no actual source `theta_x`, no proof of simple-even ground states, no
  prolate comparison estimate, no all-real-zero limit theorem, H7, or RH.
- `production_gate`: no `LeanLab/` proof or registration edit before this docs-only
  preregistration passes public CI.

The persistent RH Goal remains active.
