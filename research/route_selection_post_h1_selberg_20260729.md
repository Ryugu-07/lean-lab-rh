# Route Selection after H1 Selberg Local Sign Change

Date: 2026-07-29

Status: `RERANK_COMPLETE / H2_CLASSICAL_ZERO_DETECTOR_SELECTED`

## Closed parent

Campaign `LITERATURE-20260729-H1-SELBERG-LOCAL-SIGN-CHANGE-01` is publicly closed at
`FULL_LOCAL_SIGN_CHANGE_PRODUCER_SUCCESS`. Its complete public chain is:

- preregistration `18113427dae282e19a8d257360c6ffe318ada9a5`, run `30389770527`, job
  `90378107379`, `1m51s`;
- frozen implementation `8d9373fa6325a857541fb112b3ec137162a343c9`, run `30390650837`, job
  `90381074143`, `3m7s`;
- immutable evidence `5a80c9736d95294a3baf8bc666f8b45c85e5342f`, run `30390974932`, job
  `90382176746`, `1m48s`;
- final ledger `2be8491d89ba02acc01cb133f596bd46580303be`, run `30391193466`, job
  `90382907452`, `1m43s`.

The closed result is a local deterministic producer. Selberg's global moments, critical-zero
proportions, H1, and RH remain open. Fresh full-atlas selection is therefore required.

## Coverage correction

The H2 row is `SOURCE_ALIGNED`, but its theorem-producing coverage is asymmetric. The repository
contains the finite-line half-isolation theorem and a reflection-symmetric bow countermodel. It
does not reconstruct the classical analytic zero detector used before any Ingham, Huxley,
Maynard--Pratt, or Guth--Maynard large-value estimate.

The common detector begins with a truncated Mobius polynomial. Multiplication by zeta creates
coefficients

```text
a_M(n) = sum_{d | n, d <= M} mu(d),
```

with `a_M(1)=1` and `a_M(n)=0` for `2 <= n <= M`. A Gamma--Mellin representation of the
exponentially smoothed series is shifted through an actual zeta zero. The resulting identity
forces either a large dyadic Dirichlet-polynomial block or a large critical-line integral
remainder. Only after this step do mean-value and large-value estimates count the zeros.

Thus the existing H2 campaign formalizes the geometric obstruction after detection, while the
classical source route into detection is absent.

## Cross-family comparison

| family or subroute | first live edge | omission reading | decision |
| --- | --- | --- | --- |
| H2 classical zero detection | Reconstruct the truncated-Mobius coefficient gap, smoothed Mellin identity, and contour shift at an actual zeta zero. | No production module reaches the Type-I/Type-II detector used by classical and current zero-density proofs. Existing Mellin, Gamma, zeta-convexity, and Mobius infrastructure can test the exact source logic. | **Select.** |
| H7 spectral/trace | Construct an infinite arithmetic operator and prove controlled spectral convergence. | Finite Weil ground-state, Herglotz, and Rayleigh interfaces already have several campaigns; the infinite producer remains broad. | Retain open. |
| H10 function-field transfer | Build actual curve intersection theory or a number-field cohomological object. | Finite auxiliary, Hodge-lattice, and spectral rigidity mechanisms compile; the transfer object remains unavailable. | Retain open. |
| H11 statistics | Amplify one sparse actual off-line orbit beyond normalized pair-correlation errors. | Finite multiplicity and moving-window interfaces compile, but no source-backed amplifier is known. | Retain open. |
| H12 Speiser | Complete the global indented argument principle and top-edge variation. | Valuable and partially prepared, but several recent H12 campaigns already isolate the remaining contour package. | Retain open. |
| H1 global moments | Produce many Selberg strict-gap intervals. | This is the adjacent successor of the just-closed campaign and would be immediate route continuation. | Retain open; do not select by inertia. |

## Primary-source lock

The exact reconstruction source is James Maynard and Kyle Pratt,
[*Half-isolated zeros and zero-density estimates*](https://arxiv.org/abs/2206.11729),
Appendix C, proof of Lemma 23. It explicitly writes the truncated Mobius coefficients, the
smoothed Dirichlet series, the original vertical Mellin integral, the shift to
`Re(w)=1/2-Re(rho)`, and the dyadic-block versus integral-remainder dichotomy.

Larry Guth and James Maynard,
[*New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552),
Section 13.1, uses the same classical detector before applying its new large-value theorem. Its
historical anchors are A. E. Ingham, *On the estimation of N(sigma,T)* (1940), and M. N. Huxley,
*On the difference between consecutive primes* (1972).

This campaign reconstructs the common detector mechanism. It does not optimize a density
exponent or treat a better exponent as progress toward excluding one exceptional zero.

## Fixed next campaign

- `campaign`: `LITERATURE-20260729-H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01`.
- `node`: `H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01`.
- `mode`: `LITERATURE / OMISSION_AUDIT / PROOF-ATTEMPT`.
- `full_endpoint`: compile the actual truncated-Mobius arithmetic function and coefficient gap;
  prove its absolutely convergent zeta-product L-series identity; construct the exponential
  smoothing and original Gamma--Mellin line identity; shift at an actual off-critical-line
  nontrivial zeta zero with the Gamma pole at zero canceled and the zeta pole residue retained;
  derive a cardinality-audited dyadic-block or critical-line-remainder detector.
- `meaningful_partial`: compile the coefficient gap, actual zeta-product L-series identity,
  smoothed summability, and exact finite detector algebra, while stating the first unavailable
  Mellin inversion or contour-shift theorem exactly.
- `strict_boundary`: no Type-I or Type-II zero count, no fourth-moment estimate, no Guth--Maynard
  large-value theorem, no density exponent, no actual bow exclusion, no H2, and no RH.
- `production_gate`: no `LeanLab/` edit before the docs-only preregistration passes public CI.

The persistent RH Goal remains active.

## Selection outcome

The selected campaign reaches `MEANINGFUL_MELLIN_PARTIAL`. Lean compiles the exact arithmetic
coefficient gap, actual right-half-plane zeta-product, exponential head-tail split, full forward
Mellin transform, removable Gamma-pole cancellation at an actual zeta zero, retained
translated-zeta residue, and cardinality-audited finite detector.

The first unavailable theorem is `ClassicalDetectorInverseMellinLine`. Consequently the global
contour shift, shifted Type-I/Type-II detector identity, density estimates, H2, and RH remain
open. After the evidence chain, selection returns to the historical atlas instead of optimizing
a density constant or continuing H2 by inertia.
