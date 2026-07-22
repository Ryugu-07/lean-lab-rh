# Route Selection after H14

Date: 2026-07-23

Status: `H7_PROLATE_RAYLEIGH_GAP_SELECTED / PREREGISTRATION_CI_REQUIRED`

## Closed parent campaign

Campaign `FALSIFICATION-20260723-H14-FINITE-HEIGHT-PROMOTION-01` is publicly closed at
final-ledger commit `cd67e4ad4f899631b11b8d6a8927c5709e4f9fa3`, public Lean Action run
`29963802981`, build job `89070709361`, in `1m57s`. The generic promotion obstruction is closed;
actual-zeta global-tail reduction, H14 as a support tool, and RH remain open.

## Selection interpretation

The H0-H14 campaign census is now a coverage baseline, not a declaration that the historical
literature or every mechanism inside each family has been exhausted. Route selection continues to
look for omitted human proof mechanisms and unfinished edges. Original conjectures may enter at
any time when they have a precise statement, a falsification plan, and a named consumer in the RH
dependency graph.

## Cross-route comparison

| candidate | current frontier | discriminating next probe | verdict |
| --- | --- | --- | --- |
| H7 finite-prime Weil/prolate | Human sources prove the real-zero mechanism under a simple isolated even ground state and prove the explicit prolate transform limit to Riemann `Xi`; the actual ground-state/prolate comparison is open. | Replace the phrase "sufficiently good approximation" by a quantitative Rayleigh-excess/spectral-gap ratio and test whether that ratio is the exact missing variational object. | `SELECTED` |
| H1 mollifier/proportion | The source variational optimization is compiled, but long mean values and the sparse-exception barrier remain. | Find a source-valid statistic that gives nonvanishing weight to one exceptional orbit. | `OPEN`, but no such statistic is currently named. |
| H2 density/half-isolated bows | The symmetry-only shortcut is falsified; actual-zeta bow exclusion remains open. | Prove an arithmetic amplification or localizer for a single bow. | `OPEN`, low present formalization leverage. |
| H11 zero statistics | Density-one horizontal information and the persistent-exception model are compiled. | Find an absolute-error statistic changed by one inserted off-line orbit. | `OPEN`, currently no primary-source candidate. |
| Direct Weil/Li/closure attacks | Exact RH equivalents and several conditional consumers compile. | Prove unconditional global positivity or closure without reintroducing RH as a premise. | Always eligible; no higher-value new concrete input found in this selection. |

This selection does not optimize a numerical zero height, mollifier percentage, or H7 finite
constant. It targets the convergence mechanism identified as missing in the primary sources.

## Locked primary-source frontier

1. Connes--van Suijlekom, arXiv:2511.23257, proves that a lower-bounded form with a simple
   isolated even ground state has a ground-state Fourier transform with only real zeros.
   <https://arxiv.org/abs/2511.23257>
2. Connes--Consani--Moscovici, arXiv:2511.22755, Section 8, states two missing steps: simple-even
   structure and sufficiently accurate approximation of the true lowest eigenfunction by the
   explicit prolate candidate. The paper supplies numerical evidence, not a convergence theorem.
   <https://arxiv.org/abs/2511.22755>
3. Connes, arXiv:2602.04022, Fact 6.4 and Section 6.6, proves the explicit prolate Fourier
   transform converges to Riemann `Xi` on closed substrips and again leaves its comparison with the
   true lowest eigenfunction open.
   <https://arxiv.org/abs/2602.04022>

None of these sources states a quasimode-residual or Rayleigh-gap theorem for the Weil ground
state. The candidate below is a model-original decomposition of their open comparison.

## Original candidate

For an exact finite source matrix `A_(lambda,N)`, let `mu_(lambda,N)` be its lowest eigenvalue,
`xi_(lambda,N)` a normalized ground vector, `delta_(lambda,N) > 0` a certified gap on the
orthogonal complement of the ground line, and `kappa_(lambda,N)` the normalized coefficient
vector of the explicit prolate approximation. Define the Rayleigh excess

```text
E_(lambda,N) = <kappa, A*kappa> - mu_(lambda,N).
```

The candidate bridge is that, in the source-prescribed Galerkin limit followed by the increasing
prime-cutoff limit,

```text
E_(lambda,N) / delta_(lambda,N) -> 0.
```

The quantitative variational consumer should prove

```text
1 - <xi,kappa>^2 <= E / delta
```

for normalized real vectors. Thus the ratio controls projective distance to the ground line.
Phase/sign normalization, Galerkin-to-form convergence, transform continuity, and identification
of the actual source matrix remain separate required edges.

## Strength and falsification audit

- The generic inequality is finite-dimensional linear algebra and is weaker than RH.
- The concrete source ratio limit is not known and is not admitted as a premise.
- Combined with source-object alignment, simple-even structure, the true Galerkin/continuum
  limits, and the proved prolate-transform limit, the concrete ratio would feed the RH-bearing
  ground-state convergence chain.
- Small absolute Rayleigh excess alone is insufficient. For the diagonal matrix
  `diag(0, epsilon)` with ground vector `e0` and test vector `e1`, the excess tends to zero as
  `epsilon -> 0` while projective defect stays one; the gap collapses at exactly the same rate.
- A source numerical screen may reject the candidate if the normalized ratio fails to decrease.
  Numerical output is navigation evidence only and cannot become a Lean premise.

## Material difference from prior H7 work

The alignment campaign fixed coordinate and domain mismatches. The finite-matrix campaign built
parity and qualitative Rayleigh certificates. The Herglotz campaign reduced odd-sector positivity
to an arithmetic scalar inequality. This campaign does not continue that scalar inequality and
does not optimize finite cutoffs. It introduces a quantitative convergence consumer for the
distinct true-ground-state/prolate edge and a falsification model for gap collapse.

## Decision

Preregister campaign `DISCOVERY-20260723-H7-PROLATE-RAYLEIGH-GAP-01`. Public preregistration CI
must pass before any new Lean proof-source edit. The campaign may admit the concrete source ratio
only as a conjecture; it must never use it as a premise.
