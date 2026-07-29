# H7 Connes Ground-State Fourier Topology Immutable Evidence

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H7-CONNES-FOURIER-TOPOLOGY-01`

Classification: `FULL_SUCCESS / FOURIER_TOPOLOGY_IDENTIFIED`

## Frozen implementation

- commit: `2be884b27f505542f11ca380d8ac384b0e4bdfd2`;
- Lean Action run: `30487452115`;
- build job: `90696590632`;
- result: passed in `2m32s`;
- local full build before publication: `8803/8803`.

The frozen files are:

```text
LeanLab.lean
LeanLab/Riemann/WeilGroundStateFourierTopology.lean
LeanLab/Riemann/Targets.lean
LeanLab/Riemann/TargetChecks.lean
LeanLab/Riemann/AxiomsAudit.lean
```

Their diff from the implementation commit is empty at evidence publication.

## Certified endpoint

`weilGroundStateFourierTopology_endpoint` packages:

- the exact complex-exponential norm and closed-strip majorant;
- the actual integral Fourier-difference bound;
- one sequence bound simultaneous over the whole closed strip;
- the two-stage target-convergence transfer;
- the exact centered ground-state source-coordinate specialization;
- smoothness and compact support of the escaping packets;
- a fixed transform value equal to one at `-i/4`;
- unweighted `L1` and squared `L2` masses tending to zero;
- failure of uniform convergence to zero on the closed quarter-strip.

Nine exact TargetChecks compile. Nine selected axiom prints use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Historical finding and boundary

An `exp(A*abs(x))`-weighted `L1` comparison is sufficient to transfer prolate-transform
convergence on `abs(Im z)<=A`. Ordinary unweighted `L1`, unweighted `L2`, or a support-blind
projective comparison is insufficient when support escapes.

This evidence does not certify an actual `theta_x-k_lambda` estimate, simple-even source ground
states, an all-real-zero limit theorem, H7, or RH.
