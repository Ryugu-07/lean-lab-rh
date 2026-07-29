# H7 Connes Ground-State Fourier Topology Result

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H7-CONNES-FOURIER-TOPOLOGY-01`

Node: `H7-CONNES-GROUNDSTATE-FOURIER-TOPOLOGY-01`

Classification: `FULL_SUCCESS / FOURIER_TOPOLOGY_IDENTIFIED / LOCAL_AUDIT_GREEN`

## Result

The 527-line no-sorry module
`LeanLab/Riemann/WeilGroundStateFourierTopology.lean` proves the fixed endpoint as
`weilGroundStateFourierTopology_endpoint`.

For every `A>=0` and every `z` with `abs(Im z)<=A`, Lean proves

```text
norm(exp(i*z*x)) = exp(-Im(z)*x) <= exp(A*abs(x)).
```

For continuous compactly supported source functions `f,g`, this gives the actual integral
estimate

```text
norm(Fourier(f)(z)-Fourier(g)(z))
  <= integral_R exp(A*abs(x))*norm(f(x)-g(x)) dx.
```

The estimate is uniform in `z` over the whole closed strip. Lean therefore proves both the
sequence theorem and the two-stage transfer:

```text
Fourier(g_n) -> target uniformly on abs(Im z)<=A
StripError(A,f_n,g_n) -> 0
------------------------------------------------
Fourier(f_n) -> target uniformly on abs(Im z)<=A.
```

The same theorem is specialized to the project's literal
`weilGroundStateCenteredFourier` source coordinate with a varying interval length.

## Negative control

Let the fixed transform point be `z0=-i/4`. The module constructs

```text
p_n(x) = exp(-n/4) *
  compactLaplaceModulatedBump(1/4, x-n).
```

Every `p_n` is smooth and compactly supported. Lean proves:

```text
abs(Im z0) < 1/2,
Fourier(p_n)(z0) = 1                       for every n,
integral_R norm(p_n(x)) dx -> 0,
integral_R norm(p_n(x))^2 dx -> 0.
```

Consequently the transforms do not converge uniformly to zero even on the closed
quarter-strip. Ordinary unweighted `L1`, ordinary unweighted `L2`, and a support-blind
finite-dimensional projective defect cannot by themselves supply the approximation topology
required at this Connes ground-state edge.

## Historical reading

Connes arXiv:2602.04022 Fact 6.4 proves compact-uniform closed-substrip convergence of the
explicit prolate packet transforms to `Xi`. Section 6.6 then asks that those packets approximate
the true minimizers sufficiently well.

The formal audit identifies a sufficient meaning of "sufficiently well": for every fixed
`A<1/2`, prove

```text
integral_R exp(A*abs(x))*norm(theta_x(x)-k_lambda(x)) dx -> 0.
```

A different estimate may replace this one only if it implies the same closed-strip transform
control. The existing Rayleigh-excess-to-gap consumer remains useful, but an unweighted
projective estimate needs an additional support-sensitive tail rate.

## Verification

- preregistration commit: `fde35b125edd7de20e80727911fc1dad22471d78`;
- preregistration Lean Action: run `30486451346`, job `90693225570`, passed in `1m36s`;
- frozen implementation commit: `2be884b27f505542f11ca380d8ac384b0e4bdfd2`;
- implementation Lean Action: run `30487452115`, job `90696590632`, passed in `2m32s`;
- one proven Target: `H7.weil-ground-state.fourier-strip-topology`;
- nine exact TargetChecks;
- nine selected transitive axiom prints, each containing only `propext`,
  `Classical.choice`, and `Quot.sound`;
- warning-as-error: production module, Targets, TargetChecks, AxiomsAudit, and root pass;
- forbidden and resource-relaxation scans: empty;
- `git diff --check`: empty;
- full repository build: `8803/8803`.

## Boundary

No actual `theta_x-k_lambda` weighted estimate, simple-even source ground-state theorem,
all-real-zero limit theorem, H7, or RH is proved. The global RH Goal remains active.
