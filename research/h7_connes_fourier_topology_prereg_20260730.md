# H7 Connes Ground-State Fourier Topology Preregistration

Date: 2026-07-30

Campaign: `LITERATURE-20260730-H7-CONNES-FOURIER-TOPOLOGY-01`

Node: `H7-CONNES-GROUNDSTATE-FOURIER-TOPOLOGY-01`

Mode: `LITERATURE / HISTORICAL_OMISSION / PROOF-ATTEMPT / FALSIFICATION`

Status: `FULL_SUCCESS / LOCAL_AUDIT_GREEN`

## Parent and available chain

- `parent_closure`: H2 classical detector contour-shift receipt
  `a141b4acd1a606c815e7f179a703e882a27fd8bb`, public run `30485670826`, build job
  `90690587648`, passed in `1m56s`.
- `available_modules`:
  `LeanLab/Riemann/WeilGroundStateAlignment.lean`,
  `LeanLab/Riemann/WeilGroundStateRayleighGap.lean`,
  `LeanLab/Riemann/WeilCompactLaplaceSeparator.lean`,
  `LeanLab/Riemann/WeilCompactPositivityCriterion.lean`,
  `LeanLab/Riemann/WeilGroundStateFiniteMatrix.lean`, and
  `LeanLab/Riemann/WeilFiniteDictionaryExplicitFormula.lean`.
- `available_chain`: exact source/project Fourier coordinate alignment; compact-Laplace
  translation and modulation identities; smooth normalized compact bumps; actual finite Weil
  source blocks and explicit formula; finite parity certificates; and the quantitative
  Rayleigh-excess-to-gap projective-defect consumer.
- `first_open_obstacle`: `OBS-H7-CONNES-FOURIER-TOPOLOGY-01`.

## Source statement and fixed question

Connes, arXiv:2602.04022, Fact 6.4 proves that the explicit prolate packet transforms converge
to `Xi` uniformly on closed substrips of `abs(Im z)<1/2`. Section 6.6 then requires the packet
`k_lambda` to be a sufficiently good approximation of the true minimum-eigenvalue vector
`theta_x`.

The fixed question is:

```text
Which function-space error is sufficient to transfer compact-uniform strip convergence
from Fourier(k_lambda) to Fourier(theta_x), and can an unweighted escaping-mass shortcut
be formally ruled out?
```

For `A>=0`, define a centered exponential-strip error of the form

```text
StripError(A,f,g)
  = integral_R exp(A*abs(x)) * norm(f(x)-g(x)) dx.
```

For every `z` with `abs(Im z)<=A`, prove

```text
norm(Fourier(f)(z)-Fourier(g)(z)) <= StripError(A,f,g).
```

Then prove the corresponding uniform sequence transfer and a source-coordinate specialization
for `weilGroundStateCenteredFourier`.

## Full-success criteria

`FULL_SUCCESS` requires all of the following:

1. Define the exponential-strip error and prove its nonnegativity and integrability for
   continuous compactly supported source functions.
2. Prove the exact complex-exponential norm identity and the pointwise majorant
   `norm(exp(i*z*x)) <= exp(A*abs(x))` under `abs(Im z)<=A`.
3. Prove the Fourier-difference bound for actual integrals, with all subtraction and
   integrability hypotheses discharged.
4. Prove a uniform-on-the-whole-closed-strip sequence theorem: strip error tending to zero
   implies one eventual bound valid simultaneously for every `z` in the strip.
5. Prove the two-stage triangle transfer: if the prolate transforms converge uniformly to a
   target and the true-ground-state/prolate strip error tends to zero, then the true
   ground-state transforms converge uniformly to the same target.
6. Construct an explicit smooth compactly supported escaping packet from the project's
   normalized bump, translation, modulation, and exponential scaling.
7. Prove that its unweighted `L1` mass tends to zero while its centered Fourier transform is
   exactly nonzero at a fixed point with `abs(Im z)<1/2`.
8. If technically reasonable without weakening the fixed theorem, also prove its unweighted
   squared mass tends to zero; otherwise record this as a strict optional strengthening.
9. Register one exact H7 Target, add exact TargetChecks, selected axiom prints, and the root
   import.

## Partial, falsification, and blocked criteria

`MEANINGFUL_PARTIAL` requires the compiled uniform positive transfer theorem or the compiled
escaping-packet falsification, plus the exact missing counterpart.

`FALSIFIED_STATEMENT` requires a compiled contradiction to the proposed exponential-strip
majorant under its exact hypotheses. A counterexample only to unweighted convergence is a
successful negative control, not falsification of the fixed positive theorem.

`BLOCKED_API` requires reducing one mathematically exact statement to a named unavailable
integration or filter interface. Tactic friction is not an API block.

## Negative controls and claim boundary

- Fixed-support norm equivalence may not be used uniformly when the support radius grows.
- Pointwise transform convergence is not compact-uniform convergence.
- Unweighted `L1` or `L2` convergence does not control exponential growth at nonreal
  transform arguments.
- Rayleigh excess tending to zero is already known to be insufficient when the spectral gap
  collapses; even projective `L2` convergence still needs a support-sensitive transform rate.
- Numerical agreement of finite zeros is navigation evidence only.
- No actual `theta_x-k_lambda` estimate, simple-even ground-state theorem, Hurwitz limit
  theorem, H7, or RH may be inferred from this topology endpoint.

## Audit gates

Before implementation publication:

1. no `sorry`, `admit`, `native_decide`, custom axiom, `opaque`, or `unsafe`;
2. no heartbeat, recursion-depth, or resource relaxation;
3. warning-as-error compile of the new module and registration files;
4. exact TargetChecks and selected standard-only axiom prints;
5. empty forbidden/resource scans;
6. `git diff --check` and full project build;
7. protected inherited files remain untouched and unstaged.

After frozen implementation public CI, publish immutable evidence, final ledger, and closure
receipt through separate public-green commits. Then stop only this local campaign and rerank
all historical families.

## Public preregistration gate

The docs-only preregistration commit
`fde35b125edd7de20e80727911fc1dad22471d78` passed Lean Action run `30486451346`,
build job `90693225570`, in `1m36s`. Production implementation began only after that
public result.
