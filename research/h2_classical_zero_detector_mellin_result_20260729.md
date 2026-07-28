# H2 Classical Zero-Detector Mellin Result

Date: 2026-07-29

Campaign: `LITERATURE-20260729-H2-CLASSICAL-ZERO-DETECTOR-MELLIN-01`

Result: `MEANINGFUL_MELLIN_PARTIAL / LOCAL_AUDIT_GREEN / PUBLIC_IMPLEMENTATION_CI_REQUIRED`

## Public prerequisite

The docs-only preregistration commit
`fc6e3c1ac5a8effc4db842716078229c869f6f56` passed public Lean Action run
`30391792808`, job `90384919913`, in `2m0s` before production edits.

## Compiled theorem inventory

The no-sorry module `LeanLab/Riemann/ClassicalZeroDetectorMellin.lean` compiles:

- the finite cutoff Mobius arithmetic function and convolution coefficient;
- the exact divisor-sum formula, value one at `n=1`, and gap through `2<=n<=M`;
- equality of the finite detector mollifier with the project's Mobius Dirichlet partial sum;
- absolute L-series summability and
  `L(a_M,s)=M_M(s)*riemannZeta(s)` for `1<Re(s)`;
- the exponentially smoothed series, its summability, and its exact head-tail split;
- termwise and complete forward Mellin transforms, including the absolute sum-integral
  exchange;
- a `dslope`-based differentiable replacement for
  `Gamma(w)*riemannZeta(rho+w)` at `w=0` for an actual `IsNontrivialZero rho`;
- the translated zeta residue and the exact detector-contour residue
  `Y^(1-rho)*Gamma(1-rho)*M_M(1)`;
- the finite mass inequality, the exact `1/(3*(card+1))` block-or-remainder detector, and the
  uniform-block negative control;
- `classicalDetectorMellinPartialCertificate_endpoint`, whose fields contain no inverse-Mellin
  or global contour-shift premise.

## Preregistration clauses

| clause | status | exact boundary |
| --- | --- | --- |
| 1 | compiled | finite cutoff Mobius and convolution coefficient |
| 2 | compiled | exact divisor-sum formula |
| 3 | compiled | `a_M(1)=1` and gap for `2<=n<=M` |
| 4 | compiled | absolute source-half-plane L-series product |
| 5 | compiled | smoothing, summability, and head-tail gap |
| 6 | partial beyond minimum | complete forward Mellin transform compiles; vertical inverse formula remains open |
| 7 | partial beyond minimum | both local singularity calculations compile; global rectangle shift and horizontal edges remain open |
| 8 | abstract finite layer compiled | cardinality-audited detector compiles; source shifted identity remains open |
| 9 | compiled partial aggregate | certificate deliberately excludes open analytic fields |
| 10 | compiled | uniform-block cardinality control |

## First unavailable theorem

`ClassicalDetectorInverseMellinLine` states the exact vertical inverse identity needed to turn
the forward transform into the source integral, with `0<Y`, `0<c`, and `1-Re(z)<c` explicit.
It is defined as an open proposition and is not used as a premise of any proved declaration.

After it, the next open layer is the infinite rectangle contour shift to
`Re(w)=1/2-Re(rho)`, including horizontal-edge decay from explicit Gamma and zeta bounds. The
compiled local cancellation and residue limits are necessary but do not prove that global
theorem.

## Local evidence

- Direct warning-as-error compilation of the new production module, Targets, and TargetChecks
  passes.
- Ordered builds of the production module, Targets, TargetChecks, and AxiomsAudit pass.
- Selected axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden scans of the new production surface are empty.
- `git diff --check` passes.
- The full repository build passes `8786/8786`.

## Classification

- `historical_subroute_coverage_delta=1`.
- `mobius_coefficient_gap_delta=1`.
- `classical_zero_detector_delta=0`.
- `mellin_shift_delta=0`.
- `zero_density_delta=0`.
- `hard_gap_delta=0`.
- `rh_frontier_delta=0`.

This result is not an inverse Mellin theorem, contour shift, Type-I/Type-II count, zero-density
estimate, H2 proof, or RH proof.
