# H6 General Strip-Contraction Preregistration

Date: 2026-07-17

Campaign: `CAMPAIGN-20260717-H6-GENERAL-STRIP-CONTRACTION-01`

Mode: `LITERATURE`

Status: `LOCAL_IMPLEMENTATION_COMPLETE_PUBLIC_CI_PENDING`

## Exact mathematical endpoint

Let `t`, `delta`, and `muSq` be real, with `0 <= delta` and `2*delta <= muSq`. If every zero of
the exact source-normalized `H_t` satisfies

```text
Im(z)^2 <= muSq,
```

then every zero of `H_(t+delta)` satisfies

```text
Im(z)^2 <= muSq - 2*delta.
```

Consequently, if all zeros of `H_t` lie in `|Im(z)| <= y` for `y>=0`, then every zero of
`H_(t+y^2/2)` is real. Both the quantitative theorem and the all-real endpoint are required.

## Proposed Lean endpoints

Module: `LeanLab/Riemann/DeBruijnNewmanGeneralStrip.lean`

```lean
theorem deBruijnNewmanH_zero_im_sq_le_sub_two_mul
    {t delta muSq : Real} (hdelta : 0 <= delta)
    (hbudget : 2 * delta <= muSq)
    (hstrip : forall z : Complex,
      deBruijnNewmanH t z = 0 -> z.im ^ 2 <= muSq)
    {z : Complex} (hz : deBruijnNewmanH (t + delta) z = 0) :
    z.im ^ 2 <= muSq - 2 * delta

theorem deBruijnNewmanAllZerosReal_add_half_sq
    {t y : Real} (hy : 0 <= y)
    (hstrip : forall z : Complex,
      deBruijnNewmanH t z = 0 -> z.im ^ 2 <= y ^ 2) :
    deBruijnNewmanAllZerosReal (t + y ^ 2 / 2)
```

Binder order and names may change. The arbitrary base time, exact factor `2`, full complex zero
set, arbitrary multiplicity, and endpoint `t+y^2/2` may not be weakened.

## Source and definition alignment

- N. G. de Bruijn, *The roots of trigonometric integrals* (1950), Theorem 13, proves the strip
  contraction under the Gaussian heat multiplier.
- D. H. J. Polymath, arXiv `1904.12438`, states the same result as the final step of its upper-bound
  criterion: a zero-free canopy above height `y` at time `t` gives
  `Lambda <= t+y^2/2`.
- The compiled `deBruijnNewmanH` has the Polymath normalization and satisfies
  `partial_t H_t = -partial_z^2 H_t`. The existing fixed theorem
  `deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul` is exactly the specialization `t=0`,
  `muSq=1`.

No originality claim is made.

## Materially new angle relative to the nearest attempt

`CAMPAIGN-20260717-H6-UPPER-HALF-01` starts only from the unconditional time-zero strip
`Im(z)^2<=1` and concludes the fixed bound `1-2*t`. The new campaign makes the initial time and
strip width parameters, which is necessary to consume a later Polymath canopy certificate.

It reuses the multiplicity-preserving conjugate-factor comparison and Jensen persistence rather
than simple-zero trajectories. This is distinct from the failed heat-Li monotonicity mechanisms:
no Li coefficient, cross-index convolution, moving divisor type, or differentiated zero sum is
used.

## Fixed proof architecture

1. Expose the generic vertical-average squared-strip contraction already proved internally by the
   upper-half module.
2. Generalize the finite `cosh`-iteration invariant from base time zero to arbitrary `t`, with
   step `a=sqrt(2*delta/n)` and exact budget subtraction `n*a^2=2*delta`.
3. Reuse compact-uniform convergence of `dbnForwardApprox t delta n` to
   `deBruijnNewmanH (t+delta)` on every bounded set.
4. If the limit has a zero outside the contracted closed strip, isolate it in a closed ball whose
   every point remains outside. Jensen zero persistence then gives a late approximant zero in the
   ball, contradicting the finite invariant.
5. Specialize `muSq=y^2` and `delta=y^2/2`; the right side is zero, so nonnegativity of
   `Im(z)^2` forces `Im(z)=0`.

An alternative proof is allowed only if it reaches both exact endpoints without assuming simple
zeros, finite degree, or an unproved good time.

## Adversarial and falsification checks

- At `delta=0`, the quantitative theorem must reduce to the input strip without a sign reversal.
- At `t=0`, `muSq=1`, it must recover the compiled `1-2*delta` theorem.
- At `delta=muSq/2`, the remaining squared width must be exactly zero, not an epsilon.
- Negative base times are allowed; no positivity assumption on `t` may enter.
- Repeated zeros, real conjugation fixed points, infinitely many zeros, and an empty divisor must
  remain covered by the existing entire-function argument.
- The `n=0` approximant cannot be used to divide by zero; finite contraction uses positive `n`
  and the limit uses an eventual statement.
- A polynomial-only or simple-zero theorem is failure, not partial campaign success.

The source theorem is known and consistent with the compiled fixed specialization. Falsification
means Lean derives that one of the exact parameter clauses is incompatible with the compiled
normalization; record the exact failed clause rather than weakening it silently.

## DAG and accounting

- `node_id`: H6-H2e
- `gap_id`: source exposure immediately before the Polymath canopy/barrier criterion
- `relation_to_RH`: known quantitative heat-flow infrastructure strictly below the time-zero RH
  endpoint
- `assumption_frontier_before`: exact source family, fixed time-zero strip contraction, forward
  all-real preservation, threshold closedness, and upper-half good time are public
- `hard_gap_before`: unconditional canopy certification at `t=1/5`, H6-E/G8, and RH are open
- success `hard_gap_delta`: 0
- success `route_infrastructure_delta`: 1

Success does not prove `Lambda<=0.2`, a strict improvement below `0.2`, H6-E/G8, or RH. It makes
the exact remaining premise a source-aligned zero-free canopy certificate.

## Success and stop criteria

Success requires both exact endpoints, exact TargetChecks, selected transitive axiom prints,
forbidden scans, standalone and full builds, and public implementation CI. The theorem is then
classified `KNOWN_THEOREM_FORMALIZED`.

If the arbitrary-base compact convergence or finite strip invariant cannot be closed after two
materially distinct implementations, record the first exact dependency as an obstruction and
return to route selection. Helper-only closure is not campaign success. The persistent RH Goal
remains active in every local outcome.

No Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Public preregistration gate

Preregistration commit `2685003e8f6617add0701a2b1680328ca8c4943f` passed public Lean Action CI
run `29571892273`, build job `87857388857`, in `2m2s`. Lean proof-source edits began only after
this gate passed.

## Local implementation gate

`LeanLab/Riemann/DeBruijnNewmanGeneralStrip.lean` compiles both exact preregistered endpoints. The
finite theorem subtracts one squared vertical-shift width per iteration; positive-index forward
approximants therefore satisfy the exact `muSq-2*delta` strip. Compact-uniform convergence and a
Jensen circle-mean argument preserve a limit zero inside any isolating closed ball, closing the
arbitrary-base theorem without a simple-zero or multiplicity assumption. Specializing
`delta=y^2/2` forces the remaining imaginary square to zero.

The exact module, Targets, both TargetChecks, AxiomsAudit, and the total project import compile.
All five selected declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Placeholder, custom-declaration, unsafe, native-decision, and resource-relaxation scans are empty;
`git diff --check` passes; and the full 8,701-job build succeeds under default limits.

Local classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. This exposes the exact source step consuming a future canopy
certificate. It does not itself prove `Lambda<=0.2`, a strict improvement below `0.2`, H6-E/G8,
or RH. Public implementation CI and immutable evidence-backfill CI remain required before local
campaign closure.
