# H6 Actual Xi-Kernel TP2 Preregistration

Date: 2026-07-17

Campaign: `LITERATURE-20260717-H6-XI-KERNEL-TP2-01`

Mode: `LITERATURE`

Status: `PREREGISTRATION_PENDING_PUBLIC_CI`

## Source lock and priority correction

- George Csordas and Richard S. Varga, *Moment Inequalities and the Riemann Hypothesis*,
  Constructive Approximation 4 (1988), 175-198, DOI `10.1007/BF02075457`. Theorem 3.1 proves
  that `log Phi(sqrt t)` is strictly concave for `t>0`; its explicit kernel (1.2) is exactly the
  normalization already compiled as `deBruijnNewmanPhi`.
- Mark W. Coffey and George Csordas, *On the log-concavity of a Jacobi theta function*,
  Mathematics of Computation 82 (2013), 2265-2272, DOI
  `10.1090/S0025-5718-2013-02681-6`, gives a later proof of the same kernel-shape property.
- Avi Gershon, *On the Log-Concavity of the Riemann Xi Kernel*, preprint v2, DOI
  `10.20944/preprints202604.0159.v2`, is not a proof premise. The preceding project campaign
  rejected its attached Lean certificate, and the paper's tail and perturbation prose does not
  supply the complete inequalities required here.

The 1988 source predates the 2026 novelty claim and fixes the classification of this campaign as
known-theorem formalization. The target is still useful because the project currently has no
derivative or quantitative shape interface for the actual theta kernel.

## Exact mathematical target

For the already compiled source kernel

```text
Phi(u) = sum'_(n>=1)
  (2*pi^2*n^4*exp(9*u) - 3*pi*n^2*exp(5*u))
    * exp(-pi*n^2*exp(4*u)),
```

define the explicit first- and second-derivative series `PhiOne` and `PhiTwo`. Prove, for every
`u>=0`,

```text
PhiTwo(u) * Phi(u) - PhiOne(u)^2 < 0.
```

The derivative summands are fixed by writing `y=pi*n^2*exp(4*u)`:

```text
PhiTerm       = exp(u-y) * (  2*y^2 -   3*y)
PhiOneTerm    = exp(u-y) * ( -8*y^3 +  30*y^2 -  15*y)
PhiTwoTerm    = exp(u-y) * ( 32*y^4 - 224*y^3 + 330*y^2 - 75*y).
```

The campaign must also prove that these series are the actual first and second derivatives of
`deBruijnNewmanPhi`. A negative expression involving unrelated helper functions or an
unidentified finite truncation does not meet the target.

## Proposed Lean endpoint

Module: `LeanLab/Riemann/XiKernelStrictLogConcavity.lean`

```lean
def deBruijnNewmanPhiDerivTerm (n : Nat) (u : Real) : Real := ...
def deBruijnNewmanPhiSecondDerivTerm (n : Nat) (u : Real) : Real := ...
def deBruijnNewmanPhiDeriv (u : Real) : Real :=
  tsum fun n => deBruijnNewmanPhiDerivTerm n u
def deBruijnNewmanPhiSecondDeriv (u : Real) : Real :=
  tsum fun n => deBruijnNewmanPhiSecondDerivTerm n u

theorem hasDerivAt_deBruijnNewmanPhi (u : Real) :
    HasDerivAt deBruijnNewmanPhi (deBruijnNewmanPhiDeriv u) u

theorem hasDerivAt_deBruijnNewmanPhiDeriv (u : Real) :
    HasDerivAt deBruijnNewmanPhiDeriv (deBruijnNewmanPhiSecondDeriv u) u

theorem deBruijnNewmanPhi_logConcavityNumerator_neg
    {u : Real} (hu : 0 <= u) :
    deBruijnNewmanPhiSecondDeriv u * deBruijnNewmanPhi u -
        deBruijnNewmanPhiDeriv u ^ 2 < 0

theorem deBruijnNewmanPhi_strictLogConcavity_endpoint :
    (forall u, HasDerivAt deBruijnNewmanPhi
      (deBruijnNewmanPhiDeriv u) u) and
    (forall u, HasDerivAt deBruijnNewmanPhiDeriv
      (deBruijnNewmanPhiSecondDeriv u) u) and
    (forall u, 0 <= u ->
      deBruijnNewmanPhiSecondDeriv u * deBruijnNewmanPhi u -
        deBruijnNewmanPhiDeriv u ^ 2 < 0)
```

## Proof architecture

1. Prove the two displayed term derivatives and summability for powers through eight.
2. Use local compact-interval Gaussian majorants and `hasDerivAt_tsum_of_isPreconnected` twice,
   so the derivative identities hold at every real `u`.
3. Reconstruct the Csordas-Varga quantity
   `g(t)=t*((Phi'(t))^2-Phi(t)*Phi''(t))+Phi(t)*Phi'(t)` in the source variable and prove its
   positivity. The source's three-range decomposition may be replaced by a stronger uniform
   estimate, but every omitted infinite tail must have a proved `tsum` bound.
4. Transport `g(t)>0` through `t=u^2` to the fixed numerator inequality. Use the already compiled
   `deBruijnNewmanPhi_pos` where division or logarithmic equivalence requires positivity.

The 2026 first-term perturbation argument may be used only if every numerical constant, derivative
tail, and monotonicity claim is independently proved in Lean. Its phrases "tighter computation",
"negligible", and "the bound improves" are not accepted as premises.

## Success, falsification, and stop criteria

Success requires all of the following:

- both all-real-point derivative identities compile;
- the strict full-`tsum` numerator inequality compiles for every `u>=0`;
- exact TargetChecks unfold the derivative series and the final inequality;
- selected transitive axiom prints contain only the accepted Lean/mathlib trust base;
- standalone compilation, forbidden-token scans, `git diff --check`, full build, and public CI pass.

Falsification means finding an exact `u>=0` counterexample to the displayed full-series inequality
with a certified enclosure that includes the infinite tail. Exploratory decimal evaluation at
`u=0,0.001,...,2` found the normalized numerator strictly negative throughout; it selects the
target but is not a premise.

Stop with an OBS node if the derivative layer compiles but the source proof requires an explicit
tail or finite-range inequality that cannot be established under the fixed trust and resource
rules. Record the exact missing inequality. Do not close the campaign with only the `n=1` term,
termwise log-concavity, a finite prefix, or unchecked numerical output.

## DAG position and strength

- DAG node: H6 theta-specific shape input below H6-E/G8
- relation to RH: strict TP2 is necessary shape information but is strictly weaker than the
  all-real-zero/TP-infinity endpoint
- `hard_gap_before`: H6-E/G8, W2/G7, M2/G3, and RH open
- expected `hard_gap_delta`: 0
- expected `route_infrastructure_delta`: 1 on full success, otherwise 0 unless the derivative
  interface is retained as a separately audited prerequisite
- expected result on success: `KNOWN_THEOREM_FORMALIZED`

## Nearest attempts and material difference

The nearest attempt is `FALSIFICATION-20260717-H6-XI-LOGCONCAVITY-LEAN-01`, which rejected only
the external formal certificate. H6-Z through H6-X4 formalized positive moments and the all-index
heat-Li criterion. This campaign is materially different because it proves a derivative inequality
for the actual theta kernel with the complete infinite series; it neither extrapolates a finite Li
prefix nor reuses the vacuous external predicate.

## Stop boundary

After the exact TP2 endpoint is proved and audited, stop. Do not claim TP3, TP-infinity,
`deBruijnNewmanAllZerosReal 0`, or RH. The next route selection must decide whether the compiled
shape inequality can support a genuinely higher-order theta determinant or collision invariant.
