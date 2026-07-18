# H6 Polymath Zero-Free-Region Criterion Preregistration

Date: 2026-07-17

Campaign: `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`

Mode: `LITERATURE`

Status: `PREREGISTERED_CI_PASSED`

Public preregistration evidence:

- commit: `8f9425edd6257011b4beea644196053d9ca86d73`
- workflow: `Lean Action CI`
- run: `29573972608`
- job: `87864082110`
- duration: `2m02s`
- conclusion: `success`

## Exact source predicates

For real `t0`, `X`, and `y0`, write a complex point as `x+i*y`. Define the following three
source regions.

```lean
def deBruijnNewmanPolymathInitialRegionZeroFree (t0 X y0 : Real) : Prop :=
  forall x y : Real,
    0 <= x -> x <= X ->
    Real.sqrt (y0 ^ 2 + 2 * t0) <= y -> y <= 1 ->
    deBruijnNewmanH 0 ((x : Complex) + (y : Complex) * Complex.I) != 0

def deBruijnNewmanPolymathFinalRegionZeroFree (t0 X y0 : Real) : Prop :=
  forall x y : Real,
    X + Real.sqrt (1 - y0 ^ 2) <= x ->
    y0 <= y -> y <= Real.sqrt (1 - 2 * t0) ->
    deBruijnNewmanH t0 ((x : Complex) + (y : Complex) * Complex.I) != 0

def deBruijnNewmanPolymathBarrierRegionZeroFree (t0 X y0 : Real) : Prop :=
  forall t x y : Real,
    0 <= t -> t <= t0 ->
    X <= x -> x <= X + Real.sqrt (1 - y0 ^ 2) ->
    Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) <= y ->
    y <= Real.sqrt (1 - 2 * t) ->
    deBruijnNewmanH t ((x : Complex) + (y : Complex) * Complex.I) != 0
```

Binder order and names may change. The closed boundaries, squared-width factors, all intermediate
times, and exact source-normalized `deBruijnNewmanH` may not be weakened.

## Exact mathematical endpoints

The first endpoint is Polymath Proposition 3.3 in the project normalization.

```lean
theorem deBruijnNewmanH_zero_im_abs_lt_of_polymath_regions
    {t0 X y0 : Real} (ht0 : 0 < t0) (hX : 0 < X)
    (hy0 : 0 < y0) (hy1 : y0 <= 1)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (hfinal : deBruijnNewmanPolymathFinalRegionZeroFree t0 X y0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    {z : Complex} (hz : deBruijnNewmanH t0 z = 0) :
    abs z.im < y0
```

The second endpoint composes that exact canopy with the compiled arbitrary-base strip theorem.

```lean
theorem deBruijnNewmanAllZerosReal_add_half_sq_of_polymath_regions
    {t0 X y0 : Real} (ht0 : 0 < t0) (hX : 0 < X)
    (hy0 : 0 < y0) (hy1 : y0 <= 1)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (hfinal : deBruijnNewmanPolymathFinalRegionZeroFree t0 X y0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0) :
    deBruijnNewmanAllZerosReal (t0 + y0 ^ 2 / 2)
```

The third endpoint freezes the exact second row of Polymath Table 1 and verifies in Lean that its
endpoint is no later than `1/5`.

```lean
theorem deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_row
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree
      (93 / 500) (5 * 10 ^ 12 + 194858) (16733 / 100000))
    (hfinal : deBruijnNewmanPolymathFinalRegionZeroFree
      (93 / 500) (5 * 10 ^ 12 + 194858) (16733 / 100000))
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree
      (93 / 500) (5 * 10 ^ 12 + 194858) (16733 / 100000)) :
    deBruijnNewmanAllZerosReal (1 / 5)
```

All numerals above are real. Equivalent exact rational syntax is allowed. The table-row corollary
may not round `0.19999966445` upward without proving the monotone time transfer.

## Source and definition alignment

- D. H. J. Polymath, arXiv `1904.12438`, Proposition 3.3 gives the three-region criterion, and
  Theorem 1.2 combines it with de Bruijn strip contraction.
- Polymath Table 1 gives `X=5*10^12+194858`, `t0=0.186`, and `y0=0.16733` for the displayed
  `0.20` conclusion.
- Platt--Trudgian, arXiv `2004.09765`, Corollary 2 invokes that row after verifying RH above the
  required height. Their computation is not a premise of this campaign.
- The compiled project normalization is the same `H_t`, with
  `partial_t H_t=-partial_z^2 H_t`, evenness, conjugation symmetry, strict time-zero source strip,
  positivity on the imaginary axis, and arbitrary-base squared-strip contraction.

This campaign formalizes known mathematics. No originality or priority claim is made.

## Materially new angle relative to project attempts

The nearest completed campaign proves only the final global-strip contraction. It assumes the
entire zero set at one time is already in a strip and cannot manufacture that canopy from regional
certificates.

The nearest zero-dynamics campaign exports paths and force laws only for simple zeros and studies
real adjacent pairs. The selected criterion instead handles a first nonreal boundary contact,
including a repeated zero. It must add the source Hermite-splitting mechanism or an equally strong
kernel-checked replacement, then combine it with the arbitrary-complex simple-zero force geometry.

The earlier heat-Li, adjacent-gap, PF5, and PF4 branches do not supply this regional continuation
mechanism and are not being reopened.

## Fixed proof architecture

1. Use the strict time-zero source strip and the compiled general strip theorem to bound every
   possible zero in the relevant spacetime slab by `Im(z)^2 <= 1-2*t`.
2. Define the bad-time set of zeros in `0<=Re(z)<=X` above the moving boundary
   `Y(t)=sqrt(y0^2+2*(t0-t))`. Prove compactness/closedness and obtain a first bad time.
3. Show a first-contact zero lies on the lower moving boundary and strictly between the vertical
   sides. Use the final and barrier predicates on the right and positivity of `H_t(i*y)` on the
   left.
4. If the contact zero is repeated, prove the needed backward Hermite splitting with a positive
   square-root imaginary displacement and contradict first contact.
5. If it is simple, construct a local complex zero path, apply the exact regularized force law,
   and prove the Polymath geometric estimate forcing its imaginary velocity below `Y'(t)`.
6. Derive `abs Im(z)<y0` for all time-`t0` zeros. Square the strict bound and invoke
   `deBruijnNewmanAllZerosReal_add_half_sq`.
7. Prove the exact Table 1 rational arithmetic and use `deBruijnNewmanAllZerosReal_mono` to reach
   time `1/5`.

An alternative proof is allowed only if it reaches all three exact endpoints without assuming
simple zeros globally, finite zero sets, an unproved zero enumeration, or an admitted numerical
certificate.

## Adversarial and boundary checks

- Every region boundary is closed. Replacing `<=` by `<` in a premise is not allowed.
- Check `y0=1`, `y0^2+2*t0=1`, and the branch where the final all-real time is at least `1/2`.
- Check contact at `Re(z)=0`, `Re(z)=X`, and at the top strip boundary.
- Repeated zeros of every finite multiplicity must be covered; a theorem conditional on a simple
  first contact is failure.
- The first-contact argument must use a compact bounded spacetime set. Projection of an arbitrary
  closed unbounded zero set is not accepted.
- Conjugation and evenness must account for negative real and negative imaginary parts without
  silently changing a closed boundary.
- The table arithmetic must prove
  `93/500 + (16733/100000)^2/2 <= 1/5` exactly.
- Empty source regions in extreme parameter branches must not make a false conclusion possible;
  the compiled half-time theorem may discharge the corresponding trivial all-real branch.

## DAG and accounting

- `node_id`: H6-H2f
- `gap_id`: Polymath regional continuation criterion immediately before the certified canopy
  computation
- `relation_to_RH`: conditional known upper-bound infrastructure strictly weaker than RH
- `assumption_frontier_before`: source family, strict source strip, joint continuity, positivity,
  simple-zero paths and force, forward preservation, and arbitrary-base strip contraction are
  public
- `hard_gap_before`: the three unconditional region certificates, H6-E/G8, and RH are open
- success `hard_gap_delta`: 0
- success `route_infrastructure_delta`: 1

Success does not prove any region predicate, `Lambda<=0.2`, H6-E/G8, or RH. It changes the exact
remaining H6-Q frontier from a mixed analytic/dynamic theorem to three independently auditable
certificates.

## Success, falsification, and local stop

Success requires all three exact endpoints, exact TargetChecks, selected transitive axiom prints,
forbidden scans, standalone and full builds, and public implementation/evidence CI. Helper-only
closure, including Hermite splitting without the region criterion, is not success.

Falsification means a source clause is incompatible with the compiled normalization, a closed
boundary permits a counterexample, or the claimed table arithmetic is false. Record the exact
counterexample or compiler-checked contradiction rather than weakening the endpoint.

If the exact criterion cannot be closed, record the first missing theorem with its full hypotheses
and failed proof architectures in `attempts/` and the obstruction map, then return to fresh route
selection. The persistent RH Goal remains active in every local outcome.

No Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 8 proof-source checkpoint (2026-07-18)

The repeated-contact branch now has compiler-checked finite analytic multiplicity, a global entire
residual factor, exact variance-two Gaussian backward heat evolution, and an exact all-scale
square-root representation. The remaining preregistered source interface is narrower but still
open: identify the Gaussian moment polynomial with the compiled backward Hermite model, prove the
required compact-uniform limit, transfer a strict upper-half-plane model root to an actual heat
zero, and derive `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`.

This checkpoint does not satisfy campaign success. The three source region certificates, the
Polymath criterion endpoint, `Lambda<=0.2`, H6-E/G8, and RH remain open.

Implementation commit `549b35e736b9a2de02282bd8ac41bf010b858196` passed public Lean Action CI
run `29626216475`, build job `88031047702`, in `2m15s`.

## Loop 9 proof-source checkpoint (2026-07-18)

The Gaussian polynomial is now identified exactly: for every natural `n` and complex `xi`, the
variance-two Gaussian integral of `(xi+y)^n` is the compiled backward Hermite polynomial `P_n(xi)`.
The proof is compiler-checked from the closed complex MGF and iterated Leibniz rule.

The source family and every global entire residual factor from the repeated-zero factorization are
now uniformly bounded on fixed horizontal strips. This supplies a polynomial Gaussian majorant,
proves joint continuity of the scaled residual integral at every `(0,xi)`, and yields the exact
pointwise limit `P_m(xi)*g(z)` as the real scale tends to zero.

The remaining preregistered source interface is compact-uniform convergence on a disk around a
strict upper-half-plane model root, followed by transfer of an actual heat-family zero and the
theorem `deBruijnNewmanHasBackwardUpperLinearEscape_of_repeated`. This checkpoint does not prove
that escape theorem, any of the three region certificates, the Polymath criterion, `Lambda<=0.2`,
H6-E/G8, or RH.

Implementation commit `5e90f7ee9648a55fd10c2ea244741e2fc3254039` passed public Lean Action CI
run `29627444553`, build job `88034514707`, in `2m15s`.
