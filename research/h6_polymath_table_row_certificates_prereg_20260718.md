# H6 Polymath Table-Row Certificates Preregistration

Date: 2026-07-18

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Mode: `LITERATURE`

Status: `ACTIVE_LOOP_12_PREREGISTERED`

## Exact mathematical endpoint

For

```text
t0 = 93/500,  X = 5*10^12 + 194858,  y0 = 16733/100000,
```

prove unconditionally the time-zero initial region, the time-`t0` final region, and the full
intermediate-time barrier region from Polymath Table 1. Compose them with the already compiled
Polymath criterion to prove that every zero of `H_(1/5)` is real.

## Proposed Lean statements

```lean
theorem deBruijnNewmanPolymathInitialRegionZeroFree_table_row :
    deBruijnNewmanPolymathInitialRegionZeroFree
      (93 / 500) (5 * 10 ^ 12 + 194858) (16733 / 100000)

theorem deBruijnNewmanPolymathFinalRegionZeroFree_table_row :
    deBruijnNewmanPolymathFinalRegionZeroFree
      (93 / 500) (5 * 10 ^ 12 + 194858) (16733 / 100000)

theorem deBruijnNewmanPolymathBarrierRegionZeroFree_table_row :
    deBruijnNewmanPolymathBarrierRegionZeroFree
      (93 / 500) (5 * 10 ^ 12 + 194858) (16733 / 100000)

theorem deBruijnNewmanAllZerosReal_one_fifth :
    deBruijnNewmanAllZerosReal (1 / 5)
```

All displayed numerals are real. Binder order and final names may change, but the three closed
regions, all intermediate times, the full unbounded final region, and the hypothesis-free final
theorem may not be weakened.

## Loop 1 fixed subedge

Define a source-aligned finite-height RH predicate using project `IsNontrivialZero`, positive
imaginary ordinate, and the critical line. Prove the general transport theorem and its exact
Table 1 specialization:

```lean
def riemannHypothesisUpTo (T : Real) : Prop :=
  forall s : Complex, IsNontrivialZero s ->
    0 < s.im -> s.im <= T -> OnCriticalLine s

theorem deBruijnNewmanPolymathInitialRegionZeroFree_of_riemannHypothesisUpTo
    {t0 X y0 T : Real}
    (hT : X / 2 <= T) (hrad : 0 < y0^2 + 2*t0)
    (hfinite : riemannHypothesisUpTo T) :
    deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0

theorem deBruijnNewmanPolymathInitialRegionZeroFree_table_row_of_rh_up_to_three_trillion
    (hfinite : riemannHypothesisUpTo (3 * 10^12)) :
    deBruijnNewmanPolymathInitialRegionZeroFree
      (93 / 500) (5 * 10^12 + 194858) (16733 / 100000)
```

The `x=0` boundary must be discharged by the compiled positivity/nonvanishing of `H_t(i*y)`, not
by silently strengthening the finite-height predicate from `0<Im(s)` to `0<=Im(s)`.

This Loop 1 subedge is not campaign success and does not assert the Platt--Trudgian computation.

## Source alignment

- Polymath Theorem 1.2(i) requires no zeta zeros in the specified finite rectangle. Under
  `H_0(z)=(1/8)xi((1+i*z)/2)`, a point `z=x+i*y` has zeta ordinate `x/2`; the exact Table 1 bound
  is therefore covered by `X/2 < 3*10^12`.
- The lower imaginary boundary is `sqrt(y0^2+2*t0)>0`, so a transform zero in the initial region
  would map to a finite-height nontrivial zero off the critical line.
- Platt--Trudgian's finite-height result is a computational theorem to be reconstructed by a
  kernel-checkable certificate. It is not imported as an axiom or accepted because a paper says
  that the computation ran.
- Polymath Theorem 1.3 and Corollary 1.4 are the fixed source for the final and barrier
  nonvanishing calculations. The public Arb output at external commit `5fde84e` is never a
  premise.

## Fixed proof architecture

1. Compile the exact finite-height RH-to-initial-region transport and specialized rational
   arithmetic.
2. Define proof-producing rational interval certificates for the real and complex elementary
   functions required by the Polymath approximation. Certificate checking must reduce to kernel
   computation and proved Taylor/remainder bounds; `native_decide` and trusted foreign calls are
   forbidden.
3. Formalize the source-normalized effective Riemann--Siegel approximation and its explicit
   `e_A+e_B+e_C` error bound on `0<t<=1/2`, `0<=y<=1`, `x>=200`.
4. Certify the unbounded final region by a finite lower-range certificate plus a proved analytic
   tail. A sampled finite grid without derivative/remainder control is failure.
5. Certify the closed spacetime barrier by a finite rectangle cover, boundary nonvanishing,
   derivative bounds, and an argument-principle or Rouche theorem connecting each exact
   certificate to zero-freeness of the whole rectangle.
6. Reconstruct the finite RH computation up to `3*10^12`, including zero location and complete
   zero count, or an independently checkable equivalent certificate.
7. Compose the three unconditional predicates with
   `deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_row`.

The order of steps 2--6 may change according to dependency discovery. None may be replaced by an
unproved numerical premise.

## Success and falsification

Success requires all four hypothesis-free statements above, exact TargetChecks, selected
transitive axiom prints, empty forbidden scans, standalone and full builds, and public
implementation/evidence CI.

Falsification means an exact table boundary is not covered by the cited computation, a published
error or derivative bound is false in the compiled normalization, a stored winding output does
not imply zero-freeness under its documented assumptions, or a kernel-checked counterexample is
found. Record the exact witness and an `OBS` node rather than weakening the endpoint.

Local stop or pivot is allowed after the exact first unsupported source step and failed proof
architectures are recorded. It does not pause the persistent RH Goal.

## Known obstacles

- The finite RH verification covers trillions of height and needs a completeness/Turing count,
  not merely a list of approximate zeros.
- The final-region approximation uses up to `N=630783` terms and transcendental expressions.
- The barrier output contains hundreds of time rectangles and millions of mesh evaluations; the
  text summary is not itself a certificate.
- The public computational repository has no usable license grant, so its implementation cannot
  be vendored. The mathematical formulas may be independently reimplemented from the paper.
- Mathlib has no ready-made proof-producing Arb bridge or general certified complex interval
  tactic for this workload.

## DAG and accounting

- `node_id`: H6-Q1
- `relation_to_RH`: strict positive-time upper bound, weaker than RH
- `assumption_frontier_before`: exact source `H_t`, time-zero xi bridge, all-real-zero framework,
  forward preservation, closedness, strip contraction, and the complete conditional Polymath
  three-region criterion are K0
- `hard_gap_before`: all three Table 1 certificates, H6-E/G8, and RH are open in Lean
- `hard_gap_after_on_success`: the known unconditional theorem `Lambda<=1/5` is K0; H6-E/G8 and
  RH remain open
- `expected_hard_gap_delta`: 0 for H6-E/G8 and RH; this reconstructs a known theorem
- `expected_certified_upper_frontier_delta`: 1
- `expected_route_infrastructure_delta`: 1

No Lean proof source may be edited before this preregistration passes public Lean Action CI.

## Preregistration evidence

Commit `652c816cca25c6517fee9654511335ce912ac132` passed public Lean Action CI run
`29629630395`, build job `88040634155`, in `2m16s`. Lean proof-source work began only after this
gate passed.

## Loop 1 local checkpoint

`DeBruijnNewmanTableRowCertificates.lean` now compiles the exact finite-height predicate, full-RH
projection, general initial-region transport, and the second-row specialization through
`3*10^12`. The proof treats `x=0` by the existing imaginary-axis nonvanishing theorem and treats
`x>0` through the exact `H_0`/xi coordinate, so no zero-ordinate case is hidden in the finite RH
premise.

The standalone module, `Targets.lean`, four exact `TargetChecks.lean` witnesses, three selected
axiom prints, forbidden scans, and the full 8,704-job build pass locally. The selected axiom prints
contain only `propext`, `Classical.choice`, and `Quot.sound`.

This checkpoint is conditional. It does not prove `riemannHypothesisUpTo (3*10^12)`, any
unconditional Table 1 region, `deBruijnNewmanAllZerosReal (1/5)`, H6-E/G8, or RH. Implementation
commit `ac96523034b36e2bfafdb007d6dcd95d8e89b625` passed public Lean Action CI run `29630082237`,
build job `88041893271`, in `1m52s`. Evidence commit
`0cd4c215d59c4e37949c09160ad65789bd1fe61d` passed run `29630173782`, build job `88042132339`, in
`1m49s`. Loop 1 is publicly checked; the campaign and persistent RH Goal remain active.

## Loop 2 fixed subedge

Polymath Theorem 1.3 is normalized by the exact functions

```text
log M_0, M_0, alpha, M_t, B_t, b_n^t, N, gamma, s_*, kappa, f_t.
```

Loop 2 must define each quantity from equations (M-def), (logM), (alpha-form), (Mt-def),
(bo-def), and (ft-def)--(N-def-main), using the principal complex logarithm. It must prove the
following source-facing interfaces:

```lean
theorem deBruijnNewmanPolymathLogM0_hasDerivAt
    {s : Complex} (hs : s.im < 0) :
    HasDerivAt deBruijnNewmanPolymathLogM0
      (deBruijnNewmanPolymathAlpha s) s

theorem deBruijnNewmanPolymathB_ne_zero
    {t x y : Real} (hx : 0 < x) :
    deBruijnNewmanPolymathB t x y != 0

theorem deBruijnNewmanH_ne_zero_of_polymathEffectiveApproximation
    {t x y eA eB eC0 : Real}
    (hx : 0 < x) (hA : 0 <= eA) (hB : 0 <= eB) (hC : 0 <= eC0)
    (happrox : norm (deBruijnNewmanH t (x + y*I) /
      deBruijnNewmanPolymathB t x y - deBruijnNewmanPolymathF t x y)
      <= eA + eB + eC0)
    (hstrict : eA + eB + eC0 < norm (deBruijnNewmanPolymathF t x y)) :
    deBruijnNewmanH t (x + y*I) != 0
```

The exact binder presentation may change, but the source expression may not be replaced by an
abstract function. A general final-region consumer and the exact Table 1 second-row specialization
must also compile: pointwise certificates over the full unbounded final region must imply the
existing `deBruijnNewmanPolymathFinalRegionZeroFree` predicate.

This subedge exposes the exact input expected from the eventual effective Riemann--Siegel proof;
it does not assert Theorem 1.3, any explicit error bound, or any external numerical output. Loop 2
success requires exact TargetChecks, selected axiom prints, forbidden scans, a full build, and
public implementation/evidence CI. Failure records the first source normalization or branch-domain
mismatch and does not weaken the campaign endpoint.

Preregistration commit `be2167f3dda7f7b43aec34a1ac0acce270df7337` passed public Lean Action CI
run `29630529731`, build job `88043072197`, in `1m53s`, before Loop 2 proof-source edits.

## Loop 2 local result

The complete displayed source interface now compiles in
`DeBruijnNewmanPolymathRiemannSiegel.lean`. In addition to the preregistered definitions, the
module defines the displayed upper bounds for `e_A+e_B` and `e_C0`, their deterministic total,
the exact unproved approximation proposition, and the strict explicit certificate consumed by the
final-region theorem.

Lean proves the source branch derivative, equivalence of the two displayed `alpha` formulas,
`exp(log M_0)=M_0`, nonvanishing of `M_0`, `M_t`, and `B_t`, exact inclusion of every second-row
final-region point in the Theorem 1.3 parameter region, pointwise nonvanishing, and the exact
second-row final-region consumer. Source-definition witnesses and seven theorem witnesses compile;
the seven selected axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`.
Forbidden scans and the full 8,705-job build pass locally.

Implementation commit `3339ea0f0d6b44f656afd99c388ad313f6b18ed1` passed public Lean Action CI
run `29631298328`, build job `88045278213`, in `1m57s`. Evidence commit
`ba361a944fca85ecafde771761c03f3c0e6f3e05` passed run `29631407988`, build job `88045594759`, in
`2m11s`. Loop 2 is publicly checked; the campaign and persistent RH Goal remain active.

This does not prove `deBruijnNewmanPolymathExplicitApproximation`, any strict numerical
certificate, the final region unconditionally, the other two regions, `Lambda<=1/5`, H6-E/G8, or
RH. The next exact source edge is equation (htz): the imaginary Gaussian heat-kernel representation
and its xi-coordinate form. The existing real-shift Gaussian semigroup moves time backward and is
not a substitute.

## Loop 3 fixed subedge

Section 4 of Polymath arXiv `1904.12438` derives equation `(htz)` from the variance-one-half
Gaussian density. In the project's probability normalization, set `Y=2v`, so
`Y ~ gaussianReal(0,2)`. Loop 3 must prove the following exact source chain without an assumed
integrability premise:

```lean
theorem integral_deBruijnNewmanH_imaginary_gaussian_shift (t r : Real) (z : Complex) :
    integral (fun y => deBruijnNewmanH t (z - (r*y)*I)) (gaussianReal 0 2) =
      deBruijnNewmanH (t + r^2) z

theorem deBruijnNewmanH_eq_gaussian_zero_imaginary_shift
    {t : Real} (ht : 0 <= t) (z : Complex) :
    deBruijnNewmanH t z =
      integral (fun y => deBruijnNewmanH 0 (z - (sqrt t*y)*I)) (gaussianReal 0 2)

theorem deBruijnNewmanH_eq_gaussian_riemannXi
    {t : Real} (ht : 0 <= t) (z : Complex) :
    deBruijnNewmanH t z =
      integral (fun y => (1/8) * riemannXi
        ((1+I*z)/2 + (sqrt t/2)*y)) (gaussianReal 0 2)
```

Exact binder and cast presentation may vary. The mathematical expressions, variance, signs, and
scales may not. Success also requires the pointwise complex-cosine MGF, the full product-space
integrability theorem that licenses Fubini, exact witnesses, selected standard-only axiom prints,
forbidden scans, full build, and public implementation/evidence CI.

The nearest compiled theorem is `integral_deBruijnNewmanH_gaussian_shift`; it uses real
translations and gives `t-r^2`. Loop 3 is materially different because the imaginary translation
grows like `exp(|r*u*Y|)`. The proposed proof integrates this growth with Mathlib's exact Gaussian
MGF, obtaining `exp(r^2*u^2)`, and then invokes the existing super-Gaussian `Phi` majorant.

Failure means recording the first normalization or product-integrability obstruction. A pointwise
Gaussian identity without Fubini, an abstract wrapper, or a theorem carrying the needed
integrability as a hypothesis does not satisfy this subedge. No Lean proof source may be edited
before this preregistration passes public Lean Action CI.

Preregistration commit `38dfa81b2918bf86495954f487cb11a71a89895e` passed public Lean Action CI
run `29631894291`, build job `88047126110`, in `1m50s`, before proof-source edits.

## Loop 3 local result

`DeBruijnNewmanPolymathHeatKernel.lean` now proves the exact variance-two complex MGF,
absolute-exponential Gaussian domination, the pointwise imaginary-shift cosine multiplier, and
full product integrability against the source `Phi` kernel. Fubini then yields

```text
integral H_t(z-i*r*Y) d gaussianReal(0,2)(Y) = H_(t+r^2)(z).
```

For `0<=t`, Lean specializes `r=sqrt(t)` and rewrites `H_0` to obtain exactly

```text
H_t(z) = integral (1/8)*xi((1+i*z)/2+(sqrt(t)/2)*Y)
  d gaussianReal(0,2)(Y).
```

The standalone module, `Targets.lean`, five exact `TargetChecks.lean` witnesses, five selected
axiom prints, forbidden scans, and the full 8,706-job build pass locally. The selected declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`. This is
`KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and `route_infrastructure_delta=1`.
Implementation commit `0601c75a42e0f5218541ef5833f9687fb850c5f2` passed public CI run
`29632643337`, build job `88049238613`, in `2m18s`. Evidence commit
`c6754490e2037a4d867dedee9878943bdad87016` passed run `29632785404`, build job `88049632427`, in
`1m43s`. Loop 3 is publicly checked; the campaign and persistent RH Goal remain active.

Equation `(htz)` is now K0, but Titchmarsh `(xio)`, the infinite diagonal contour `R_(0,N)`, its
residue expansion, the effective approximation, every numerical region certificate,
`Lambda<=1/5`, H6-E/G8, and RH remain open. The next exact source gate starts with a fixed
`5*pi/4` parameterization of `N swarrow N+1`, absolute integrability, and the finite residue shift;
an unproved contour identity or abstract `R_(0,N)` premise is not a substitute.

## Loop 4 fixed subedge

Titchmarsh Section 2.10 and Polymath Section 4 fix the next source edge. Set

```text
d = exp(5*pi*i/4),
L_N(v) = (N+1/2) + d*v,
K_s(w) = w^(-s) exp(i*pi*w^2) / (exp(pi*i*w)-exp(-pi*i*w)).
```

The power is the principal complex power and increasing `v` gives the source orientation. Loop 4
must define the actual parameterized integral `I_N(s)=integral K_s(L_N(v))*d dv`, prove its
absolute integrability, and prove the exact finite shift

```text
I_0(s) = sum (n=1..N) n^(-s) + I_N(s).
```

After multiplying by

```text
(1/8) * (s*(s-1)/2) * pi^(-s/2) * Gamma(s/2),
```

this must yield the source definitions `r_(0,n)`, `R_(0,N)` and

```text
R_(0,0)(s) = sum (n=1..N) r_(0,n)(s) + R_(0,N)(s).
```

Loop 4 must also attack the upstream Titchmarsh identity rather than assume it. With
`F^*(s)=conj(F(conj(s)))`, prove on the source domain excluding integer `s`

```text
(1/8) * riemannXi(s) = R_(0,0)(s) + R_(0,0)^*(1-s),
```

and compose it with the finite shift to expose the exact finite xi decomposition required by
Polymath `(htz-expand)`. Binder presentation and helper names may change, but the fixed line,
principal branch, orientation, prefactor, residue `n^(-s)`, reflection, and xi normalization may
not.

The contour proof must establish denominator nonvanishing, branch-cut avoidance, Gaussian tail
decay, explicit subtraction of the enclosed integer poles, vanishing truncation end segments, and
the affine-parallelogram Cauchy identity. Mathlib has no packaged residue theorem; the intended
route is its Poincare curve-integral theorem for a smooth affine homotopy, applied after extending
the pole-subtracted remainder continuously across the integers.

Success requires the definitions, integrability, finite residue shift, `(xio)`, composed finite xi
decomposition, exact TargetChecks, selected standard-only axiom prints, empty forbidden scans,
standalone/full builds, and public implementation/evidence CI. Definitions alone, an assumed
contour identity, an abstract remainder, a pointwise residue calculation, or a theorem carrying
`(xio)` as a premise is not success.

Falsification means the fixed midpoint line meets a pole or forbidden branch, the orientation or
residue normalization disagrees with the source, the proved tail bounds do not kill the end
segments, or Titchmarsh `(2.10.6)` cannot be connected to project `riemannXi` without a new
analytic-continuation theorem. If the full edge remains open, record the first such dependency and
the strongest compiled proper prefix as infrastructure; do not label the loop closed or claim RH
progress.

Nearest sources: Titchmarsh, *The Theory of the Riemann Zeta-function*, second edition,
`(2.10.1)--(2.10.6)`; Polymath arXiv `1904.12438`, equations `(xio)`, `(ron-def)`, and
`(RON-def)`. The nearest local pole-removal pattern is `TruncatedPerron.lean`; the new geometric
input is
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`.

No Lean proof source may be edited before this Loop 4 preregistration passes public Lean Action CI.

Preregistration commit `80ac70759296e9823a5b55f4ec12afda109364b5` passed public Lean Action CI
run `29633356952`, build job `88051178220`, in `1m51s`, before proof-source edits.

## Loop 4 local checkpoint

Loop 4 reached a compiler-checked proper prefix but not its full success criterion. The new module
`DeBruijnNewmanPolymathRiemannSiegelContour.lean` defines the actual source direction, midpoint
lines, raw kernel, line integrand, raw integral, prefactor, `R_(0,N)`, residue terms, reflection,
and Gaussian majorant. Lean proves the fixed lines avoid both the principal-power branch cut and
all integer poles, the source denominator has norm at least `2`, and the line integrand is
absolutely integrable for every natural `N` and complex `s`.

At every positive integer `n`, Lean also computes the exact denominator derivative and numerator
sign and proves the punctured-neighborhood limit

```text
(w-n) K_s(w) -> n^(-s)/(2*pi*i).
```

These two outputs are bundled in `deBruijnNewmanRiemannSiegelContour_prefix`. Five exact witnesses,
five standard-only axiom prints, empty forbidden scans, `git diff --check`, and the full 8,707-job
build pass locally. Classification is `PARTIAL / BLOCKER_EXPOSED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`.

The first unclosed dependency is the removable extension of the pole-subtracted kernel on an
adjacent affine strip. It must supply the within-domain derivative premise for Mathlib's Poincare
homotopy theorem. The next steps are the finite nonorthogonal parallelogram identity, vanishing of
both end segments as the truncation grows, and induction of the finite residue shift. Titchmarsh
`(xio)` remains downstream and additionally requires the auxiliary contour recurrence and
analytic-continuation step in `(2.10.1)--(2.10.6)`. No contour identity or `(xio)` premise was
postulated, and the full Loop 4 endpoint, numerical Table 1 certificates, H6-E/G8, and RH remain
open.

Implementation commit `7bb3101bc9ecc4698416ec6bfa5d296494a07a46` passed public Lean Action CI
run `29634900588`, build job `88055411542`, in `1m51s`. Evidence commit
`0fcfbd510180161f82cd3ee2cc7b5f0e17c45fe0` passed run `29635011657`, build job
`88055710345`, in `1m52s`. Loop 4 is publicly checked as a proper prefix; its full endpoint remains
open.

## Loop 5 fixed subedge

The next target is selected from Loop 4's first uncancelled dependency, not from theorem count.
For every natural `N` and complex `s`, prove the exact adjacent-line identity

```text
I_N(s) = (N+1)^(-s) + I_(N+1)(s).
```

Use the already defined source lines and raw integrals. At finite truncation height `T`, the proof
must use the nonorthogonal affine parallelogram between `L_N([-T,T])` and
`L_(N+1)([-T,T])`, with both end segments and all orientations explicit. Subtract the exact
principal part

```text
(N+1)^(-s) / (2*pi*i*(w-(N+1)))
```

and define its removable value at `w=N+1` from the derivative-level limit. The extended one-form
must satisfy the continuity and within-domain derivative premise of Mathlib's Poincare homotopy
theorem. The resulting finite contour equality must then be combined with proved Gaussian bounds
that send both end-segment integrals to zero and with the compiled absolute integrability of the
long sides.

Success is the exact infinite adjacent shift, plus exact witnesses, selected standard-only axiom
prints, empty forbidden scans, a full build, and public implementation/evidence CI. An assumed
residue theorem, an abstract holomorphic remainder, the already compiled local residue alone, or a
finite contour equality without the tail limit does not count. Falsification is an incompatible
removable derivative, opposite source orientation, or failure of the proved bounds to kill both
ends. If successful, the following loop will induct over adjacent lines and transport the finite
sum through the source prefactor. If blocked, record the first missing derivative or end estimate
and the strongest compiled prefix. No Loop 5 proof source may be edited before this preregistration
passes public Lean Action CI.

Loop 5 preregistration commit `25f6f43132acec6c3fc066cd800933b0f877455e` passed public Lean Action CI
run `29635161693`, build job `88056094834`, in `2m15s`. Loop 5 proof-source edits are now admitted.

## Loop 5 local checkpoint

`DeBruijnNewmanPolymathRiemannSiegelShift.lean` now proves the fixed infinite endpoint

```text
I_N(s) = (N+1)^(-s) + I_(N+1)(s).
```

The proof pulls the source plane back by `w=(N+1)+d*z`. In these coordinates the crossed pole is
at zero, the denominator's divided slope is nonzero throughout the open band, and a second
`dslope` supplies a holomorphic removable remainder. The boundary integral splits into the exact
principal part and a zero removable contribution.

The implemented finite contour is an axis-aligned pullback rectangle. Consequently the upper
source-line interval is staggered by `sqrt(2)/2` rather than using the literal equal-parameter
parallelogram in the preregistration. Lean proves both fixed-length short-side integrals tend to
zero by a uniform `exp(-pi*x^2/2)` bound, and proves both the symmetric lower interval and the
staggered upper interval tend to their full-line Bochner integrals. Thus the fixed infinite
endpoint is unchanged and exact; the finite-geometry deviation is recorded explicitly.

Five exact witnesses, five selected standard-only axiom prints, forbidden scans,
`git diff --check`, and the full 8,708-job build pass. The finite summation/prefactor
decomposition, Titchmarsh `(xio)`, effective approximation, numerical certificates, H6-E/G8, and
RH remain open. Classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`.

Implementation commit `580bc73436b1571bb6096d2c85071562481598d0` passed public Lean Action CI
run `29637266988`, build job `88061673433`, in `2m2s`.

## Loop 6 fixed finite-decomposition edge

Loop 6 follows Loop 5's declared next exact gate. It does not select a theorem by size or theorem
count: finite summation and exact prefactor transport are the first uncancelled source dependencies
between the public adjacent contour shift and Titchmarsh `(2.10.1)--(2.10.6)`.

For every natural `N` and complex `s`, prove both actual-source identities

```text
I_0(s) = (sum k in Finset.range N, (k+1)^(-s)) + I_N(s),
R_(0,0)(s) = (sum k in Finset.range N, r_(0,k+1)(s)) + R_(0,N)(s).
```

The proof must induct from `deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift`, close the
`N=0` endpoint exactly, use the source indexing at the successor step, and transport the result
through the already defined completed-zeta prefactor. An assumed finite shift, an abstract
telescoping theorem detached from the source definitions, or the raw identity without the exact
`R_(0,N)` decomposition does not count.

Success requires the exact theorems
`deBruijnNewmanRiemannSiegelRawIntegral_finite_shift` and
`deBruijnNewmanRiemannSiegelR0N_finite_decomposition`, exact witnesses, selected standard-only
axiom prints, empty forbidden scans, a full build, and public implementation/evidence CI.
Falsification is an index or sign mismatch visible at `N=0` or `N=1`, or a mismatch between the
displayed finite decomposition and the compiled source prefactor normalization. The known risks
are casts, `Finset.range` successor normalization, and scalar distribution; no analytic premise is
left on this edge.

If successful, the next loop attacks the source auxiliary recurrence and analytic-continuation
chain for Titchmarsh `(xio)`. If blocked, it records the first exact obstruction and strongest
compiled prefix. The H6-Q1 campaign and persistent RH Goal remain active. No Loop 6 proof source
may be edited before this preregistration passes public Lean Action CI.

Loop 6 preregistration commit `0e6ce9b44f72d81ddad115e2a953198bd43c50fd` passed public Lean Action
CI run `29637526635`, build job `88062338513`, in `1m32s`. Proof-source edits were then admitted.

## Loop 6 local checkpoint

`DeBruijnNewmanPolymathRiemannSiegelSum.lean` proves both fixed endpoints. The raw theorem inducts
directly from the public adjacent contour shift, and the remainder theorem unfolds the exact
source definitions and distributes the completed-zeta prefactor. The `N=0` base case and
`Finset.range` successor term are compiler checked; no analytic premise remains or was added.

Both exact witnesses pass. Both selected axiom prints contain only `propext`,
`Classical.choice`, and `Quot.sound`; the forbidden scans and `git diff --check` are empty, and the
full 8,709-job build passes. This is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. Titchmarsh `(2.10.1)--(2.10.6)` and `(xio)`, the effective
approximation, numerical certificates, H6-E/G8, and RH remain open. The next exact gate is the
source auxiliary recurrence and analytic-continuation chain for `(xio)`.

Implementation commit `7ea4238b1f1159d5e59850406fa5b8d3bbebbca4` passed public Lean Action CI
run `29637745080`, build job `88062926702`, in `1m51s`.

## Loop 7 fixed Titchmarsh--Polymath `(xio)` edge

Loop 7 is a `PROOF-ATTEMPT` at the first uncancelled dependency after the public finite contour
decomposition. The authoritative source audit uses Titchmarsh--Heath-Brown, second edition,
Section 2.10, pages 25--27 (`/tmp/TitchmarshZeta.pdf`, SHA-256
`ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`) and Polymath arXiv
`1904.12438`, equation (36) and definitions (37)--(38) (`/tmp/Polymath1904.12438.pdf`, SHA-256
`60d0d2d381227d32f98535a5c43dedb86e333a9006d6819f0bdebdd734085603`).

The fixed endpoint is the actual project/source statement, for every noninteger complex `s`,

```text
(1/8) * riemannXi(s) = R_(0,0)(s) + R_(0,0)^*(1-s).
```

Here `R_(0,0)`, principal complex power, the `5*pi/4` line orientation, Schwarz reflection, Gamma
factor, and `1/8` normalization are the already compiled definitions. Binder presentation for
"noninteger" and helper theorem names may change, but none of these mathematical data may change.

Titchmarsh's source proof fixes the mandatory spine. Define the actual contour integral `Phi(a)`
from `(2.10.1)`. Prove its Gaussian integrability, the translation recurrence `(2.10.2)`, the
parallel-line one-residue relation `(2.10.3)`, and the eliminated formula `(2.10.4)`. Specialize
`a=i*z/(2*pi)+1/2`, multiply by `z^(s-1)`, and integrate on the source ray of argument `-pi/4`.
For `1<re(s)`, prove the double-integral majorant, Fubini inversion, ray Gamma identity, and zeta
Mellin identity. Finally prove the locally uniform logarithmic Gaussian bounds needed for analytic
dependence of the raw contour terms and perform the source analytic continuation to every
noninteger `s`.

Success is the exact theorem `deBruijnNewmanRiemannSiegel_xio`, exact milestone witnesses,
selected standard-only axiom prints, empty forbidden scans, a full build, and public
implementation/evidence CI. An abstract `Phi` supplied with its recurrences, any assumed contour
shift or Mellin identity, a half-plane-only theorem, a detached functional-equation restatement,
or `(xio)` as a premise is rejected. If a line orientation, branch, sign, residue, Mellin domain,
normalization, or continuation condition disagrees with the source, that falsifies the proposed
implementation route and must be recorded.

A compiler-checked source milestone may be retained as a proper prefix if the full endpoint does
not close, but it is then `PARTIAL / BLOCKER_EXPOSED`, with the first remaining dependency named;
it is not Loop 7 success or RH progress. If successful, the next loop composes `(xio)`, the public
finite decomposition, and `(htz)` into the exact Polymath equation (39). The H6-Q1 campaign and
persistent RH Goal remain active. No Loop 7 proof source may be edited before this preregistration
passes public Lean Action CI.

## Loop 7 local checkpoint

The fixed endpoint now compiles as `deBruijnNewmanRiemannSiegel_xio` for every noninteger complex
`s`. The proof constructs Titchmarsh's actual `Phi(a)` contour and derives `(2.10.2)--(2.10.4)`,
the specialized closed form, the slanted-ray Mellin/Fubini identity and Gamma--zeta factors, and
the half-plane form of `(xio)`. It then proves a locally uniform logarithmic Gaussian majorant,
differentiates the raw fixed contour in the complex parameter, establishes analyticity on the
noninteger domain, and applies the identity theorem to obtain the requested global statement.

Six exact witnesses pass. Six selected axiom prints contain only `propext`, `Classical.choice`,
and `Quot.sound`; the forbidden scans and `git diff --check` are empty, and the full 8,712-job
build passes. This is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=1` and
`route_infrastructure_delta=1`: the previously open source edge `(xio)` is now K0, while exact
Polymath equation `(39)`, its effective remainder estimate, numerical certificates, H6-E/G8, and
RH remain open. The next exact gate is the source-aligned composition of public `(xio)`, the
finite `R_(0,0)` decomposition, and `(htz)` into equation `(39)`.

Implementation commit `4be468094a7295778eb50082459f9927f8d0a484` passed public Lean Action CI
run `29648023167`, build job `88089442767`, in `2m46s`.

## Loop 8 fixed Polymath equation `(39)` edge

Loop 8 is a `PROOF-ATTEMPT` at Loop 7's declared next exact gate. The primary source is D.H.J.
Polymath arXiv `1904.12438v2`, source lines 487--524. The local source archive
`/tmp/Polymath1904.12438v2.tar` has SHA-256
`1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863`; its audited
`debruijn.tex` has SHA-256
`560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`.

Write `gamma_2=gaussianReal(0,2)`, `a_t(y)=sqrt(t)*y/2`, and

```text
E_t(F)(s) = integral_y F(s+a_t(y)) d gamma_2(y).
```

The fixed definitions are `r_(t,n)=E_t(r_(0,n))` and `R_(t,N)=E_t(R_(0,N))`, with the already
compiled Schwarz reflection. For every `t>0`, `z.re!=0`, and natural `N`, the fixed endpoint is

```text
H_t(z) = sum_(n=1)^N r_(t,n)((1+i*z)/2)
       + sum_(n=1)^N r_(t,n)^*((1-i*z)/2)
       + R_(t,N)((1+i*z)/2) + R_(t,N)^*((1-i*z)/2).
```

This is source equation `(39)` after the paper's Gaussian variable is changed by `Y=2v`. The
proposed Lean endpoint is `deBruijnNewmanH_riemannSiegel_finite_expansion`, with exact
`Finset.range N` indexing.

The mandatory proof starts from public `(htz)`, proves all horizontally shifted parameters are
noninteger using `z.re!=0`, applies public `(xio)` and both public finite decompositions pointwise,
and then justifies every integral split. In particular, it must prove separate horizontal
Gaussian integrability of the actual `r_(0,n)` and `R_(0,N)` functions at fixed nonzero imaginary
part. The reflected terms must be identified as the Schwarz reflections of the heat-evolved
functions by conjugating the integral and using the exact measure-preserving substitution
`y -> -y`.

The first known obstacle is not finite algebra: existing modules prove fixed-parameter contour
integrability and holomorphy, but no horizontal subgaussian bound for the Gamma-prefactored source
terms. The proof must control the Gamma factor in both real directions away from its poles and
combine it with the raw contour bound. A combined-integrand substitute, assumed integrability,
`N=0`, `t=0`, or equation `(39)` as a premise is rejected.

Success requires the exact endpoint and its growth, integrability, and reflection milestones,
exact witnesses, standard-only axiom prints, clean forbidden scans, a full build, and public
implementation/evidence CI. If blocked, only the strongest compiled source prefix is retained and
the first uncancelled dependency is recorded. If successful, the next exact gate is the source
contour-shift formulae `(rtn-def)` and `(RTN-def)` before Propositions 6.1 and 6.3. H6-Q1 and the
persistent RH Goal remain active. No Loop 8 proof source may be edited before this preregistration
passes public Lean Action CI.

Loop 8 preregistration commit `a726d2c84395d0c7795ba176f6a884d759749cbb` passed public Lean Action CI
run `29648603372`, build job `88090965556`, in `1m48s`, before Loop 8 proof-source edits.

## Loop 8 local checkpoint

The fixed endpoint now compiles as `deBruijnNewmanH_riemannSiegel_finite_expansion` for every
`t>0`, `z.re!=0`, and natural `N`. Lean proves a tunable horizontal bound for the actual raw
contour, transports Gamma control across both real directions, and obtains separate
variance-two Gaussian integrability for every source residue and remainder. It also proves exact
centered-Gaussian negation invariance and uses it to commute heat evolution with Schwarz
reflection. Public `(htz)`, `(xio)`, and the finite decomposition then compose to the exact
two-sum, two-remainder equation `(39)`.

Six exact witnesses and five selected axiom prints pass locally; every selected declaration
depends only on `propext`, `Classical.choice`, and `Quot.sound`. Classification is
`KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=1` and `route_infrastructure_delta=1`. This closes
equation `(39)`, not `(rtn-def)`/`(RTN-def)`, the effective approximation, numerical certificates,
H6-E/G8, or RH. Forbidden scans and `git diff --check` are clean, and the full 8,713-job build
passes. Implementation commit `af6c80c42c0abdfb1cf91147e74a8b88263b20ea` passed public Lean
Action CI run `29651603027`, build job `88098754302`, in `2m41s`. The next exact source gate is
`(rtn-def)` and `(RTN-def)`. Evidence commit `7cf65e6d19afb963e9bb910a1a0e763a5f234344`
passed public CI run `29651774163`, build job `88099210841`, in `1m55s`; Loop 8 is publicly
checked and the H6-Q1 campaign and RH Goal remain active.

## Loop 9 exact `(rtn-def)` / `(RTN-def)` contour-shift edge

Loop 9 is a `PROOF-ATTEMPT` at Loop 8's declared next gate. The exact primary-source text is
D.H.J. Polymath arXiv `1904.12438v2`, `debruijn.tex` lines 528--536. The audited source archive
has SHA-256 `1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863`; the extracted source
has SHA-256 `560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`.

In the project's variance-two normalization, write `a_t(Y)=sqrt(t)*Y/2`. For every `t>0`, positive
natural `n`, arbitrary natural `N`, and arbitrary complex `alpha,beta,s`, the fixed endpoints are

```text
r_(t,n)(s) = exp(-t*alpha^2/4)
  * integral_Y exp(-a_t(Y)*alpha)
      * r_(0,n)(s+a_t(Y)+t*alpha/2) d gaussianReal(0,2)(Y),

R_(t,N)(s) = exp(-t*beta^2/4)
  * integral_Y exp(-a_t(Y)*beta)
      * R_(0,N)(s+a_t(Y)+t*beta/2) d gaussianReal(0,2)(Y).
```

The first formula assumes `s` and `s+t*alpha/2` have imaginary parts of the same strict sign;
the second uses the analogous condition for `beta`. Proposed Lean endpoints are
`deBruijnNewmanRiemannSiegelHeatTerm_contour_shift` and
`deBruijnNewmanRiemannSiegelHeatRemainder_contour_shift`.

The mandatory proof sets `q=sqrt(t)*alpha` and
`g(w)=exp(-w^2/4)*F(s+(sqrt(t)/2)*w)`. It must prove one subgaussian bound uniform over the closed
imaginary strip, use noninteger-domain holomorphy on finite rectangles, send both vertical sides
to zero, pass both long sides to full-line integrals, remove the real part of `q` by Lebesgue
translation, and verify the complete-square factors exactly. The strict half-plane hypothesis is
used to produce a positive lower bound on the imaginary part across the strip, which is needed by
the Gamma recurrence estimate.

Loop 8's one-horizontal-line bounds and integrability are not enough by themselves: the rectangle
ends require constants uniform in the strip parameter. A generic contour theorem alone, a theorem
assuming the desired equality, a real-only or special-parameter shift, `t=0`, or a statement only
for the combined equation `(39)` is rejected. Generic machinery counts only if both actual source
functions are instantiated.

Success requires both exact endpoints, exact statement witnesses, selected standard-only axiom
prints, empty forbidden scans, a full build, and public implementation/evidence CI. A proper prefix
must remove a named strip-bound, rectangle, vertical-decay, or limit obligation and be recorded as
`PARTIAL / BLOCKER_EXPOSED`. On success, the next source gate is the explicit term and remainder
estimates in Propositions 6.1 and 6.3. On blockage, the first failed obligation becomes an H6-Q1
obstruction-map node. The global RH Goal remains active in either case.

No Loop 9 proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 9 compiled result

Preregistration commit `9f42efc9c53c40ad6a8c001a3a9bced3a427290d` passed public Lean Action
CI run `29652764442`, build job `88101787571`; proof-source editing was then admitted.

`DeBruijnNewmanPolymathRiemannSiegelHeatContourShift.lean` compiles the two fixed endpoints
`deBruijnNewmanRiemannSiegelHeatTerm_contour_shift` and
`deBruijnNewmanRiemannSiegelHeatRemainder_contour_shift`. They cover arbitrary `t>0`, arbitrary
complex shifts and source parameter, every natural remainder index, every positive term index,
and the exact strict same-open-half-plane source condition. The variance-two outside factor,
inside linear exponential, and `t*q/2` argument displacement agree exactly with `(rtn-def)` and
`(RTN-def)`.

The compiled proof removes every preregistered analytic obligation. It proves a uniform `1/64`
raw-contour bound over the closed interpolation strip, a uniform `1/128` Gamma bound away from
real-axis integer poles, and actual `3/128` residue/remainder bounds. Combined with the
`-29/128` Gaussian exponent this sends both rectangle ends to zero. A finite Cauchy rectangle,
Bochner limits on both long sides, real translation, variance-two Gaussian density conversion,
and exact completed-square algebra establish the generic shift, which is then instantiated to both
actual source functions.

Exact witnesses and selected axiom prints pass; the final endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Forbidden scans and diff checks are clean, and the complete
8,714-job build passes. Implementation commit `74946858f75e27b306cbf43042df74c447b18740`
passed public Lean Action CI run `29654348324`, build job `88105922988`, in `2m16s`.

Classification is `KNOWN_THEOREM_FORMALIZED`, with `hard_gap_delta=1` and
`route_infrastructure_delta=1`. This closes only `(rtn-def)` and `(RTN-def)`. The next exact source
gate is the quantitative term/remainder estimate pair in Propositions 6.1 and 6.3. Strict
finite-sum certificates, finite RH through `3*10^12`, compact barrier winding, H6-E/G8, and RH
remain open; the persistent RH Goal remains active.

Evidence commit `03ccacba97674a8adabf5e2f5b9b6f810539000e` passed public Lean Action CI
run `29654669529`, build job `88106762342`, in `1m35s`. Loop 9 is publicly checked and enters
route selection for the Proposition 6.1/6.3 quantitative edge; H6-Q1 and the RH Goal remain active.

Loop 9 closure commit `f51a3563cd2fdc19170385fe099d78e3cb0c5b49` passed public Lean Action CI
run `29654773659`, build job `88107035901`, in `1m34s`.

## Loop 10 exact Proposition 6.1 `r_(t,n)` estimate

Loop 10 is a `PROOF-ATTEMPT` at the first quantitative edge after `(rtn-def)`. The primary source is
D.H.J. Polymath arXiv `1904.12438v2`, `debruijn.tex` lines 621--678, together with Lemma 5.1(v)
at lines 542--606 and the alpha derivative estimate at lines 608--615. The audited archive and TeX
hashes remain respectively
`1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863` and
`560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`.

For arbitrary real `sigma`, `T>10`, positive natural `n`, and `0<t<=1/2`, set

```text
s = sigma + i*T,
alpha_n = alpha(s) - log n,
epsilon = exp(((t^2/8)*|alpha_n|^2 + t/4 + 1/6)/(T-3.33)) - 1.
```

The fixed Lean endpoint `deBruijnNewmanRiemannSiegelHeatTerm_effective_estimate` must produce an
actual complex witness `e` with `norm e<=epsilon` and the exact equality

```text
r_(t,n)(s) = M_t(s) * b_n^t / n^(s+(t/2)*alpha(s)) * (1+e).
```

This existential equality is the formal meaning of the source's multiplicative
`1+O_<=(epsilon)`. An unspecified big-O term is not accepted.

The proof must derive, rather than assume, four quantitative layers: the upper-half-plane alpha
derivative and `1/(2*Im(s)-6)` bound; Boyd's effective complex Stirling remainder in Lemma 5.1(v)
and its actual `r_(0,n)` consequence; `Im(alpha_n)>=-0.15` and the resulting legal `(rtn-def)`
shift; and the line-segment Taylor plus exact Gaussian perturbation bound producing `T-3.33`.
Mathlib currently has complex Gamma definitions, recurrence, holomorphy, and integral formulae, but
no effective complex Stirling theorem with this remainder. That is the first registered obstacle.

Proposition 6.1 is selected before Proposition 6.3 because it directly feeds both `e_A` and `e_B`
and reuses the public contour shift. Proposition 6.3 additionally requires Proposition 6.2's absent
Arias de Reyna `C_k(p,sigma)` and `RS_K(s)` expansion, including a measurable truncation order.

Success is only the full actual-function endpoint with exact witness, standard-only axiom audit,
clean forbidden scan, full build, and public implementation/evidence CI. A source-exact Stirling,
actual base-term, alpha/Taylor, or Gaussian theorem may survive a failed full attempt only as
`PARTIAL / BLOCKER_EXPOSED`, with the first remaining dependency named. No Loop 10 proof source may
be edited before this preregistration passes public Lean Action CI. H6-Q1 and the RH Goal remain
active.

## Loop 10 local result

The preregistration gate passed at commit `5a9d4ac09317314feba6e9d6482c2336ec941480`, public Lean
Action CI run `29655041718`, build job `88107737514`, in `1m40s`, before proof-source edits.

Loop 10 closes locally as `PARTIAL / BLOCKER_EXPOSED`, not as Proposition 6.1. The new production
module proves the unconditional alpha derivative bound `norm(alpha'(s))<=1/(2*Im(s)-6)`, the exact
`Im(alpha_n)>=-0.15` certificate, the same-open-half-plane condition, the uniform Taylor-segment
bound, and

```text
norm(log M_0(s+d)-log M_0(s)-alpha(s)*d) <= norm(d)^2/(4*(T-3.08)).
```

It also identifies the exact central term
`M_t(s)*b_n^t/n^(s+(t/2)*alpha(s))`, bounds the displacement square, evaluates the variance-two
Gaussian quadratic exponential, and compiles source equation `(ax)` with denominator `T-3.33`.

For the remaining prefactor, Lean proves the exact identity

```text
R_2(z) = Gamma(z)/GammaStirlingMain(z) - 1 - 1/(12*z)
```

and every subsequent branch and arithmetic conversion from

```text
norm(R_2(z)) <= (41/2000)/norm(z)^2
```

to the source relative-error constant `0.246` and logarithmic-error constant `0.33`. The displayed
Boyd effective remainder itself remains unproved and is now the single first open analytic
obligation. Therefore the full `deBruijnNewmanRiemannSiegelHeatTerm_effective_estimate` endpoint,
Proposition 6.1, and all Table 1 certificates remain open. No conditional consumer of the Boyd
bound is promoted to an unconditional premise.

The exact TargetChecks, ten selected axiom prints, forbidden-token scan, `git diff --check`, and
the full 8,715-job build pass. The selected declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The local inventory found Gamma recurrence, integrals,
holomorphy, coarse strip bounds, and a digamma series, but no existing effective `0.0205` complex
Stirling remainder. Loop 11 must preregister a direct proof of that inequality from an explicit
Boyd-type remainder representation. H6-Q1 and the global RH Goal remain active.

Implementation commit `814083d6c831c4ed18acaf291ce0d64b6199f1da` passed public Lean Action CI
run `29657235672`, build job `88113679693`, in `2m4s`. Loop 10's retained prefix is therefore
publicly checked; its `PARTIAL / BLOCKER_EXPOSED` classification and the open Boyd obligation are
unchanged.

Evidence commit `d656c643194d0685c085f871b1d3c4a159d2f73e` passed public Lean Action CI
run `29657362457`, build job `88114009920`, in `1m30s`. Loop 10 is publicly closed as
`PARTIAL / BLOCKER_EXPOSED`; the global Goal remains active.

## Loop 11 direct Boyd `R_2` attack

Loop 11 is a `PROOF-ATTEMPT` on the single first obligation exposed by Loop 10. Its source endpoint
is Polymath Lemma 5.1(v): for every complex `z` with `abs(z.im)>=1` or `z.re>=1`, prove

```text
norm(Gamma(z)/GammaStirlingMain(z)-1-1/(12*z))
  <= (41/2000)/norm(z)^2.
```

The proposed Lean theorem is
`deBruijnNewmanPolymathGammaStirlingR2_norm_le`, using the existing actual `Complex.Gamma`,
principal-power `deBruijnNewmanPolymathGammaStirlingMain`, and
`deBruijnNewmanPolymathGammaStirlingR2`. The domain may not be narrowed to the positive real axis.

The primary source is Boyd, Proc. R. Soc. A 447 (1994), 609--630, DOI
`10.1098/rspa.1994.0158`, equations `(1.13)`, `(3.1)`, `(3.14)`, and `(3.15)` as cited by the
audited Polymath source. Nemes arXiv `1310.0166` is a secondary primary-paper cross-check for the
resurgence representation and effective bounds.

The mandatory proof chain is an exact remainder representation with branch alignment and absolute
integrability; Boyd's right-half-plane bound; his left-half-plane bound with denominator
`norm(1-exp(2*pi*i*z))`; the lower bound `1-exp(-2*pi)` when `z.im>=1`; conjugation for the lower
half-plane; and a Lean proof that the resulting explicit constant is at most `41/2000`. Assuming
the target inequality or an equivalent effective Gamma estimate, using unspecified asymptotics,
introducing a replacement Gamma function, or proving only sampled/positive-real cases is rejected.

Success also makes the existing Loop 10 prefactor-error consumer unconditional on the source
domain and must pass exact TargetChecks, standard-only axiom audit, forbidden scans, the full build,
and public implementation/evidence CI. A failed endpoint may retain only a source-exact prefix
that removes one named analytic obligation. No Loop 11 proof source may be edited before this
preregistration passes public Lean Action CI. H6-Q1 and the global RH Goal remain active.

Preregistration commit `14bdc45fa1a0e70a26e00e57b4bc8325d73d8ad5` passed public Lean Action CI
run `29657566566`, build job `88114535307`, in `2m10s`. Loop 11 proof-source work is admitted.

## Loop 11 local outcome

The full unconditional `deBruijnNewmanPolymathGammaStirlingR2_norm_le` endpoint did not compile.
The retained source-exact module proves Nemes equation `(28)` in the project's principal branch,
the exact imaginary-axis scaled-Gamma norm, the full imaginary-axis reciprocal bound, open
right-half-plane differentiability, a conditional application of mathlib's right-half-plane
Phragmen--Lindelof theorem, the reflected left-ray/Stokes estimate, the `399/400` denominator
separation, and the final Boyd majorant `<41/2000`.

This is `PARTIAL / BLOCKER_EXPOSED`, not the Boyd `R_2` theorem. The next exact source edge is
Boyd/Nemes equation `(15)` as an absolutely integrable representation of the actual project
remainder, followed by the Theorem 3 contour rotation. The conditional ray bound is also waiting
on Stieltjes equation `(13)` to prove origin continuity, subquadratic growth, and eventual
positive-real boundedness for `1/Gamma*`. No target-equivalent premise was introduced.

The new module, exact TargetChecks, selected standard-only axiom prints, clean forbidden scan,
`git diff --check`, and the full 8,716-job build pass locally. Implementation commit
`3409b7175eb24f1e0f01377795334a08e5f80384` passed public Lean Action CI run `29659089400`, build
job `88118485517`, in `2m19s`. H6-Q1 and the global RH Goal remain active.

## Loop 12 equation `(15)` registration

Loop 11 closure-evidence commit `ee6a6fcd1130203ec84ee4450b952277e9290db4` passed public Lean
Action CI run `29659211122`, build job `88118794823`, in `1m35s`.

Loop 12 now fixes the first remaining edge as the `N=2` Boyd/Nemes equation `(15)` representation
for the actual project remainder on `Re z>0`, together with absolute integrability of both source
kernels. The full exact statement, source signs, assumption frontier, falsification criteria, and
anti-substitution rule are in `research/h6_boyd_r2_loop12_prereg_20260719.md`. No Loop 12 proof
source may be edited before the preregistration commit passes public CI. H6-Q1 and the global RH
Goal remain active.

## Loop 12 local outcome

The actual `N=2` positive- and negative-ray kernels now compile as Bochner integrable for every
`Re z>0` in `DeBruijnNewmanPolymathBoydR2Integral.lean`. Lean proves the exact ray-weight norm
square, a global `sqrt(s)*exp(-pi*s)` majorant, denominator inverse bounds, both continuity
statements, the source-exact RHS normalization, and positive-real conjugacy reduction.

The exact equation `(15)` identity with the project's `GammaStirlingR2` remains open. Nemes cites
Boyd for this resurgence formula; no global saddle-coordinate/Cauchy decomposition or equivalent
Binet/Stieltjes remainder theorem is available locally. No representation or target bound is
assumed. Loop 12 is therefore `PARTIAL / BLOCKER_EXPOSED`, with `hard_gap_delta=0` and
`route_infrastructure_delta=1`. The next upstream gate is the exact positive-real scaled-Gamma
saddle integral obtained from Euler's Gamma integral by `t=x*exp(u)`. H6-Q1 and the global RH Goal
remain active.

Implementation commit `75d39360af35c3fc65ef357b3e4d1aa498c32602` passed public Lean Action CI
run `29660452525`, build job `88122109932`, in `2m17s`. Loop 12 remains
`PARTIAL / BLOCKER_EXPOSED`; H6-Q1 and the global RH Goal remain active.

Closure-evidence commit `9e8cafdbf9e853d3c811d83dd5ef8eb66d0def69` passed public Lean Action CI
run `29660573269`, build job `88122426325`, in `1m29s`. Loop 13 now preregisters the exact
positive-real scaled-Gamma saddle integral with phase `t-1-log(t)` and its integrability, derived
from Euler's Gamma integral and positive scaling only. Full details are in
`research/h6_boyd_scaled_gamma_saddle_loop13_prereg_20260719.md`. No Loop 13 proof source may be
edited before public preregistration CI passes. H6-Q1 and the global RH Goal remain active.

## Loop 13 local outcome

Loop 13 closes locally as `KNOWN_THEOREM_FORMALIZED`. The new production module
`DeBruijnNewmanPolymathBoydSaddleIntegral.lean` proves the exact positive-real saddle identity for
the project's scaled Gamma and integrability of the `t-1-log(t)` kernel for every `x>0`. It uses
Euler's real Gamma integral, positive scaling, and the actual principal-branch Stirling main term;
it does not assume Boyd/Nemes equation `(15)` or an effective `R2` estimate.

Exact Targets, both TargetChecks layers, selected standard-only axiom prints, the forbidden scan,
and the full 8,718-job build pass. The next fixed edge is the global logarithmic-coordinate formula
with phase `exp(u)-u-1`, followed by the analytic inverse of `w^2/2=exp(u)-u-1`. H6-Q1 and the
global RH Goal remain active.

Implementation commit `604199086831750112f5cbf189786860e8137755` passed public Lean Action CI
run `29661356249`, build job `88124459774`, in `1m56s`. Loop 13 is publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

Closure-evidence commit `ca039c09d2e241e6ff36900d2285dea90fd598d1` passed public Lean Action CI
run `29661467295`, build job `88124766580`, in `1m34s`.

## Loop 14 logarithmic-coordinate registration

Loop 14 fixes the global substitution `t=exp(u)`: prove integrability on `R` of the phase kernel
`exp(-x*(exp(u)-u-1))` for every `x>0` and rewrite the exact project scaled-Gamma integral in this
coordinate. The implementation must use the audited one-dimensional Jacobian image theorem on
`univ`, not assume endpoint convergence separately. Full details are in
`research/h6_boyd_log_saddle_loop14_prereg_20260719.md`. H6-Q1 and the global RH Goal remain
active.

Preregistration commit `4d21765574a4e43174a8ace7939ea9d585395d9a` passed public Lean Action CI
run `29661631696`, build job `88125198144`, in `1m31s`.

## Loop 14 local outcome

Loop 14 closes locally as `KNOWN_THEOREM_FORMALIZED`. The new production module
`DeBruijnNewmanPolymathBoydLogSaddleIntegral.lean` uses the global exponential Jacobian to prove
full-real integrability of `exp(-x*(exp(u)-u-1))` and the exact project scaled-Gamma representation
for every `x>0`. Exact checks, selected standard-only axiom prints, the forbidden scan, and the
full 8,719-job build pass. The next fixed edge is the normalized local analytic square-root
coordinate and inverse at the double saddle. H6-Q1 and the global RH Goal remain active.

Implementation commit `7578728f6b16544d983f53d68ea0c10f0beb3d42` passed public Lean Action CI
run `29661915485`, build job `88125929156`, in `2m3s`. Loop 14 is publicly closed as
`KNOWN_THEOREM_FORMALIZED`.

Closure-evidence commit `9724002c25905b4e03cc3db5ccbc34508c1f4f97` passed public Lean Action CI
run `29662032198`, build job `88126225464`, in `1m28s`.

## Loop 15 normalized local-inverse registration

Loop 15 fixes the first complex saddle-coordinate edge: construct the normalized analytic factor
and principal square-root coordinate for `exp(u)-u-1`, prove the global square identity and unit
derivative at the origin, and compile the analytic local inverse with both eventual inverse laws.
Global branch continuation, adjacent saddle images, equation `(15)`, and effective `R2` are not
premises. Full details are in `research/h6_boyd_local_saddle_inverse_loop15_prereg_20260719.md`.

## Loop 15 local result

`LeanLab/Riemann/DeBruijnNewmanPolymathBoydLocalSaddleInverse.lean` now compiles the exact
order-three Taylor removal, normalized principal square-root coordinate, global phase-square
identity, unit derivative at zero, and a defined analytic local inverse with both eventual inverse
laws. Exact target witnesses, selected standard-only axiom prints, forbidden scans, and the full
8,720-job build pass. This is K0 route infrastructure with `rh_frontier_delta=0` and
`route_infrastructure_delta=1`; global continuation, adjacent saddle images, equation `(15)`,
effective `R2`, the unconditional Table 1 certificates, H6-E/G8, and RH remain open.

Implementation commit `016fc4fd71e6b63c142714058547f8b2501fd3a5` passed public Lean Action CI
run `29663109048`, build job `88128987815`, in `1m53s`.

Closure-evidence commit `60ff744dc89d39980be8460162f4e9a319e0faca` passed public Lean Action CI
run `29663259192`, build job `88129384030`, in `2m17s`. Loop 15 is publicly closed.
H6-Q1 and the global RH Goal remain active.

## Loop 16 real saddle diffeomorphism registration

Loop 16 fixes the whole-real extension of the normalized Boyd coordinate: prove global strict
monotonicity and both infinite-end limits, construct the order-isomorphic inverse, compute its
derivative, and compile the exact Gaussian-Jacobian form of the Loop 14 scaled-Gamma integral. It
also identifies the nonzero integer saddles `2*pi*i*n` as complex critical points and records their
coordinate squares, without a global complex branch or equation `(15)` premise. Full details are
in `research/h6_boyd_real_saddle_diffeomorphism_loop16_prereg_20260719.md`.

## Loop 16 local result

`LeanLab/Riemann/DeBruijnNewmanPolymathBoydRealSaddleDiffeomorphism.lean` now compiles the complete
real-axis orientation-preserving order isomorphism, its positive inverse derivative, the exact
Gaussian-Jacobian scaled-Gamma integral, and analytic criticality with coordinate square
`-4*pi*i*n` at every nonzero integer source saddle. Exact Targets and TargetChecks, sixteen
selected standard-only axiom prints, empty forbidden scans, and the full 8,721-job build pass.

This is K0 route infrastructure with `rh_frontier_delta=0`, `hard_gap_delta=0`,
`route_infrastructure_delta=1`, and `obstruction_map_delta=1`. The inverse-Jacobian Cauchy
coefficient representation, adjacent-saddle decomposition, equation `(15)`, effective `R2`, the
unconditional Table 1 certificates, H6-E/G8, and RH remain open.

Preregistration commit `e21951ecbbf91bfaa7f654027de4e671a45ab525` passed public Lean Action CI
run `29663980567`; implementation commit `59d58270504f26555d6f8771e8a101bda4a115c5` passed run
`29664724249`; closure-evidence commit `8e75db36287768ae8521dc85fdcf101a6b173ffd` passed run
`29664938202`. Loop 16 is publicly closed.
