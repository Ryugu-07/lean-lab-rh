# H6 Polymath Table-Row Certificates Preregistration

Date: 2026-07-18

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Mode: `LITERATURE`

Status: `ACTIVE_LOOP_5_PREREGISTERED_CI_PENDING`

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
