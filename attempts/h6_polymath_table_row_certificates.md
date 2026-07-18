# H6 Polymath Table-Row Certificates Attempt Log

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Status: `ACTIVE_LOOP_5_PREREGISTRATION_PUBLIC_CI_PASSED`

## Target

- `mode`: `LITERATURE`
- `node_id`: H6-Q1
- `exact_mathematical_statement`: prove the specialized initial, final, and barrier zero-free
  predicates at `(t0,X,y0)=(93/500,5*10^12+194858,16733/100000)` and then
  `deBruijnNewmanAllZerosReal (1/5)` without hypotheses
- `relation_to_RH`: weaker than RH; reconstructs the known unconditional `Lambda<=0.2` frontier
- `success_criterion`: all four exact theorems compile, pass statement witnesses, standard-only
  axiom audit, full build, and public implementation/evidence CI
- `falsification_criterion`: a kernel-checked counterexample or a precise failure of source
  coverage, normalization, interval enclosure, winding implication, or finite-zero completeness

## Prior state

- `assumption_frontier_before`: the exact conditional Polymath criterion is publicly K0; its
  three region hypotheses remain unproved
- `hard_gap_before`: Table 1 initial/final/barrier certificates, H6-E/G8, and RH open
- `known_obstacles`: finite RH completeness through `3*10^12`; source-aligned effective
  Riemann--Siegel error bounds; large proof-producing transcendental interval certificates;
  compact barrier winding and mesh coverage
- `nearest_primary_source`: Polymath arXiv `1904.12438`, Theorems 1.2/1.3, Corollary 1.4,
  Sections 7--8, Table 1; Platt--Trudgian arXiv `2004.09765`
- `nearest_project_attempt`: `LITERATURE-20260717-H6-POLYMATH-ZERO-FREE-CRITERION-01`, publicly
  closed at the three explicit region predicates
- `new_attack_angle`: consume the now exact region interfaces and reconstruct the numerical proof
  as kernel-checkable rational certificates, starting with a source-aligned finite-RH transport
  that fixes the coordinate and height boundary

## Source reconnaissance

External repository `km-git-acc/dbn_upper_bound` was inspected at
`5fde84e11ba80adad5c225a4eaa0a28b68dc925d`. It contains Arb source, stored sums, and the exact
row's winding summary. The repository grants no software license, and none of its code or decimal
output is imported. Every numerical fact must be independently re-proved in Lean.

## Attempt log

| loop | mode | result | next decision |
| --- | --- | --- | --- |
| 0 | `ROUTE_SELECTION / LITERATURE` | Fixed the full hypothesis-free Table 1 endpoint after source and external-artifact audit. Identified the three independent certificate layers and the exact first subedge from finite-height RH to the initial region. No proof source edited. | Commit and publicly build the preregistration. Only after green CI, begin Loop 1 on the exact finite-height transport; do not assert the external computation. |
| 1 | `LITERATURE` | Compiled `riemannHypothesisUpTo`, the general finite-height-RH transport, and the exact Table 1 specialization through height `3*10^12`. The `x=0` boundary uses `deBruijnNewmanH_mul_I_ne_zero`; the positive branch derives the exact `x/2` zeta ordinate and contradicts the positive lower `y` boundary. Standalone checks, exact witnesses, standard-only axiom prints, forbidden scans, and the full 8,704-job build pass locally. This is conditional on `riemannHypothesisUpTo (3*10^12)` and proves no unconditional region. | Keep the campaign active. Loop 2 should attack the source-normalized effective Riemann--Siegel approximation and error consumer needed by the final and barrier certificates; do not build interval infrastructure detached from an exact `H_t` statement. The finite RH computation, final region, and barrier remain open. |
| 2 | `LITERATURE` | Formalized the exact Theorem 1.3 normalization: source arguments, `log M_0`, `M_0`, both formulas for `alpha`, `M_t`, `B_t`, `b_n^t`, `N`, `gamma`, `s_*`, `kappa`, `f_t`, the displayed `e_A+e_B` and `e_C0` upper bounds, and their total. Lean proves the branch derivative on the lower half-plane, `exp(log M_0)=M_0`, `B_t!=0` for `x>0`, exact inclusion of the second-row final region in the theorem's parameter region, Corollary 1.4, and both general and exact-row final-region certificate consumers. Definition witnesses, seven theorem witnesses, seven standard-only axiom prints, forbidden scans, and the full 8,705-job build pass locally. The deterministic approximation inequality remains an unproved `Prop`. | Keep the campaign active. Loop 3 attacks the paper's first analytic identity `H_t(z)=integral H_0(z-i*sqrt(t)*Y) d gamma_2(Y)` and its exact xi-coordinate form. The existing compiled Gaussian theorem averages real translations and moves time backward; it cannot discharge this imaginary-shift forward representation. |
| 3 | `LITERATURE` | Proved the exact complex MGF and absolute-exponential moment control for `gaussianReal(0,2)`, the imaginary-shift cosine multiplier `exp((r*u)^2)`, full product integrability, the general identity `integral H_t(z-i*r*Y)=H_(t+r^2)(z)`, the `r=sqrt(t)` reconstruction from `H_0`, and the exact `(htz)` xi-coordinate form. Five exact witnesses, five standard-only axiom prints, forbidden scans, and the full 8,706-job build pass locally. | Keep the campaign active. Loop 4 must confront the next source edge rather than add another heat wrapper: define the fixed `5*pi/4` infinite-line contour `R_(0,N)`, prove its integrability and residue shift, and reconstruct Titchmarsh `(xio)`/the finite `R_(0,0)` decomposition. The effective approximation and all numerical certificates remain open. |
| 4 | `LITERATURE / PROOF-ATTEMPT` | `PARTIAL / BLOCKER_EXPOSED`. Lean now fixes the source direction and midpoint lines, proves branch-cut and integer-pole avoidance, a uniform denominator lower bound, exact Gaussian decay, a global integrable majorant for the actual raw line integrand, and the exact punctured-neighborhood residue `n^(-s)/(2*pi*i)` at every positive integer. The aggregate `deBruijnNewmanRiemannSiegelContour_prefix` compiles with five exact witnesses, five standard-only axiom prints, empty forbidden scans, and the full 8,707-job local build. The finite residue shift and `(xio)` were not proved, so this is route infrastructure with `hard_gap_delta=0`, not closure of Loop 4 or an RH progress claim. | Keep the campaign and RH Goal active. The first unclosed dependency is a continuous removable extension of the single-pole-subtracted kernel on each affine strip; then apply the Poincare homotopy theorem to a finite nonorthogonal parallelogram and prove its end-segment integrals vanish. Only after the finite residue shift closes should the attack advance to Titchmarsh's auxiliary recurrence and analytic continuation for `(xio)`. |
| 5 | `LITERATURE / PROOF-ATTEMPT` | `KNOWN_THEOREM_FORMALIZED` locally. Lean constructs the derivative-supplied removable pole subtraction, proves the exact finite one-pole contour identity, separately sends both fixed-length short sides to zero by a compiled Gaussian majorant, passes both long sides to the full Bochner integrals, and proves `deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift`. Five exact witnesses and five standard-only axiom prints pass. The finite contour uses a complex-linear pullback and a staggered upper truncation, not the literal equal-parameter parallelogram named in preregistration; both upper truncations have the same full-line limit, so the fixed infinite endpoint is unchanged. | Keep the campaign and RH Goal active. Next induct the adjacent identity to `I_0=sum_(1..N)n^(-s)+I_N`, transport it through the exact prefactor to `R_(0,0)=sum r_(0,n)+R_(0,N)`, and then attack the auxiliary recurrence and analytic continuation needed for `(xio)`. No Table 1 certificate or RH consequence is claimed. |

## Loop 4 preregistration

- `mode`: `LITERATURE`
- `fixed_subedge`: formalize the Riemann--Siegel contour identity used between Polymath equations
  `(htz)` and `(htz-expand)`, including the actual infinite diagonal integral, its finite residue
  shift, and the xi decomposition `(xio)`
- `fixed_geometry`: set `d=exp(5*pi*I/4)` and parameterize
  `L_N(v)=(N+1/2)+d*v`, oriented by increasing real `v`; no arbitrary contour premise may
  replace this line
- `raw_kernel`: use the principal complex power in
  `w^(-s)*exp(I*pi*w^2)/(exp(pi*I*w)-exp(-pi*I*w))`; prove the denominator is nonzero on every
  `L_N`, the branch cut is avoided, and the parameterized kernel is integrable on `R`
- `residue_statement`: for every natural `N`, prove the unscaled finite shift
  `I_0(s)=sum_(n=1)^N n^(-s)+I_N(s)`, then multiply by the exact source prefactor to obtain
  `R_(0,0)(s)=sum_(n=1)^N r_(0,n)(s)+R_(0,N)(s)`
- `xio_statement`: define reflection by `F^*(s)=conj(F(conj(s)))` and prove, at least on the
  source domain excluding integer `s`,
  `(1/8)*riemannXi(s)=R_(0,0)(s)+R_(0,0)^*(1-s)`; compose this with the residue statement to
  expose the exact finite xi decomposition consumed by `(htz-expand)`
- `success_criterion`: fixed-line definitions, Gaussian decay/integrability, explicit removable
  pole subtraction, vanishing finite-truncation end segments, the finite residue shift, `(xio)`,
  and the composed finite xi decomposition all compile with exact witnesses and standard-only
  axiom prints
- `falsification_criterion`: the fixed midpoint line meets a denominator zero or forbidden branch,
  the explicit residue has a normalization or orientation different from `n^(-s)`, end segments
  do not vanish under the proved bounds, or Titchmarsh `(2.10.6)` cannot be connected to the
  project's `riemannXi` without an additional unformalized analytic-continuation theorem
- `known_obstacles`: Mathlib has no packaged residue theorem or Riemann--Siegel formula. The
  required contour strip is a non-orthogonal parallelogram, principal `cpow` must be controlled on
  both tails, and `(xio)` additionally needs Titchmarsh's auxiliary contour recurrence and
  analytic-continuation argument
- `nearest_primary_source`: Titchmarsh, *The Theory of the Riemann Zeta-function*, second edition,
  Section 2.10, especially `(2.10.1)--(2.10.6)`; Polymath arXiv `1904.12438`, Section 4,
  equations `(xio)`, `(ron-def)`, and `(RON-def)`
- `nearest_project_attempt`: `TruncatedPerron.lean` removes a simple pole before applying a
  rectangle Cauchy theorem, but only for axis-aligned rectangles
- `new_attack_angle`: use `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_`
  `hasFDerivWithinAt` from Mathlib's Poincare curve-integral API for the affine
  parallelogram; subtract the finite sum of explicit `1/(w-n)` principal parts so the remaining
  one-form extends continuously across all enclosed integers
- `anti_substitution_rule`: definitions alone, an assumed contour-shift equality, a theorem whose
  premise is `(xio)`, an abstract `R_(0,N)`, or only a pointwise residue calculation is not Loop 4
  success

If the full success criterion is not reached, the loop must still attempt it and record the first
uncancelled analytic dependency and the strongest compiled proper prefix. A proper prefix is
infrastructure, not a successful closure of Loop 4 or an RH progress claim.

No Lean proof source may be edited for Loop 4 before this preregistration passes public CI.

Preregistration commit `80ac70759296e9823a5b55f4ec12afda109364b5` passed public Lean Action CI
run `29633356952`, build job `88051178220`, in `1m51s`, before Loop 4 proof-source edits.

## Loop 4 accounting

- `classification`: `PARTIAL / BLOCKER_EXPOSED`
- `compiled_aggregate`: `deBruijnNewmanRiemannSiegelContour_prefix`
- `compiled_geometry`: exact `5*pi/4` direction coordinates, `d^2=i`, `norm d=1`, line real and
  imaginary coordinates, slit-plane membership, and avoidance of every integer
- `compiled_denominator`: exact complex-sine formula, denominator nonvanishing, and the uniform
  lower bound `2 <= norm denominator` on every fixed midpoint line
- `compiled_integrability`: principal-`cpow` norm control, exact Gaussian real exponent,
  completion-of-the-square majorant, majorant integrability, continuity, and absolute
  integrability of the actual source line integrand for every `N` and `s`
- `compiled_residue`: exact denominator derivative at each natural integer, exact numerator sign,
  residue coefficient `n^(-s)/(2*pi*i)`, and the corresponding punctured-neighborhood limit for
  every positive `n`
- `assumption_frontier_after`: fixed-line integrability and local residue normalization are K0;
  no contour-shift equality or `(xio)` premise has been introduced
- `hard_gap_after`: removable extension on the crossed strips, finite affine-parallelogram Cauchy
  identity, vanishing truncation ends, finite residue shift, Titchmarsh `(xio)`, the effective
  approximation, every numerical region certificate, finite RH computation, barrier, H6-E/G8,
  and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `first_uncancelled_dependency`: define the single-pole-subtracted kernel at each crossed integer
  by its derivative-level limit and prove the extension has the within-domain derivative needed by
  `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`
- `next_exact_gate`: close one finite strip shift between adjacent midpoint lines, including both
  finite end segments and their limit; then induct over `N` to obtain
  `I_0(s)=sum_(n=1)^N n^(-s)+I_N(s)`

## Loop 4 local mechanical audit

- standalone source module: passed; only a non-blocking flexible-`simp` linter note is emitted
- `Targets.lean`: passed with the honest proven proper-prefix target
- `TargetChecks.lean`: five exact statement witnesses passed at default resource limits
- `AxiomsAudit.lean`: all five selected declarations print only `propext`,
  `Classical.choice`, and `Quot.sound`
- forbidden proof-token, custom declaration, unsafe/opaque, and resource-relaxation scans: empty
- `git diff --check`: passed
- full `lake build`: passed, 8,707 jobs
- implementation commit `7bb3101bc9ecc4698416ec6bfa5d296494a07a46` passed public CI run
  `29634900588`, build job `88055411542`, in `1m51s`
- evidence commit `0fcfbd510180161f82cd3ee2cc7b5f0e17c45fe0` passed public CI run
  `29635011657`, build job `88055710345`, in `1m52s`
- Loop 4's full preregistered endpoint remains open; the campaign and persistent RH Goal remain
  active

## Loop 5 preregistration

- `mode`: `PROOF-ATTEMPT`
- `selection_basis`: Loop 4's first uncancelled dependency on H6-Q1; this is the shortest graph
  edge from the compiled local residue and line-integrability spine to the finite `R_(0,N)` shift
- `fixed_subedge`: prove the adjacent-line source identity
  `I_N(s)=(N+1)^(-s)+I_(N+1)(s)` for every natural `N` and complex `s`, using the actual raw
  integrals already defined
- `finite_geometry`: for truncation height `T`, use the affine parallelogram whose long sides are
  the oriented source lines `L_N` and `L_(N+1)` restricted to `[-T,T]`; state both short end
  segments explicitly with their source orientations
- `pole_removal`: subtract the exact principal part
  `(N+1)^(-s)/(2*pi*i*(w-(N+1)))`, define its value at the pole by the derivative-level limit,
  and prove the resulting one-form has the continuity and within-domain derivative required by
  Mathlib's Poincare homotopy theorem
- `finite_shift`: derive the finite-truncation contour equality with the exact orientation and
  residue normalization; an assumed residue theorem or contour equality is forbidden
- `tail_limit`: prove both short end-segment integrals tend to zero and pass the two long sides to
  the already compiled Bochner integrals, yielding the adjacent infinite-line shift
- `success_criterion`: the removable extension, finite affine-parallelogram identity, end-segment
  limits, and exact adjacent-line infinite shift compile with exact witnesses, selected
  standard-only axiom prints, empty forbidden scans, full build, and public implementation/evidence
  CI
- `falsification_criterion`: the pole-subtracted kernel does not admit the required derivative at
  the crossed integer, the Poincare orientation produces the opposite residue sign, or the proved
  Gaussian bounds do not force both end segments to zero
- `known_obstacles`: Mathlib's Poincare theorem is stated for a smooth homotopy and requires a
  derivative on the whole image; the principal `cpow` branch and the pole-removal value must be
  controlled simultaneously, and the short segments have truncation-dependent real and imaginary
  coordinates
- `anti_substitution_rule`: a theorem assuming the adjacent shift, an abstract holomorphic
  remainder, only a local residue statement, or a finite contour identity without the infinite
  tail limit is not Loop 5 success
- `next_if_success`: induct the adjacent shift to the finite
  `I_0(s)=sum_(n=1)^N n^(-s)+I_N(s)` identity and transport it through the exact source prefactor
- `next_if_blocked`: record the first missing derivative or end-segment estimate and retain the
  strongest compiler-checked proper prefix; the campaign and RH Goal remain active

No Loop 5 proof source may be edited before this preregistration passes public Lean Action CI.

Loop 5 preregistration commit `25f6f43132acec6c3fc066cd800933b0f877455e` passed public Lean Action CI
run `29635161693`, build job `88056094834`, in `2m15s`. Loop 5 proof-source edits are now admitted.

## Loop 5 local accounting

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `compiled_endpoint`:
  `deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift`, proving for every natural `N` and
  complex `s` that `I_N(s)=(N+1)^(-s)+I_(N+1)(s)`
- `compiled_spine`: the pullback denominator has only the crossed zero in the open band; `dslope`
  supplies a nonvanishing divided denominator and a holomorphic removable remainder; the exact
  principal part has coefficient `(N+1)^(-s)/(2*pi*i)`; the finite boundary integral is
  `(N+1)^(-s)`; both short ends tend to zero under a pure Gaussian majorant; symmetric and
  staggered long intervals both converge to the existing raw integrals
- `finite_geometry_deviation`: instead of the literal equal-parameter affine parallelogram in the
  preregistration, the conformal coordinate `w=(N+1)+d*z` uses an axis-aligned rectangle. This
  staggers the upper source parameter by `sqrt(2)/2`. The stagger disappears in the full-line
  limit, and the preregistered infinite identity is proved exactly. The deviation is retained here
  for audit rather than silently described as the original finite contour.
- `assumption_frontier_after`: the exact adjacent infinite shift is K0; no residue theorem,
  abstract holomorphic remainder, tail limit, finite decomposition, or `(xio)` identity is assumed
- `hard_gap_after`: finite induction and prefactor transport, Titchmarsh `(xio)`, the effective
  approximation, strict finite-sum certificate, finite RH computation, compact barrier,
  H6-E/G8, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `local_audit`: standalone module, Targets, five exact TargetChecks, and five selected axiom
  prints pass; every selected theorem depends only on `propext`, `Classical.choice`, and
  `Quot.sound`; forbidden scans and `git diff --check` are clean; the full 8,708-job build passes
- `next_exact_gate`: prove the finite adjacent-shift induction and exact source-prefactor
  decomposition before attempting Titchmarsh `(2.10.1)--(2.10.6)`
- `public_implementation_evidence`: commit `580bc73436b1571bb6096d2c85071562481598d0`
  passed public Lean Action CI run `29637266988`, build job `88061673433`, in `2m2s`

## Loop 6 preregistration

- `mode`: `LITERATURE`
- `selection_basis`: Loop 5's declared `next_exact_gate`; finite induction and source-prefactor
  transport are the first uncancelled dependencies between the public adjacent contour shift and
  Titchmarsh `(2.10.1)--(2.10.6)`
- `fixed_raw_endpoint`: for every natural `N` and complex `s`, prove on the actual source
  integrals
  `I_0(s) = (sum k in Finset.range N, (k+1)^(-s)) + I_N(s)`
- `fixed_prefactor_endpoint`: for every natural `N` and complex `s`, prove on the actual source
  remainder and residue terms
  `R_(0,0)(s) = (sum k in Finset.range N, r_(0,k+1)(s)) + R_(0,N)(s)`
- `proof_obligations`: induct only from
  `deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift`, close the `N=0` endpoint exactly, use
  `Finset.sum_range_succ` for the successor indexing, and distribute the already defined exact
  prefactor through the finite sum without introducing a new normalization
- `success_criterion`: both exact identities compile under the expected theorem names
  `deBruijnNewmanRiemannSiegelRawIntegral_finite_shift` and
  `deBruijnNewmanRiemannSiegelR0N_finite_decomposition`, with exact TargetChecks witnesses,
  selected standard-only axiom prints, empty forbidden scans, full build, and public
  implementation/evidence CI
- `falsification_criterion`: either the `N=0` or `N=1` specialization has an index/sign mismatch,
  or the source definitions make the displayed prefactor decomposition false
- `known_obstacles`: no analytic input remains on this edge; the remaining risks are natural-to-
  complex casts, `Finset.range` successor normalization, and distribution of a complex scalar
  through the finite sum
- `anti_substitution_rule`: an abstract telescoping lemma, a theorem assuming either finite
  identity, a detached `Finset` equality, or a raw-integral theorem without the exact
  `R_(0,N)`/`r_(0,n)` transport is not Loop 6 success
- `next_if_success`: attack the source auxiliary recurrence and analytic-continuation chain in
  Titchmarsh `(2.10.1)--(2.10.6)` needed for equation `(xio)`
- `next_if_blocked`: record the first exact cast, indexing, or normalization obstruction and the
  strongest compiler-checked prefix; the H6-Q1 campaign and persistent RH Goal remain active

No Loop 6 proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 3 preregistration

- `mode`: `LITERATURE`
- `fixed_subedge`: formalize Polymath equation `(htz)` by proving the imaginary Gaussian
  reconstruction of the source-normalized heat family and its exact xi-coordinate form
- `general_statement`: for all real `t,r` and complex `z`, prove
  `integral H_t(z-i*r*Y) d gaussianReal(0,2)(Y) = H_(t+r^2)(z)`
- `source_statement`: for `0<=t`, specialize `r=sqrt(t)` to prove
  `H_t(z)=integral H_0(z-i*sqrt(t)*Y) d gaussianReal(0,2)(Y)`
- `xi_statement`: rewrite the preceding integrand exactly as
  `(1/8)*xi((1+i*z)/2+(sqrt(t)/2)*Y)`, matching the paper after the change of variables
  `Y=2v`
- `success_criterion`: the pointwise complex-cosine Gaussian moment, product integrability,
  Fubini exchange, general heat-shift identity, nonnegative-time specialization, and xi form all
  compile with exact statement witnesses and standard-only axiom prints
- `falsification_criterion`: the variance-two normalization yields a scale other than `r^2`, the
  `Y=2v` xi coordinate does not match the source, or joint integrability requires an analytic
  premise not supplied by the compiled `Phi` majorant
- `known_obstacles`: the imaginary shift makes the cosine grow exponentially in `Y`; unlike the
  existing real-shift theorem, its product majorant must integrate that growth to
  `exp(r^2*u^2)` before applying the super-Gaussian `Phi` bound
- `nearest_primary_source`: Polymath arXiv `1904.12438`, Section 4, equation `(htz)`
- `nearest_project_attempt`: `integral_deBruijnNewmanH_gaussian_shift`, which averages real
  translations and gives time `t-r^2`
- `new_attack_angle`: use Mathlib's exact Gaussian MGF and the compiled all-quadratic-exponent
  `Phi` integrability theorem to prove the missing imaginary-shift Fubini hypothesis directly
- `anti_substitution_rule`: a pointwise MGF identity, a theorem assuming product integrability,
  or an abstract heat-semigroup wrapper without the exact `H_0` and xi integrands is not success

No Lean proof source may be edited for Loop 3 before this preregistration passes public CI.

Preregistration commit `38dfa81b2918bf86495954f487cb11a71a89895e` passed public Lean Action CI
run `29631894291`, build job `88047126110`, in `1m50s`, before Loop 3 proof-source edits.

## Loop 3 accounting

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `compiled_theorems`:
  `integral_cexp_mul_gaussianReal_zero_two`,
  `integral_rexp_mul_abs_gaussianReal_zero_two_le`,
  `integral_complex_cos_imaginary_gaussian_shift`,
  `integrable_deBruijnNewmanH_imaginary_gaussian_shift_kernel`,
  `integral_deBruijnNewmanH_imaginary_gaussian_shift`,
  `deBruijnNewmanH_eq_gaussian_zero_imaginary_shift`, and
  `deBruijnNewmanH_eq_gaussian_riemannXi`
- `assumption_frontier_after`: equation `(htz)` is K0 for every nonnegative heat time and every
  complex spatial argument; product integrability is proved rather than assumed
- `hard_gap_after`: Titchmarsh `(xio)`, the `R_(0,N)` contour and residue expansion, the
  deterministic Riemann--Siegel approximation, strict finite-sum certificate, unconditional final
  region, finite RH computation, barrier, H6-E/G8, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `normalization_check`: the paper's density `exp(-v^2)/sqrt(pi)` becomes
  `gaussianReal(0,2)` under `Y=2v`; the shift is `-i*sqrt(t)*Y` and the xi increment is
  `(sqrt(t)/2)*Y`
- `next_exact_gate`: parameterize the source line `N swarrow N+1` in direction `exp(5*pi*i/4)`,
  prove absolute integrability and the finite residue shift
  `R_(0,0)(s)=sum_(n=1)^N r_(0,n)(s)+R_(0,N)(s)`, then reconstruct `(xio)` without an assumed
  contour identity

## Loop 3 local mechanical audit

- standalone source module: passed without new diagnostics
- `Targets.lean`: passed with one honest proven known-source target
- `TargetChecks.lean`: five exact theorem witnesses passed at default resource limits
- `AxiomsAudit.lean`: all five selected declarations print only `propext`,
  `Classical.choice`, and `Quot.sound`
- forbidden proof-token, custom declaration, and resource-relaxation scans: empty
- `git diff --check`: passed
- full `lake build`: passed, 8,706 jobs
- implementation commit `0601c75a42e0f5218541ef5833f9687fb850c5f2` passed public CI run
  `29632643337`, build job `88049238613`, in `2m18s`
- evidence commit `c6754490e2037a4d867dedee9878943bdad87016` passed public CI run
  `29632785404`, build job `88049632427`, in `1m43s`
- Loop 3 is publicly checked; the campaign and persistent RH Goal remain active

## Loop 2 preregistration

- `mode`: `LITERATURE`
- `fixed_subedge`: formalize the exact source normalization in Polymath Theorem 1.3 and compile
  Corollary 1.4 all the way to the Table 1 final-region predicate
- `definitions`: source `log M_0`, `M_0`, `alpha`, `M_t`, `B_t`, `b_n^t`, `N`, `gamma`,
  `s_*`, `kappa`, and `f_t`, with the paper's principal complex logarithm and exact signs
- `analytic_statement`: on the strict lower half-plane, the derivative of source `log M_0` is
  the explicit `alpha`; `M_0`, `M_t`, and `B_t(x+iy)` are nonzero when `x>0`
- `certificate_statement`: if
  `norm (H_t(x+iy) / B_t(x+iy) - f_t(x+iy)) <= e_A+e_B+e_C0` and the nonnegative error sum is
  strictly below `norm (f_t(x+iy))`, then `H_t(x+iy) != 0`
- `region_statement`: pointwise certificates on every point of the exact second-row final region
  imply `deBruijnNewmanPolymathFinalRegionZeroFree` at
  `(93/500,5*10^12+194858,16733/100000)`
- `success_criterion`: all source definitions and the derivative, nonvanishing, pointwise, general
  final-region, and exact-row consumer theorems compile with exact witnesses and standard-only
  axiom prints
- `falsification_criterion`: any source sign, conjugation, branch-domain, floor convention, or
  final-region endpoint fails exact alignment, or the claimed consumer cannot be derived from the
  stated norm bound without an additional premise
- `known_obstacles`: this loop does not yet prove the effective approximation inequality or its
  explicit error bounds; the paper's full proof still requires the heat convolution,
  Riemann--Siegel expansion, contour shifts, saddle-point remainders, and large finite sums
- `anti-substitution_rule`: a generic interval or abstract norm lemma detached from the exact
  source `H_t/B_t-f_t` expression is not Loop 2 success

No Lean proof source may be edited for Loop 2 before this preregistration passes public CI.

## Loop 2 accounting

- `compiled_theorems`:
  `deBruijnNewmanPolymathLogM0_hasDerivAt`,
  `deBruijnNewmanPolymathAlpha_eq_compact`,
  `deBruijnNewmanPolymath_exp_logM0_eq_M0`,
  `deBruijnNewmanPolymathB_ne_zero`,
  `deBruijnNewmanPolymath_table_row_final_mem_effectiveRegion`,
  `deBruijnNewmanH_ne_zero_of_polymathExplicitCertificate`, and
  `deBruijnNewmanPolymathFinalRegionZeroFree_table_row_of_explicitCertificates`
- `assumption_frontier_after`: the complete source normalization and exact displayed-error
  consumer are K0; `deBruijnNewmanPolymathExplicitApproximation` is only a definition of the next
  unproved proposition and is not a premise
- `hard_gap_after`: the effective approximation inequality, strict finite-sum certificate,
  unconditional final region, initial finite computation, barrier, H6-E/G8, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `first_analytic_obstacle`: the paper uses an imaginary Gaussian shift to reconstruct positive
  heat time from `H_0`; the compiled project semigroup theorem uses real shifts and moves time
  backward. A new product-integrability/Fubini proof is required.
- `next_exact_gate`: for `0<t<=1/2`, prove
  `H_t(z)=integral H_0(z-sqrt(t)*Y*I) d gaussianReal(0,2)(Y)` and then rewrite the integrand as
  `(1/8)*xi((1+i*z)/2+(sqrt(t)/2)*Y)`

## Loop 2 local mechanical audit

- standalone source module: passed
- `Targets.lean`: passed with two honest proven infrastructure/consumer targets
- `TargetChecks.lean`: all source-definition and seven theorem witnesses passed at default
  resource limits
- `AxiomsAudit.lean`: all seven selected declarations print only `propext`,
  `Classical.choice`, and `Quot.sound`
- forbidden proof-token, custom declaration, and resource-relaxation scans: empty
- `git diff --check`: passed
- full `lake build`: passed, 8,705 jobs
- preregistration commit `be2167f3dda7f7b43aec34a1ac0acce270df7337` passed public CI run
  `29630529731`, build job `88043072197`, in `1m53s`
- implementation commit `3339ea0f0d6b44f656afd99c388ad313f6b18ed1` passed public CI run
  `29631298328`, build job `88045278213`, in `1m57s`
- evidence commit `ba361a944fca85ecafde771761c03f3c0e6f3e05` passed public CI run
  `29631407988`, build job `88045594759`, in `2m11s`
- Loop 2 is publicly checked; the campaign and persistent RH Goal remain active

## Mechanical audit

- exact module compilation: passed for `DeBruijnNewmanTableRowCertificates.lean`
- `Targets.lean`: passed with one in-progress campaign target and one proven conditional subedge
- `TargetChecks.lean` exact witness: four exact witnesses passed
- `AxiomsAudit.lean` and printed axioms: the three new theorem prints contain only
  `propext`, `Classical.choice`, and `Quot.sound`
- forbidden token/declaration/resource scan: empty
- witness audit: external numerical outputs rejected as witnesses
- definition/source alignment: exact `H_0`/xi coordinate, positive ordinate, and Table 1 height
  arithmetic compiled; Platt--Trudgian remains an unproved external computational theorem
- full `lake build`: passed locally, 8,704 jobs

## Loop 1 accounting

- `compiled_theorems`:
  `RiemannHypothesis.riemannHypothesisUpTo`,
  `deBruijnNewmanPolymathInitialRegionZeroFree_of_riemannHypothesisUpTo`, and
  `deBruijnNewmanPolymathInitialRegionZeroFree_table_row_of_rh_up_to_three_trillion`
- `assumption_frontier_after`: the transport from finite RH through `3*10^12` to the Table 1
  initial predicate is K0; the finite RH premise itself is not K0
- `hard_gap_after`: all three unconditional Table 1 certificates, H6-E/G8, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `obstacle_record`: no finite-zero certificate or Turing completeness proof was obtained; the
  final-region approximation and compact barrier certificate were not attacked in Loop 1

## Public evidence

- preregistration commit `652c816cca25c6517fee9654511335ce912ac132` passed public Lean Action CI
  run `29629630395`, build job `88040634155`, in `2m16s`
- implementation commit `ac96523034b36e2bfafdb007d6dcd95d8e89b625` passed public Lean Action CI
  run `29630082237`, build job `88041893271`, in `1m52s`
- evidence commit `0cd4c215d59c4e37949c09160ad65789bd1fe61d` passed public Lean Action CI
  run `29630173782`, build job `88042132339`, in `1m49s`
- Loop 1 is publicly checked; the campaign and persistent RH Goal remain active

## Runtime record

- `model`: GPT-5 Codex; exact deployment identifier not exposed
- `reasoning_effort`: not exposed
- `budget`: persistent Goal has no token budget; no per-loop budget exposed
- `compaction_state`: inherited a compaction summary, then re-read canonical governance,
  `HANDOFF.md`, hard-gap DAG, route atlas, current attempt, exact Lean predicates, and primary
  source text before selection
- `persistent_goal`: active
