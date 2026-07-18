# H6 Polymath Table-Row Certificates Attempt Log

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Status: `LOOP_12_EVIDENCE_PENDING_CI`

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
| 6 | `PROOF-ATTEMPT` | `KNOWN_THEOREM_FORMALIZED`. Lean inducts the adjacent raw shift to the exact finite identity and transports it through the source Gamma prefactor to `R_(0,0)=sum r_(0,n)+R_(0,N)`. Exact witnesses, standard-only axiom prints, scans, full build, and public implementation CI pass. | Attack the actual Titchmarsh `(2.10.1)--(2.10.6)` recurrence, Mellin, and analytic-continuation chain for `(xio)`; no abstract recurrence or half-plane substitute. |
| 7 | `PROOF-ATTEMPT` | `KNOWN_THEOREM_FORMALIZED`. Lean proves the full noninteger-domain `(xio)` identity from the actual `Phi(a)` contour, recurrences, slanted-ray Mellin/Fubini calculation, Gamma--zeta constants, logarithmic Gaussian parameter bounds, and identity-theorem continuation. Six witnesses, standard-only axiom prints, scans, full build, and public implementation CI pass. | Compose public `(htz)`, `(xio)`, and the finite source decomposition into exact Polymath equation `(39)`, including separate integrability and reflection transport. |
| 8 | `PROOF-ATTEMPT` | `KNOWN_THEOREM_FORMALIZED`. Lean proves tunable horizontal bounds for the raw contour and Gamma prefactor, separate Gaussian integrability of every actual residue and remainder term, centered-Gaussian sign symmetry, heat-evolution/Schwarz-reflection commutation, and the exact two-sum, two-remainder equation `(39)` for every `t>0`, `z.re!=0`, and `N`. Six exact witnesses, five selected standard-only axiom prints, scans, full build, public implementation CI, and public evidence CI pass. | Before the next proof attack, satisfy the outstanding contribution-self-report governance deliverables. Then attack the source contour shifts `(rtn-def)` and `(RTN-def)` before the effective estimates. |
| 9 | `PROOF-ATTEMPT` | `KNOWN_THEOREM_FORMALIZED`. Lean proves a uniform closed-strip bound for the actual raw contour, Gamma-prefactored residue, and remainder; kills both finite-rectangle vertical sides; passes both horizontal sides to Bochner full-line integrals; removes the real contour displacement by translation; and compiles the exact variance-two `(rtn-def)` and `(RTN-def)` endpoints for arbitrary complex shifts in the strict same-half-plane domain. Exact witnesses, standard-only axiom prints, scans, the full 8,714-job build, public implementation CI, and public evidence CI pass. | Audit the exact statements and dependency order of Polymath Propositions 6.1 and 6.3, preregister one source-exact quantitative subedge, and require its public CI before new proof-source edits. The numerical certificates, H6-E/G8, and RH remain open. |
| 10 | `PROOF-ATTEMPT` | `PARTIAL / BLOCKER_EXPOSED` locally. Lean proves the upper-half-plane alpha derivative and sharp norm bound, `Im(alpha_n)>=-0.15`, legal same-half-plane transport, the exact second-order `log M_0` Taylor bound, the displacement-square estimate, the source main-term identity, equation `(ax)`, and every branch conversion from a Boyd `R_2` bound through the `0.246` relative-error and `0.33` logarithmic-error constants. The full Proposition 6.1 endpoint is not proved. | Publicly check the retained prefix, close Loop 10 without a Proposition 6.1 claim, and preregister Loop 11 on the single remaining first obligation `norm R_2(z)<=0.0205/norm(z)^2`. |
| 11 | `PROOF-ATTEMPT` | `PARTIAL / BLOCKER_EXPOSED` locally. Compiled the principal-branch scaled-Gamma continuation, exact imaginary-axis boundary norm, right-half-plane differentiability, conditional Phragmen--Lindelof propagation, mirror-ray/Stokes transfer, denominator bounds, and the strict `41/2000` constant comparison. The actual Boyd/Nemes `R_2` resurgence representation and contour rotation are not yet proved. | Retain the source-exact prefix after public CI. Next preregister equation `(15)` with absolute integrability/contour rotation as the first edge; separately close the Stieltjes inputs for the reciprocal scaled-Gamma growth hypothesis. |

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

Loop 6 preregistration commit `0e6ce9b44f72d81ddad115e2a953198bd43c50fd` passed public Lean Action
CI run `29637526635`, build job `88062338513`, in `1m32s`. Loop 6 proof-source edits were then
admitted.

## Loop 6 local accounting

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `compiled_endpoints`:
  `deBruijnNewmanRiemannSiegelRawIntegral_finite_shift` proves
  `I_0(s)=sum_(k<N)(k+1)^(-s)+I_N(s)`, and
  `deBruijnNewmanRiemannSiegelR0N_finite_decomposition` proves
  `R_(0,0)(s)=sum_(k<N)r_(0,k+1)(s)+R_(0,N)(s)`
- `compiled_spine`: natural-number induction uses only the public adjacent shift and
  `Finset.sum_range_succ`; scalar distribution uses the compiled exact source definitions,
  `mul_add`, and `Finset.mul_sum`
- `assumption_frontier_after`: both finite decompositions are K0; no finite shift, abstract
  telescoping identity, alternative prefactor, or `(xio)` statement is assumed
- `hard_gap_after`: Titchmarsh `(2.10.1)--(2.10.6)` and `(xio)`, effective approximation, strict
  finite-sum certificate, finite RH computation, compact barrier, H6-E/G8, and RH remain open
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `local_audit`: standalone module, both exact TargetChecks witnesses, and both selected axiom
  prints pass; the selected axioms are only `propext`, `Classical.choice`, and `Quot.sound`;
  forbidden scans and `git diff --check` are clean; the full 8,709-job build passes
- `next_exact_gate`: preregister and attack the source auxiliary recurrence and analytic-
  continuation chain in Titchmarsh `(2.10.1)--(2.10.6)` required for equation `(xio)`
- `public_implementation_evidence`: commit `7ea4238b1f1159d5e59850406fa5b8d3bbebbca4`
  passed public Lean Action CI run `29637745080`, build job `88062926702`, in `1m51s`

## Loop 7 preregistration

- `mode`: `PROOF-ATTEMPT`
- `selection_basis`: Loop 6's declared `next_exact_gate`; Titchmarsh `(2.10.1)--(2.10.6)` is the
  first uncancelled source dependency between the public finite `R_(0,0)` decomposition and the
  Polymath heat expansion
- `source_audit`: Titchmarsh--Heath-Brown, second edition, Section 2.10, pages 25--27, local audit
  copy `/tmp/TitchmarshZeta.pdf`, SHA-256
  `ee495ba7e6b7af4722317baa79087881c16f648cb8af72843eb869c7497a03d0`; Polymath arXiv
  `1904.12438`, equation (36) and definitions (37)--(38), local audit copy
  `/tmp/Polymath1904.12438.pdf`, SHA-256
  `60d0d2d381227d32f98535a5c43dedb86e333a9006d6819f0bdebdd734085603`
- `fixed_endpoint`: for every noninteger complex `s`, prove the exact project/source identity
  `(1/8)*riemannXi(s) = R_(0,0)(s) + R_(0,0)^*(1-s)`, where `R_(0,0)`, Schwarz reflection,
  principal complex power, line orientation, and every prefactor are the already compiled source
  definitions
- `forced_source_spine`: define Titchmarsh's actual `Phi(a)` contour from `(2.10.1)`; prove its
  Gaussian integrability, the translation identity `(2.10.2)`, the one-period contour/residue
  identity `(2.10.3)`, and the eliminated closed form `(2.10.4)`; specialize
  `a=i*z/(2*pi)+1/2`; justify the slanted-ray Mellin integral and Fubini for `1<re(s)`; identify
  the Gamma and zeta factors; then prove the analytic dependence and continuation needed to reach
  every noninteger `s`
- `success_criterion`: the exact source-aligned theorem
  `deBruijnNewmanRiemannSiegel_xio` compiles without carrying `(xio)` or an equivalent contour
  decomposition as a premise, with exact milestone witnesses, selected standard-only axiom
  prints, empty forbidden scans, full build, and public implementation/evidence CI
- `falsification_criterion`: the Titchmarsh-to-Polymath change of variables gives a different line
  orientation, branch, sign, or `1/8` normalization; the residue relation has the opposite sign;
  the Mellin/Fubini integral fails on `1<re(s)`; or the two sides cannot be shown analytic on a
  domain supporting the required continuation without assuming the target
- `known_obstacles`: Mathlib has no packaged residue theorem; the slanted double integral needs a
  source-specific integrable majorant; analytic dependence of the infinite raw contour integral
  requires a locally uniform logarithmic Gaussian bound; and the final domain excludes all
  integers because the two separately presented Gamma-prefactored terms are meromorphic there
- `anti_substitution_rule`: an abstract `Phi` satisfying the recurrences, an assumed contour
  shift, an assumed Mellin identity, a theorem only for `1<re(s)`, a detached functional-equation
  restatement, or a theorem assuming `(xio)` is not Loop 7 success
- `proper_prefix_rule`: if the full endpoint does not compile, retain only the strongest source-
  aligned milestone actually proved by Lean and record the first uncancelled dependency; such a
  result is `PARTIAL / BLOCKER_EXPOSED`, never Loop 7 success or RH progress
- `next_if_success`: combine `(xio)` with the public finite decomposition and the public heat
  kernel `(htz)` to prove the exact finite Polymath equation (39) before attacking its effective
  remainder estimate
- `next_if_blocked`: record the first failed contour, Fubini, Mellin, or analytic-continuation
  obligation and choose the next attack from that exact obstruction; the H6-Q1 campaign and
  persistent RH Goal remain active

No Loop 7 proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 7 local accounting

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `compiled_endpoint`: `deBruijnNewmanRiemannSiegel_xio` proves, for every noninteger complex
  `s`, the exact source identity
  `(1/8)*riemannXi(s)=R_(0,0)(s)+R_(0,0)^*(1-s)`
- `compiled_spine`: the actual Titchmarsh `Phi(a)` contour, `(2.10.2)--(2.10.4)`, the specialized
  closed form, slanted-ray Mellin/Fubini and Gamma--zeta identification, the half-plane identity,
  local-uniform logarithmic Gaussian domination, parameter differentiation of the raw contour,
  and identity-theorem continuation on `C` minus the integers are all proved in Lean
- `assumption_frontier_after`: `(xio)` is K0 for every noninteger `s`; no contour recurrence,
  Mellin decomposition, analytic continuation, or equivalent form of the target is assumed
- `hard_gap_after`: exact Polymath equation `(39)`, its effective remainder estimate, strict
  finite-sum certificate, finite RH computation, compact barrier certificate, H6-E/G8, and RH
  remain open
- `hard_gap_delta`: 1
- `route_infrastructure_delta`: 1
- `local_audit`: the standalone endpoint module, six exact TargetChecks witnesses, and six
  selected axiom prints pass; each selected theorem depends only on `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden scans and `git diff --check` are clean; the full
  8,712-job build passes
- `next_exact_gate`: combine public `(xio)`, the public finite decomposition, and public `(htz)`
  into exact finite Polymath equation `(39)` before attacking the effective remainder estimate
- `public_implementation_evidence`: commit `4be468094a7295778eb50082459f9927f8d0a484`
  passed public Lean Action CI run `29648023167`, build job `88089442767`, in `2m46s`

## Loop 8 preregistration

- `mode`: `PROOF-ATTEMPT`
- `selection_basis`: Loop 7's declared `next_exact_gate`; Polymath equation `(39)` is the first
  uncancelled source dependency after public `(htz)`, `(xio)`, and the finite `R_(0,0)`
  decomposition, and it exposes the actual heat-evolved terms consumed by the effective estimates
- `source_audit`: D.H.J. Polymath, arXiv `1904.12438v2`, source lines 487--524; local source
  archive `/tmp/Polymath1904.12438v2.tar`, SHA-256
  `1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863`, and audited
  `debruijn.tex`, SHA-256
  `560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`
- `fixed_definitions`: with `gamma_2=gaussianReal(0,2)` and
  `a_t(y)=((sqrt(t)/2*y : R) : C)`, define
  `E_t(F)(s)=integral_y F(s+a_t(y)) d gamma_2(y)`,
  `r_(t,n)=E_t(r_(0,n))`, and `R_(t,N)=E_t(R_(0,N))`; Schwarz reflection remains the compiled
  `F^*(s)=conj(F(conj(s)))`
- `fixed_endpoint`: for every real `t>0`, complex `z` with `z.re != 0`, and natural `N`, prove
  `H_t(z)=sum_(n=1)^N r_(t,n)((1+i*z)/2)
  +sum_(n=1)^N r_(t,n)^*((1-i*z)/2)
  +R_(t,N)((1+i*z)/2)+R_(t,N)^*((1-i*z)/2)`
- `proposed_lean_endpoint`: `deBruijnNewmanH_riemannSiegel_finite_expansion`, using exact
  `Finset.range N` indexing and the source functions rather than an abstract decomposition
- `forced_proof_spine`: use `(htz)` to expose the xi Gaussian integral; prove every shifted
  parameter is noninteger from `z.re != 0`; rewrite pointwise by `(xio)` and both finite
  decompositions; establish horizontal Gaussian integrability for every `r_(0,n)` and
  `R_(0,N)` at fixed nonzero imaginary part; commute finite sums with the Bochner integral; then
  prove that Gaussian heat evolution commutes with Schwarz reflection using conjugation and the
  measure-preserving substitution `y -> -y`
- `success_criterion`: the exact definitions, horizontal-integrability milestones,
  reflection-commutation theorem, and fixed endpoint compile without target-equivalent premises,
  with exact witnesses, selected standard-only axiom prints, empty forbidden scans, full build,
  and public implementation/evidence CI
- `falsification_criterion`: the variance-two change of variables produces a shift other than
  `sqrt(t)*y/2`; the reflected arguments differ from `(1-i*z)/2`; pointwise `(xio)` crosses an
  integer despite `z.re != 0`; one of the displayed source terms is not separately Gaussian
  integrable; or the resulting finite expression differs from source equation `(39)`
- `known_obstacles`: the public contour modules prove fixed-parameter integrability and parameter
  holomorphy but not the required horizontal subgaussian growth; the Gamma prefactor must be
  controlled in both real directions away from its integer poles; and reflection transport needs
  an exact Gaussian negation/change-of-variables argument before integral conjugation is usable
- `nearest_prior_attempt`: Loops 3, 6, and 7 separately proved `(htz)`, the finite source
  decomposition, and `(xio)`; no prior theorem defines or proves integrability of the actual
  `r_(t,n)` or `R_(t,N)` terms
- `assumption_frontier_before`: `(htz)`, `(xio)` for every noninteger parameter, and the finite
  `R_(0,0)` decomposition are public K0; equation `(39)`, horizontal Gaussian integrability, and
  every effective estimate remain open
- `anti_substitution_rule`: a theorem about the integral of the combined right-hand side, an
  abstract heat-evolution operator supplied with integrability, a statement only at `N=0` or
  `t=0`, or a theorem assuming equation `(39)` is not Loop 8 success
- `proper_prefix_rule`: if the endpoint does not compile, retain only the strongest source-aligned
  growth, integrability, or reflection milestone and record the first uncancelled dependency as
  `PARTIAL / BLOCKER_EXPOSED`; helper theorem count is not success
- `next_if_success`: attack the source contour-shift identities `(rtn-def)` and `(RTN-def)` for
  the exact heat-evolved terms before the effective estimates in Propositions 6.1 and 6.3
- `next_if_blocked`: record the first failed horizontal-growth, Gamma, reflection, or Bochner
  interchange obligation and choose the next attack from that obstruction; H6-Q1 and the global
  RH Goal remain active

No Loop 8 proof source may be edited before this preregistration passes public Lean Action CI.

Loop 8 preregistration commit `a726d2c84395d0c7795ba176f6a884d759749cbb` passed public Lean Action CI
run `29648603372`, build job `88090965556`, in `1m48s`, before Loop 8 proof-source edits.

## Loop 8 local accounting

- `classification`: `KNOWN_THEOREM_FORMALIZED`
- `compiled_endpoint`: `deBruijnNewmanH_riemannSiegel_finite_expansion` proves exact Polymath
  equation `(39)` for every real `t>0`, complex `z` with `z.re!=0`, and natural `N`
- `compiled_spine`: a tunable raw-contour horizontal bound; right-half-plane Gamma control and
  recurrence transport to the left; a tunable Gamma horizontal subgaussian bound; Gaussian
  integrability of every actual `R_(0,N)` and `r_(0,n)` term; centered-Gaussian negation
  invariance; heat-evolution/Schwarz-reflection commutation; and the exact composition of public
  `(htz)`, `(xio)`, and both finite decompositions
- `assumption_frontier_after`: equation `(39)` and every separate Bochner integrability premise
  used by its finite split are K0; no effective remainder estimate, contour-shift identity, or
  numerical certificate is assumed
- `hard_gap_after`: `(rtn-def)` and `(RTN-def)`, the effective estimates in Propositions 6.1 and
  6.3, strict finite-sum certificates, the finite RH computation through `3*10^12`, compact
  barrier winding, H6-E/G8, and RH remain open
- `hard_gap_delta`: 1
- `route_infrastructure_delta`: 1
- `local_audit`: the production module, six exact `TargetChecks` witnesses, and five selected
  `#print axioms` checks pass; each selected declaration depends only on `propext`,
  `Classical.choice`, and `Quot.sound`; forbidden proof-token, custom declaration, and
  resource-relaxation scans are empty; `git diff --check` passes; the full 8,713-job build passes
- `preregistration_public_evidence`: commit `a726d2c84395d0c7795ba176f6a884d759749cbb`
  passed public CI run `29648603372`, build job `88090965556`, in `1m48s`
- `public_implementation_evidence`: commit `af6c80c42c0abdfb1cf91147e74a8b88263b20ea`
  passed public CI run `29651603027`, build job `88098754302`, in `2m41s`
- `public_evidence_backfill`: commit `7cf65e6d19afb963e9bb910a1a0e763a5f234344`
  passed public CI run `29651774163`, build job `88099210841`, in `1m55s`
- `next_exact_gate`: prove the source complex-Gaussian contour shifts `(rtn-def)` and `(RTN-def)`
  for the now concrete heat-evolved terms, before attempting their effective estimates
- `governance_before_next_research_loop`: produce the outstanding `CONTRIBUTIONS.md`, plain-language
  summary, and `VERIFYING.md` deliverables recorded by the sixth architecture audit

## Loop 9 preregistration

- `mode`: `PROOF-ATTEMPT`
- `fixed_subedge`: prove Polymath equations `(rtn-def)` and `(RTN-def)` for the actual public
  `deBruijnNewmanRiemannSiegelHeatTerm` and
  `deBruijnNewmanRiemannSiegelHeatRemainder`, before attempting Propositions 6.1 and 6.3
- `primary_source`: D.H.J. Polymath arXiv `1904.12438v2`, `debruijn.tex` lines 528--536;
  source archive SHA-256
  `1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863` and extracted source
  SHA-256 `560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`
- `source_normalization`: under `Y=2v`, with `a_t(Y)=sqrt(t)*Y/2`, prove for arbitrary complex
  `alpha` and `beta`
  `E_t(r_(0,n))(s)=exp(-t*alpha^2/4) * integral exp(-a_t(Y)*alpha) *
  r_(0,n)(s+a_t(Y)+t*alpha/2) d gaussianReal(0,2)(Y)` and the identical formula with
  `R_(0,N)` and `beta`
- `domain`: `t>0`, `n>0`, arbitrary `N`, and the source condition that `s` and
  `s+t*alpha/2` (respectively `s+t*beta/2`) lie in the same strict open half-plane; this keeps
  the entire interpolation strip away from every integer pole
- `proposed_endpoints`:
  `deBruijnNewmanRiemannSiegelHeatTerm_contour_shift` and
  `deBruijnNewmanRiemannSiegelHeatRemainder_contour_shift`
- `mandatory_proof_spine`: set `q=sqrt(t)*alpha` and
  `g(w)=exp(-w^2/4)*F(s+(sqrt(t)/2)*w)`; prove a uniform subgaussian bound for the actual `F`
  throughout the closed strip between the two source arguments; prove differentiability of `g`
  on each finite rectangle; send both vertical-side integrals to zero; pass both horizontal
  intervals to their Bochner integrals; remove `q.re` by Lebesgue translation; and finish by the
  exact identity `exp(-(Y+q)^2/4)=exp(-q^2/4)*exp(-Y*q/2)*exp(-Y^2/4)`
- `success_criterion`: both exact source endpoints compile for all stated parameters, with no
  contour-shift premise; exact `TargetChecks`, selected standard-only `#print axioms`, empty
  forbidden scans, full build, and public implementation/evidence CI pass
- `falsification_criterion`: the variance-two conversion gives any coefficient other than
  `-t*alpha^2/4`, `-sqrt(t)*Y*alpha/2`, or `t*alpha/2`; the strict same-half-plane condition does
  not keep the interpolation strip in the noninteger domain; or the existing growth estimates
  cannot be strengthened enough to make both finite vertical sides vanish
- `known_obstacle`: Loop 8 bounds one fixed horizontal line at a time. The contour proof needs one
  bound uniform over the whole compact imaginary strip. For `R_(0,N)` this requires a strip-uniform
  raw-contour bound and Gamma recurrence bound with a positive lower distance from the real-axis
  poles; pointwise horizontal integrability alone does not control the rectangle ends
- `nearest_prior_attempt`: Loop 5 proves a different one-pole contour shift for the raw
  Riemann--Siegel integration variable. Loop 8 proves actual heat-term integrability but performs
  no complex translation in the `s` variable
- `assumption_frontier_before`: exact `(htz)`, `(xio)`, the finite `R_(0,0)` decomposition,
  equation `(39)`, actual horizontal Gaussian integrability, and noninteger-domain holomorphy of
  `R_(0,N)` are public K0; no `(rtn-def)`, `(RTN-def)`, effective remainder estimate, or numerical
  certificate is assumed
- `anti_substitution_rule`: a generic contour theorem with growth and holomorphy hypotheses, a
  theorem that assumes either desired contour equality, a result only for real shifts, only for a
  special `alpha`/`beta`, only for `t=0`, or only for the combined equation `(39)` is not Loop 9
  success. A generic theorem may be used only when both actual source functions are instantiated
- `proper_prefix_rule`: if both endpoints do not compile, retain only a source-aligned uniform
  strip bound, finite rectangle identity, or vertical-side limit that removes a named dependency;
  record the first remaining obligation as `PARTIAL / BLOCKER_EXPOSED`
- `next_if_success`: use the two source contour shifts to attack the explicit term and remainder
  estimates in Polymath Propositions 6.1 and 6.3
- `next_if_blocked`: add the first failed strip-Gamma, raw-contour, rectangle-orientation,
  vertical-decay, or full-line-limit obligation to the H6-Q1 obstruction map and change the attack
  angle without pausing the global RH Goal

No Loop 9 proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 9 result

- `preregistration_evidence`: commit `9f42efc9c53c40ad6a8c001a3a9bced3a427290d` passed public CI
  run `29652764442`, build job `88101787571`
- `result`: `KNOWN_THEOREM_FORMALIZED`
- `compiled_endpoints`:
  `deBruijnNewmanRiemannSiegelHeatTerm_contour_shift` and
  `deBruijnNewmanRiemannSiegelHeatRemainder_contour_shift`
- `source_coverage`: arbitrary `t>0`, arbitrary complex `alpha`/`beta`/`s`, arbitrary natural
  `N`, positive natural `n`, and the exact strict same-open-half-plane condition for `s` and the
  translated endpoint
- `proof_spine`: uniform `1/64` raw-contour strip bound; uniform `1/128` Gamma bound away from
  real-axis integer poles; actual residue/remainder `3/128` strip bounds; Gaussian exponent
  `-29/128`; vanishing of both finite-rectangle vertical sides; finite Cauchy identity; Bochner
  limits on both horizontal sides; real translation; variance-two density conversion; exact
  completed-square algebra; instantiation to both actual source functions
- `assumption_frontier_after`: exact `(rtn-def)` and `(RTN-def)` are K0 and may be used as premises;
  no effective estimate, numerical certificate, finite-RH computation, or barrier winding premise
  is introduced
- `hard_gap_after`: explicit term/remainder estimates in Propositions 6.1 and 6.3, strict finite-sum
  certificates, finite RH through `3*10^12`, compact barrier winding, H6-E/G8, and RH remain open
- `hard_gap_delta`: 1
- `route_infrastructure_delta`: 1
- `verification`: exact Targets and TargetChecks pass; selected axiom prints are exactly
  `propext`, `Classical.choice`, and `Quot.sound`; forbidden scan and diff checks are clean; full
  `lake build` passes all 8,714 jobs
- `public_implementation_evidence`: commit `74946858f75e27b306cbf43042df74c447b18740`
  passed public CI run `29654348324`, build job `88105922988`, in `2m16s`
- `public_evidence_backfill`: commit `03ccacba97674a8adabf5e2f5b9b6f810539000e`
  passed public CI run `29654669529`, build job `88106762342`, in `1m35s`
- `next_exact_gate`: audit and preregister the source-exact quantitative endpoints of Polymath
  Propositions 6.1 and 6.3, then prove the term and remainder estimates without replacing them by
  an abstract asymptotic statement
- `global_goal`: active

## Loop 10 preregistration

- `mode`: `PROOF-ATTEMPT`
- `fixed_subedge`: Polymath Proposition 6.1, the effective estimate for the actual
  `r_(t,n)(sigma+iT)`; Proposition 6.3 is not bundled into this loop
- `primary_source`: D.H.J. Polymath arXiv `1904.12438v2`, `debruijn.tex` lines 621--678, with
  elementary Lemma 5.1(v) at lines 542--606 and the alpha derivative bound at lines 608--615
- `source_hashes`: archive SHA-256
  `1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863`; TeX SHA-256
  `560a28fe31bec92dd793820222e9e73a1fc6958a08344033a946b2ccaba225e5`
- `parameters`: arbitrary `sigma : R`, `T : R` with `10<T`, positive natural `n`, and real `t`
  with `0<t` and `t<=1/2`; put `s=sigma+i*T` and
  `alpha_n=deBruijnNewmanPolymathAlpha s-log n`
- `exact_error`:
  `epsilon=exp(((t^2/8)*norm(alpha_n)^2+t/4+1/6)/(T-333/100))-1`
- `proposed_Lean_endpoint`:
  `deBruijnNewmanRiemannSiegelHeatTerm_effective_estimate`
- `statement_shape`: there exists `e : C` with `norm e<=epsilon` such that the actual public
  `deBruijnNewmanRiemannSiegelHeatTerm t n s` equals
  `deBruijnNewmanPolymathM t s * b_n^t / n^(s+(t/2)*alpha(s)) * (1+e)`; the existential witness is
  the exact kernel-checkable meaning of the source's `1+O_<=(epsilon)`
- `relation_to_RH`: strict route infrastructure toward the effective `A+B-C` approximation and
  Table 1 final/barrier certificates; weaker than RH and not itself a zero-free theorem
- `success_criterion`: the exact endpoint compiles for all source parameters, with no assumed
  Stirling estimate, Taylor remainder, contour shift, or Gaussian perturbation; exact witness,
  standard-only axiom print, forbidden scan, full build, and public implementation/evidence CI pass
- `falsification_criterion`: the source bound fails under the project's exact Gamma/power branch
  normalization, the stated epsilon cannot dominate the rigorously derived remainder on the full
  source domain, or a source constant requires an omitted hypothesis
- `known_obstacles`: mathlib has no effective complex Stirling theorem. The source invokes Boyd to
  obtain Lemma 5.1(v), including `1/(12*(abs z-0.33))`; the project also lacks the upper-half-plane
  `log M_0` Taylor remainder, the exact `Im alpha_n>=-0.15` certificate, and the final parameterized
  Gaussian perturbation estimate
- `mandatory_milestones`: prove the upper-half-plane alpha derivative and bound; prove source
  Lemma 5.1(v) or the exact actual-function consequence
  `r_(0,n)=M_0*n^(-s)*exp(error)` with the displayed norm bound; prove the same-half-plane condition;
  prove the line-segment Taylor remainder; close the source Gaussian integral inequality
- `anti_substitution_rule`: an asymptotic `IsEquivalent`, a theorem with an assumed Gamma/Stirling
  error, an unspecified big-O constant, a special `sigma`/`n`/`t`, or a generic perturbation lemma
  without the actual heat term is not Loop 10 success
- `proper_prefix_rule`: if the final endpoint does not compile, retain only a source-exact theorem
  that removes one named Stirling, alpha, Taylor, or Gaussian obligation and classify the loop
  `PARTIAL / BLOCKER_EXPOSED`; helper count alone is not progress
- `selection_reason`: Proposition 6.1 directly supplies both finite-sum errors `e_A` and `e_B` and
  reuses public `(rtn-def)`. Proposition 6.3 additionally depends on the entirely absent Arias de
  Reyna Proposition 6.2 coefficient/remainder apparatus, so 6.1 has the shorter dependency path and
  creates shared quantitative infrastructure
- `next_if_success`: preregister Proposition 6.2/6.3's exact Arias de Reyna remainder edge, or if
  the aggregate consumer needs it first, compose Proposition 6.1 into the exact finite-sum
  `e_A/e_B` bound
- `next_if_blocked`: add the first failed Boyd/Stirling, branch, Taylor, or Gaussian constant to the
  H6-Q1 obstruction map and change the attack angle without pausing the global RH Goal

No Loop 10 proof source may be edited before this preregistration passes public Lean Action CI.

## Loop 10 local accounting

- `preregistration_gate`: commit `5a9d4ac09317314feba6e9d6482c2336ec941480` passed public Lean
  Action CI run `29655041718`, build job `88107737514`, in `1m40s`, before proof-source edits
- `classification`: `PARTIAL / BLOCKER_EXPOSED`
- `success_criterion_result`: failed; the actual
  `deBruijnNewmanRiemannSiegelHeatTerm_effective_estimate` endpoint does not compile because the
  Boyd effective `R_2` estimate has not been proved
- `compiled_alpha_prefix`: `deBruijnNewmanPolymathAlphaPrime_norm_le`,
  `deBruijnNewmanPolymathAlphaN_im_ge_neg_three_twentieths`,
  `deBruijnNewmanPolymathTerm_sameOpenHalfPlane`, and the uniform line-segment alpha-prime and
  alpha-difference bounds
- `compiled_taylor_prefix`: `deBruijnNewmanPolymathTerm_logM0_taylor_remainder_le` gives the exact
  source factor `norm(d)^2/(4*(T-3.08))`; the factor `1/2` is obtained from interval integration
- `compiled_term_prefix`: `deBruijnNewmanPolymathTermDisplacement_norm_sq_le` and
  `deBruijnNewmanPolymathTermMain_eq` identify the exact source displacement and central
  `M_t*b_n^t/n^(s+(t/2)*alpha(s))` factor
- `compiled_gaussian_prefix`: `integral_exp_sq_gaussianReal_two`,
  `inv_sqrt_one_sub_le_exp`, and `deBruijnNewmanPolymathTerm_gaussian_error_le` prove source
  equation `(ax)` with `T-3.33` in the project's variance-two normalization
- `compiled_stirling_reduction`: the actual Riemann--Siegel prefactor is
  `M_0(s)*exp(prefactorError(s))`; its ratio is exactly
  `Gamma(s/2)/GammaStirlingMain(s/2)`. Lean proves the complete conditional chain
  `norm R_2(z)<=0.0205/norm(z)^2 -> relative radius 1/(12*(norm(z)-0.246)) -> logarithmic radius
  1/(6*(norm(s)-0.66))`
- `first_open_obligation`: prove, on the source region needed at `z=s/2`,
  `norm (Gamma(z)/GammaStirlingMain(z)-1-1/(12*z)) <= (41/2000)/norm(z)^2`; this is the Boyd
  effective steepest-descent remainder, not a branch or elementary-arithmetic obligation
- `local_inventory_result`: Mathlib and the vendored Gamma files provide recurrence, integral,
  holomorphy, coarse strip bounds, and a digamma series, but no theorem with this effective
  `0.0205` remainder
- `assumption_frontier_after`: no theorem requiring the unproved `R_2` inequality is admitted as
  K0; only the unconditional prefix and explicit conditional reduction may be reused
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `local_mechanical_audit`: standalone module, production import, exact TargetChecks, ten selected
  axiom prints, forbidden-token scan, `git diff --check`, and the full 8,715-job build pass;
  selected declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`
- `public_implementation_evidence`: commit `814083d6c831c4ed18acaf291ce0d64b6199f1da` passed
  public Lean Action CI run `29657235672`, build job `88113679693`, in `2m4s`
- `public_evidence_backfill`: commit `d656c643194d0685c085f871b1d3c4a159d2f73e` passed public
  Lean Action CI run `29657362457`, build job `88114009920`, in `1m30s`
- `next_exact_gate`: Loop 11 must preregister and attack the displayed Boyd `R_2` inequality from
  an explicit integral or steepest-descent remainder representation; a theorem assuming that
  inequality, an asymptotic expansion without constants, or a real-axis-only bound is not success
- `global_goal`: active

## Loop 11 preregistration

- `mode`: `PROOF-ATTEMPT`
- `fixed_subedge`: Boyd's effective second Gamma/Stirling remainder used in Polymath Lemma 5.1(v)
- `primary_sources`: W. G. C. Boyd, *Gamma Function Asymptotics by an Extension of the Method of
  Steepest Descents*, Proc. R. Soc. A 447 (1994), 609--630, DOI
  `10.1098/rspa.1994.0158`, especially equations `(1.13)`, `(3.1)`, `(3.14)`, `(3.15)` as cited by
  Polymath; G. Nemes, arXiv `1310.0166`, for a modernized resurgence representation and error-bound
  cross-check
- `source_domain`: arbitrary `z : C` satisfying `1<=abs(Im z)` or `1<=Re z`; this is the exact
  domain of Polymath Lemma 5.1(v), not a positive-real-axis surrogate
- `fixed_definitions`: use the existing project
  `deBruijnNewmanPolymathGammaStirlingMain z` and
  `deBruijnNewmanPolymathGammaStirlingR2 z =
  Gamma(z)/GammaStirlingMain(z)-1-1/(12*z)` with Mathlib's `Complex.Gamma` and principal `cpow`
- `proposed_Lean_endpoint`:
  `deBruijnNewmanPolymathGammaStirlingR2_norm_le`
- `statement_shape`: for every source-domain `z`, prove
  `norm (deBruijnNewmanPolymathGammaStirlingR2 z) <=
  (41/2000)/norm(z)^2` without an analytic remainder premise
- `mandatory_milestones`: construct and prove the exact Boyd/Nemes remainder representation in
  project normalization; prove absolute integrability and branch agreement; obtain the
  `(2*sqrt(2)+1)*C_2*Gamma(2)/(2*pi)^3` right-half-plane bound; obtain the corresponding
  left-half-plane bound with `norm(1-exp(2*pi*i*z))` in the denominator; prove its
  `1-exp(-2*pi)` lower bound when `Im z>=1`; use Gamma conjugation for `Im z<=-1`; and close the
  rational `41/2000` constant comparison in Lean
- `success_criterion`: the exact full-domain endpoint compiles, the Loop 10 source-form
  prefactor-error theorem becomes unconditional on the Lemma 5.1(v) domain, exact witnesses and
  standard-only axiom prints pass, scans and full build pass, and implementation/evidence commits
  pass public CI
- `falsification_criterion`: Boyd's cited representation does not match the project's principal
  complex power, requires an omitted sector or pole-avoidance hypothesis, the left-half-plane
  denominator estimate fails on the registered domain, or the explicit constant does not prove
  `41/2000`
- `anti_substitution_rule`: no theorem may assume the displayed `R_2` inequality, an equivalent
  relative Gamma error, or a prepackaged effective Stirling bound; an asymptotic `O`, a new Gamma
  definition, an abstract remainder predicate, a numerical sample, or a positive-real-only theorem
  is not Loop 11 success
- `proper_prefix_rule`: if the endpoint does not compile, retain only a source-exact theorem that
  removes one named representation, integrability, sector, denominator, conjugation, or constant
  obligation and record the first remaining one as `PARTIAL / BLOCKER_EXPOSED`
- `selection_reason`: Loop 10 reduced the entire Proposition 6.1 chain to this one first analytic
  obligation; proving it immediately activates the already compiled `0.0205 -> 0.246 -> 0.33`
  conversion and actual Riemann--Siegel prefactor bound
- `next_if_success`: compose the unconditional base-term error, public contour shift, Taylor bound,
  displacement estimate, and Gaussian `(ax)` into the full Proposition 6.1 witness
- `next_if_blocked`: log the exact failed Boyd representation or sector bound, then compare the
  Nemes integral representation or derive Binet's formula directly; the global RH Goal remains
  active

No Loop 11 proof source may be edited before this preregistration passes public Lean Action CI.

Preregistration commit `14bdc45fa1a0e70a26e00e57b4bc8325d73d8ad5` passed public Lean Action CI
run `29657566566`, build job `88114535307`, in `2m10s`. Loop 11 proof-source work is admitted.

## Loop 11 local result

- `classification`: `PARTIAL / BLOCKER_EXPOSED`
- `source_audit`: Nemes arXiv `1310.0166` TeX SHA-256
  `2ed05322fda9c874cc2f83e67ba1e5e59ef6bb342866eb112be05f943aec34d8`; equations `(15)`,
  `(28)` and Lemma 2/Theorem 3 were checked against the implementation.
- `compiled_prefix`: project-normalized scaled-Gamma conjugation and continuation; exact
  imaginary-axis norm square and reciprocal boundary bound; differentiability in the open right
  half-plane; continuity-on-closure reduction to the origin; mathlib Phragmen--Lindelof application
  conditional only on origin continuity, subquadratic exponential growth, and eventual positive-real
  boundedness; mirror-ray/Stokes transfer; `399/400` denominator separation; and the exact Boyd
  majorant `<41/2000`.
- `anti_substitution_audit`: no theorem assumes the target `R_2` bound, an equivalent effective
  Stirling estimate, an unspecified big O, or a replacement Gamma function.
- `first_remaining_edge`: prove Boyd/Nemes equation `(15)` as an absolutely integrable identity for
  the actual `deBruijnNewmanPolymathGammaStirlingR2`, then justify the rotated contour used in
  Theorem 3. The ray subproof additionally needs Stieltjes equation `(13)` to discharge the three
  reciprocal scaled-Gamma growth interfaces.
- `mechanical_audit`: standalone, exact TargetChecks, selected axiom prints, forbidden scan,
  `git diff --check`, and the 8,716-job full build pass. Selected declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `public_state`: implementation commit `3409b7175eb24f1e0f01377795334a08e5f80384` passed public
  Lean Action CI run `29659089400`, build job `88118485517`, in `2m19s`; this accounting update is
  the Loop 11 closure evidence. H6-Q1 and the persistent RH Goal remain active.

## Loop 12 preregistration

- `campaign`: `PROOF-ATTEMPT-20260719-H6-BOYD-R2-EQ15-01`
- `mode`: `PROOF-ATTEMPT`
- `fixed_subedge`: the `N=2` Boyd/Nemes equation `(15)` integral representation for the actual
  project `deBruijnNewmanPolymathGammaStirlingR2` on `Re z > 0`, including absolute integrability
  of both kernels.
- `proposed_Lean_endpoint`:
  `deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_integrals`
- `success_criterion`: both source kernels are Bochner integrable on `Ioi 0`, the exact equality
  compiles for every `0<z.re`, and exact checks, standard-only axiom audit, full build, and public
  implementation/evidence CI pass.
- `falsification_criterion`: branch, coefficient, sign, sector, endpoint-integrability, or contour
  alignment fails against the project definitions.
- `assumption_frontier_before`: all Loop 11 scaled-Gamma branch/boundary/Stokes/constant results are
  public K0; equation `(15)` and every effective `R2` estimate remain absent.
- `known_obstacles`: neither mathlib nor the project packages Binet/Stieltjes or Boyd resurgence;
  Nemes states equation `(15)` by citation to Boyd.
- `nearest_primary_source`: Nemes arXiv `1310.0166`, equation `(15)`, cross-checked with Boyd 1994.
- `nearest_project_attempt`: Loop 11 compiled the exact imaginary-axis scaled-Gamma norm and the
  downstream reflection/Stokes chain but did not connect `R2` to an integral.
- `new_attack_angle`: specialize to `N=2`, retain the source two-integral signs, prove kernel
  integrability from the compiled imaginary-axis norm, derive the positive-real identity from the
  Euler Gamma integral/contour decomposition, and extend holomorphically to `Re z>0`.
- `anti_substitution_rule`: equation `(15)`, the target remainder bound, equivalent effective
  Stirling estimates, abstract remainders, replacement Gamma functions, and unspecified big O are
  forbidden as premises.
- `full_preregistration`: `research/h6_boyd_r2_loop12_prereg_20260719.md`.
- `prior_public_evidence`: Loop 11 closure-evidence commit
  `ee6a6fcd1130203ec84ee4450b952277e9290db4` passed public CI run `29659211122`, build job
  `88118794823`, in `1m35s`.

No Loop 12 proof source may be edited before this preregistration passes public Lean Action CI.

Preregistration commit `00be4a5bfa3c614482aa4374a177fa73fa3bd131` passed public Lean Action CI
run `29659498616`, build job `88119559667`, in `1m31s`. Loop 12 proof-source work is admitted.

## Loop 12 local result

- `classification`: `PARTIAL / BLOCKER_EXPOSED`
- `compiled_module`: `LeanLab/Riemann/DeBruijnNewmanPolymathBoydR2Integral.lean` (453 lines)
- `success_criterion_part_1`: passed. For every `0<z.re`, both actual source kernels are Bochner
  integrable on `Ioi 0` in
  `deBruijnNewmanPolymathBoydR2_integrableOn`.
- `compiled_prefix`: exact denominator quotient identities, right-half-plane lower bounds and
  bounded inverses; scaled-Gamma differentiability on the slit plane; continuity of both
  imaginary rays; exact positive-ray weight norm square; the global elementary bound
  `|s*exp(-2*pi*s)*GammaStar(i*s)| <= sqrt(s)*exp(-pi*s)`; positive/negative-ray integrability;
  the source-exact two-integral RHS and its algebraic normalization; pointwise and integral
  conjugacy on the positive real axis; and reduction of the Boyd RHS to one integral imaginary
  part there.
- `success_criterion_part_2`: open. No theorem proves
  `deBruijnNewmanPolymathGammaStirlingR2 z = deBruijnNewmanPolymathBoydR2Integral z`.
- `first_failed_obligation`: Nemes explicitly introduces equation `(15)` as Boyd's resurgence
  formula by citation. Euler's Gamma integral does not by itself provide the required global
  saddle-coordinate inverse/Cauchy decomposition across the adjacent `2*pi*i` saddle images.
  Mathlib and the project contain no Boyd resurgence, Binet/Stieltjes remainder, or equivalent
  bridge. The representation was therefore recorded only as
  `deBruijnNewmanPolymathBoydR2RepresentationAt`, never assumed.
- `anti_substitution_audit`: equation `(15)`, the target `R2` estimate, an equivalent effective
  Stirling theorem, unspecified asymptotics, and replacement Gamma functions are absent from all
  premises.
- `hard_gap_delta`: 0
- `route_infrastructure_delta`: 1
- `local_mechanical_audit`: standalone module, exact Targets and three new TargetChecks pass;
  selected axiom prints use only `propext`, `Classical.choice`, and `Quot.sound`; forbidden scan is
  empty; `git diff --check` and the full 8,717-job build pass. Public-CI evidence is recorded after
  the implementation commit.
- `next_exact_gate`: preregister the positive-real saddle integral
  `GammaStar(x)=sqrt(x/(2*pi))*integral_R exp(-x*(exp(u)-u-1)) du` for `x>0`, derived from Euler's
  Gamma integral by the exact substitution `t=x*exp(u)`. This is the first source-faithful Boyd
  steepest-descent input and introduces no equation `(15)` premise.
- `global_goal`: H6-Q1 and the persistent RH Goal remain active.
- `public_implementation`: commit `75d39360af35c3fc65ef357b3e4d1aa498c32602` passed public
  Lean Action CI run `29660452525`, build job `88122109932`, in `2m17s`.

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
