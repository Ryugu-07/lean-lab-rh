# H6 Polymath Table-Row Certificates Attempt Log

Campaign: `LITERATURE-20260718-H6-POLYMATH-TABLE-ROW-CERTIFICATES-01`

Status: `ACTIVE_LOOP_3_PUBLIC_IMPLEMENTATION_VERIFIED_EVIDENCE_PENDING`

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
- immutable evidence-backfill CI: pending

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
