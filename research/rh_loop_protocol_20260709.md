# RH Loop Protocol v2

Date: 2026-07-10

Sources:

- `/Users/karasuakamatsu/Downloads/rh_loop_protocol_v2_20260710.md`
- `/Users/karasuakamatsu/.codex/attachments/fb68cde6-ceb8-4986-9180-fbceb69fae28/pasted-text.txt`
- Historical v1 source:
  `/Users/karasuakamatsu/Downloads/review_rh_loop_goal_20260709.md`

This v2 section replaces the operating rules from v1. The historical loop updates below remain as
chronology, not as authority for choosing future proof targets.

## Operational Goal

Advance auditable RH research in `/Users/karasuakamatsu/lean-lab`.

New local Lean lemmas, rewrite lemmas, predicate wrappers, finite-sum transports, and closing
self-created ledger nodes do not count as RH research progress by themselves. Lean verifies
correctness. Research progress is defined only by reduction of a fixed external hard gap.

Fixed milestones:

- M0 Statement Alignment: compare the project-local Nyman-Beurling/Baez-Duarte predicates with
  published classical criteria. Prove exact equivalence item by item, or record each mismatch.
- M1 Known Criterion Formalization: after M0, formalize one accurately cited published
  Nyman-Beurling or Baez-Duarte criterion as a Lean equivalence with `Mathlib.RiemannHypothesis`.
- M2 Discovery: count direct RH progress only for an unconditional proof of such a criterion, an
  explicit approximating family with error tending to zero, or a literature-audited new structural
  lemma.

All future work must target a pre-existing node in `research/hard_gap_dag.md`. The model must not
create a local successor node merely to make the next loop executable. Mechanical lemmas are batched.

## Work Classes

Each loop or engineering batch has exactly one tag:

- FORMALIZATION: formalizes known mathematics, infrastructure, bridges, or batched transports.
- DISCOVERY: attempts a new structural lemma, constant, or error bound; requires the novelty audit
  below.
- RH_PROGRESS: not the default; allowed only when `research/hard_gap_dag.md` changes a hard-gap
  status and an auditor confirms the delta.

## Result Classes

Each loop result is exactly one of:

- HARD_GAP_REDUCED
- KNOWN_THEOREM_FORMALIZED
- BRANCH_FALSIFIED
- DEPENDENCY_GAP_IDENTIFIED
- FORMALIZATION_ONLY
- NO_PROGRESS

If `hard_gap_delta = 0`, the result cannot be `HARD_GAP_REDUCED`.

## Fixed-Gap Entry Rule

Before starting a loop, record:

- `node_id`
- `work_class`
- exact mathematical statement
- exact Lean statement, when applicable
- published source or novelty rationale
- `assumption_frontier_before`
- `hard_gap_before`
- expected `hard_gap_delta`
- why the work is not a mechanical batch item

Reject a standalone loop when the proposed work only composes proved implications, only renames or
repackages a predicate, keeps the same unproved assumption frontier, is a one-step corollary in the
same edge, or targets a node created by the immediately previous loop.

## Stop Rules

Stop or pivot before another proof loop when any of these occurs:

- three consecutive loops have `hard_gap_delta = 0`;
- five loops keep the same unproved assumption frontier;
- two loops repeat the same strategy;
- the next target is only a mechanical corollary;
- compaction/summary occurred and the fixed DAG has not been re-audited from source files;
- no published source or novelty rationale is available.

Every five accepted loops, a clean-context audit must decide one of `CONTINUE`, `PIVOT`, `BATCH`,
or `STOP`.

## Batching Rule

Definitions, iff rewrites, finite-support transports, norm/integral rewrites, predicate wrappers,
and one-step corollaries on the same edge must be grouped into one engineering batch whenever
possible. The planned loop-131 corollary is a mechanical batch item, not a standalone research
loop.

## Target Ledger Hardening

- Use double-backtick Lean identifiers in `LeanLab/Riemann/Targets.lean`, so missing names fail
  elaboration.
- Keep `LeanLab/Riemann/TargetChecks.lean` in the build. It must typecheck every `.proven` target
  that has a `leanName`; exact statement witnesses should be expanded in engineering batches.
- New target nodes need external-source or auditor sign-off before they can count as research
  progress.

## Future Attempt Record Fields

Each future loop or batch record must include:

- `loop_id`
- `node_id`
- `work_class`
- `result_class`
- `assumption_frontier_before`
- `assumption_frontier_after`
- `hard_gap_before`
- `hard_gap_after`
- `hard_gap_delta`
- Lean verification commands and results
- theorem names
- nearest known literature
- model
- reasoning effort
- budget
- compaction state
- commit SHA

## Novelty Audit

Claims of possible first formalization or candidate new mathematics require a note comparing the
claim against mathlib, Isabelle AFP, relevant external Lean repositories, and arXiv. A local mathlib
miss is not evidence of novelty.

## Historical Loop Updates

## M0 Audit 2026-07-10-01

Clean-context audit `AUDIT-20260710-M0-01` targeted fixed node M0 and proved
`nymanBeurlingConcreteApprox_unconditional`. Arbitrary signed parameters make the unrestricted
predicate unconditional because the kernels at `1` and `-1` sum to one almost everywhere. The
result class is `BRANCH_FALSIFIED`, the unrestricted criterion branch is rejected, and the audit
decision is `PIVOT` to exact restricted-statement alignment. See
`research/m0_statement_alignment_20260710.md`.

## M0 Batch 2026-07-10-02

Batch `BATCH-20260710-M0-02` proved the exact equivalence between the project restricted closure
membership and `nymanBeurlingRestrictedConcreteApprox`. A primary-source audit then found that
Beurling's unit-interval criterion requires `sum c_k * theta_k = 0`, which the project predicate
omits. Lean proved that the omitted Baez-Duarte `(1, infinity)` tail is exactly the square of this
coefficient-parameter moment. The result class is `DEPENDENCY_GAP_IDENTIFIED`, and the decision is
`PIVOT` to a published positive-natural finite-error statement with the moment/tail term restored.
See `research/m0_restricted_closure_alignment_20260710.md`.

## M0 Batch 2026-07-10-03

Batch `BATCH-20260710-M0-03` restored the missing tail in a separate source-faithful
positive-natural predicate. `baezDuarteSplitFullLineError` keeps the `(0,1)` constant-one error and
the `(1, infinity)` zero-target tail as separate integrals; Lean proves its normalized form is local
error plus squared reciprocal moment. `nymanBeurlingBaezDuarteFullLineConcreteApprox` is the only
current natural predicate eligible for later M1 work. The result is `FORMALIZATION_ONLY`; the
Baez-Duarte equivalence with RH remains open. See
`research/m0_baez_duarte_full_line_alignment_20260710.md`.

## M0 Batch 2026-07-10-04

Batch `BATCH-20260710-M0-04` packages `chi_(0,1]` and every positive-natural reciprocal kernel in
the actual real `Lp Real 2 (volume.restrict (Set.Ioi 0))` space. Lean proves that the whole-space
norm error equals `baezDuarteSplitFullLineError`, including the null-endpoint bridge, and proves
`baezDuarteTargetL2_mem_closure_iff_fullLineConcreteApprox`. The result is
`FORMALIZATION_ONLY`; M1/G1 and RH remain open. M0 next permits only the bounded coefficient-field
and source-convention audit. See `research/m0_baez_duarte_l2_closure_alignment_20260710.md`.

## M0 Batch 2026-07-10-05

Batch `BATCH-20260710-M0-05` inspected the primary Baez-Duarte paper and closed the remaining
coefficient-field ambiguity. Lean proves `baezDuarteKernel_source_formula`, packages the complex
positive-half-line `Lp` target and natural-kernel closure, and proves both
`baezDuarteComplexTarget_mem_closure_iff_real` and
`baezDuarteComplexTarget_mem_closure_iff_fullLineConcreteApprox`. A requirement-by-requirement
audit found no remaining statement mismatch, so M0 is complete and the result is
`HARD_GAP_REDUCED`. This does not prove the published RH equivalence; M1/G1 now begins from the
eligible complex closure side. See `research/m0_completion_audit_20260710.md`.

## M1 Audit 2026-07-10-01

Audit `AUDIT-20260710-M1-01` starts fixed node M1/G2 without adding an RH-equivalence wrapper. Lean
proves `RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re`, which supplies the zero-free
half-plane premise in Baez-Duarte's quoted Balazard-Saias lemma. The pinned mathlib tree has complex
Mellin transforms, pointwise Mellin/Fourier conversion, Fourier `L2` Plancherel, and Mobius L-series
inversion only for `re(s) > 1`. It lacks the RH-conditional quantitative Mobius estimate near the
critical line and the base Nyman-Beurling/Hardy-space criterion needed for the reverse direction.
The result is `DEPENDENCY_GAP_IDENTIFIED`, not G1 or RH progress. See
`research/m1_baez_duarte_dependency_audit_20260710.md`.

## Loop 86 Update

The Li/Hadamard inventory is complete as
`research/tier2_li_hadamard_inventory_20260709.md`. It found strong local analytic and divisor
infrastructure, but not the global product, zero-enumeration, or coefficient-to-zero-sum bridge
needed for a direct structural route. The next loop should inspect Nyman-Beurling/Báez-Duarte
support before choosing `T2.pivot`.

## Loop 87 Update

The Nyman-Beurling/Baez-Duarte inventory is complete as
`research/tier2_nyman_beurling_inventory_20260709.md`. It found no ready criterion statement, but
it did find enough `L2`, indicator, density, interval-measure, fractional-part, and Hilbert-subspace
closure infrastructure to make the first missing nodes small. The next loop should close
`T2.pivot` by choosing the Nyman-Beurling foundation route.

## Loop 88 Update

`T2.pivot` is closed: the sustained Tier 2 direction is now the Nyman-Beurling foundation route.
The first compiled foundation theorem is in `LeanLab.Riemann.NymanBeurling`: for every real `a`,
`fractionalPartKernel a = fun x => Int.fract (a / x)` belongs to `L2` on `(0,1)`. The next loop
should fill `T2.nyman.span.scaffold` by defining the real submodule generated by the packaged
`L2` kernels and proving the generator membership lemma.

## Loop 89 Update

`T2.nyman.span.scaffold` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`unitIntervalL2`, `nymanBeurlingKernelSpan`, proves every packaged fractional-part kernel belongs
to that span, and records the span's minimality property. The next loop should fill
`T2.nyman.closure.scaffold` by defining the topological closure of this span and proving the basic
span-to-closure inclusion.

## Loop 90 Update

`T2.nyman.closure.scaffold` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`nymanBeurlingKernelClosure`, proves `nymanBeurlingKernelSpan ≤ nymanBeurlingKernelClosure`,
records closedness, relates the submodule closure to `Set.closure`, and proves each packaged
fractional-part kernel belongs to the closure. The next loop should fill
`T2.nyman.density.predicate` by packaging the Hilbert-space density statement without claiming any
criterion bridge.

## Loop 91 Update

`T2.nyman.density.predicate` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`nymanBeurlingKernelDense` as density of the kernel span and proves it is equivalent to
`nymanBeurlingKernelClosure = ⊤`, and also to every `L²(0,1)` element lying in the kernel-span
closure. The next loop should fill `T2.nyman.orthogonal.reformulation`, still staying on the
Hilbert-space side.

## Loop 92 Update

`T2.nyman.orthogonal.reformulation` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`nymanBeurlingKernelDense_iff_orthogonal_eq_bot`, using the local closure-density bridge together
with mathlib's Hilbert-space theorem that a submodule has dense closure exactly when its orthogonal
complement is bottom. The next loop should fill `T2.nyman.orthogonal.pointwise` by unpacking
membership in the orthogonal complement into vanishing inner products against every packaged kernel.

## Loop 93 Update

`T2.nyman.orthogonal.pointwise` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`mem_nymanBeurlingKernelSpan_orthogonal_iff`: a vector lies in the orthogonal complement of the
kernel span exactly when its inner product with every packaged fractional-part kernel vanishes. The
next loop should fill `T2.nyman.density.pointwise` by combining this pointwise theorem with the
orthogonal-bottom reformulation of density.

## Loop 94 Update

`T2.nyman.density.pointwise` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero`: kernel-span density is equivalent
to every `L²(0,1)` vector with zero inner product against every packaged fractional-part kernel
being zero. Because this closes the current Hilbert-space rewrite chain, the next loop should avoid
another pure equivalence rewrite and instead fill `T2.nyman.inner.integral.inventory`, a bounded
inventory of `Lp` inner-product-to-integral API.

## Loop 95 Update

`T2.nyman.inner.integral.inventory` is closed. The inventory is recorded as
`research/tier2_nyman_inner_integral_inventory_20260710.md`, and
`LeanLab.Riemann.NymanBeurling` now proves `inner_fractionalPartKernelL2_eq_integral`, rewriting
the inner product against a packaged fractional-part kernel as the integral of
`fractionalPartKernel a x * f x` over the restricted unit interval. The next loop should fill
`T2.nyman.density.integral` by substituting this integral formula into the density obstruction
statement.

## Loop 96 Update

`T2.nyman.density.integral` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero`, reformulating kernel-span
density as the statement that every `L²(0,1)` vector whose integrals against all concrete
fractional-part kernels vanish is zero. The next loop should fill `T2.nyman.constant.one.l2` by
packaging the constant-one function in the same `L²(0,1)` space.

## Loop 97 Update

`T2.nyman.constant.one.l2` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`unitIntervalOne`, proves `unitIntervalOne_memLp_two_unitInterval`, packages it as
`unitIntervalOneL2`, and proves `unitIntervalOneL2_coeFn` plus the constant representative theorem
`unitIntervalOneL2_coeFn_const`. The next loop should fill
`T2.nyman.density.one.closure` by deriving the conditional membership
`unitIntervalOneL2 ∈ nymanBeurlingKernelClosure` from `nymanBeurlingKernelDense`.

## Loop 98 Update

`T2.nyman.density.one.closure` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense`, deriving the constant-one closure
membership from the pointwise closure form of `nymanBeurlingKernelDense`. The next loop should fill
`T2.nyman.one.closure.epsilon` by turning this closure membership into an epsilon-distance
approximation statement with approximants in `nymanBeurlingKernelSpan`.

## Loop 99 Update

`T2.nyman.one.closure.epsilon` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt` using `Metric.mem_closure_iff`, and the
density-conditioned corollary `exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense`.
The next loop should fill `T2.nyman.span.finite.approx` by unpacking abstract membership in
`nymanBeurlingKernelSpan` into finite real linear combinations of packaged fractional-part kernels.

## Loop 100 Update

`T2.nyman.span.finite.approx` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum`,
`unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt`, and
`exists_finsupp_sum_fractionalPartKernelL2_dist_unitIntervalOneL2_lt_of_dense`, using
`Finsupp.mem_span_range_iff_exists_finsupp` to unpack span membership into finite kernel
combinations. The next loop should fill `T2.nyman.finite.approx.norm` by rewriting the finite
approximation distance as a norm of a difference.

## Loop 101 Update

`T2.nyman.finite.approx.norm` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt` and
`exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`, using `dist_eq_norm` to rewrite
the finite-combination approximation in norm form. The next loop should fill
`T2.nyman.finite.approx.integral.inventory` by inventorying `L²` norm-square-to-integral support.

## Loop 102 Update

`T2.nyman.finite.approx.integral.inventory` is closed. The inventory is recorded as
`research/tier2_nyman_finite_approx_integral_inventory_20260710.md`. `LeanLab.Riemann.NymanBeurling`
now proves `unitIntervalL2_norm_sq_eq_integral_mul_self` and
`norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self`, using
`norm_sq_eq_re_inner` and `L2.inner_def`. The next loop should fill
`T2.nyman.finite.approx.representatives` by identifying finite kernel combinations with their
concrete pointwise representatives almost everywhere.

## Loop 103 Update

`T2.nyman.finite.approx.representatives` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`finsupp_sum_fractionalPartKernelL2_coeFn` and
`unitIntervalOneL2_sub_finsupp_sum_fractionalPartKernelL2_coeFn`, using `Lp.coeFn_smul`,
`Lp.coeFn_sub`, `Lp.coeFn_fun_finsetSum`, and `eventuallyEq_sum` to identify finite packaged
kernel combinations and the constant-one difference with their concrete pointwise representatives
almost everywhere. The loop also proves
`norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete`, rewriting the norm-square
integral as the concrete squared-error integral. The next loop should fill
`T2.nyman.finite.approx.integral.epsilon` by deriving an `ε ^ 2` concrete integral bound from the
density-conditioned norm approximation.

## Loop 104 Update

`T2.nyman.finite.approx.integral.epsilon` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense`, deriving a finite
coefficient family whose concrete squared-error integral is below `ε ^ 2` from
`nymanBeurlingKernelDense` and `0 < ε`. The proof combines
`exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense`,
`norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete`, and `sq_lt_sq₀`. The next
loop should fill `T2.nyman.finite.approx.integral.tolerance` by replacing the squared tolerance
with an arbitrary positive tolerance, likely via `Real.sqrt`.

## Loop 105 Update

`T2.nyman.finite.approx.integral.tolerance` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance`, instantiating
the `ε ^ 2` theorem with `Real.sqrt δ` and simplifying with `Real.sq_sqrt`. The next loop should
fill `T2.nyman.concrete.approx.predicate` by packaging the positive-tolerance integral
approximation as a short reusable project-local predicate and proving that
`nymanBeurlingKernelDense` implies it.

## Loop 106 Update

`T2.nyman.concrete.approx.predicate` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`nymanBeurlingConcreteApprox`, the project-local concrete finite-approximation predicate, and
proves `nymanBeurlingConcreteApprox_of_dense`. The next loop should fill
`T2.nyman.classical.criterion.inventory` by comparing this predicate with the classical
Nyman-Beurling/Baez-Duarte criterion and recording the exact formal gaps before attempting any RH
bridge.

## Loop 107 Update

`T2.nyman.classical.criterion.inventory` is closed. The inventory is recorded as
`research/tier2_nyman_classical_criterion_inventory_20260710.md`. It compares
`nymanBeurlingConcreteApprox` with the classical Nyman-Beurling/Baez-Duarte statement shapes and
records five formal gaps: real versus restricted unit-interval parameters, natural-parameter
strengthening, unit-interval versus half-line target functions, closure-style criteria versus the
project's integral-tolerance predicate, and the missing criterion-to-`RiemannHypothesis` bridge.
The next loop should fill `T2.nyman.restricted.concrete.approx.predicate` by defining a restricted
support version of the concrete approximation predicate and proving it implies
`nymanBeurlingConcreteApprox`.

## Loop 108 Update

`T2.nyman.restricted.concrete.approx.predicate` is closed. `LeanLab.Riemann.NymanBeurling` now
defines `nymanBeurlingRestrictedConcreteApprox`, requiring the finite coefficient support to lie
in `0 < a ∧ a ≤ 1`, and proves `nymanBeurlingConcreteApprox_of_restricted`. The theorem reuses
the same finite coefficient family and discards only the support condition, so it introduces no
new analytic premise. The next loop should fill `T2.nyman.restricted.span.scaffold` by defining
the submodule generated by the restricted kernel family and proving it is contained in
`nymanBeurlingKernelSpan`.

## Loop 109 Update

`T2.nyman.restricted.span.scaffold` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`nymanBeurlingRestrictedParameterSet`, `nymanBeurlingRestrictedKernelSet`, and
`nymanBeurlingRestrictedKernelSpan`. It also proves restricted generator membership through
`fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSet` and
`fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSpan`, plus the structural inclusion
`nymanBeurlingRestrictedKernelSpan_le`. The next loop should fill
`T2.nyman.restricted.closure.scaffold` by defining the restricted closure and relating it to
`nymanBeurlingKernelClosure`.

## Loop 110 Update

`T2.nyman.restricted.closure.scaffold` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`nymanBeurlingRestrictedKernelClosure` and proves `nymanBeurlingRestrictedKernelSpan_le_closure`,
`isClosed_nymanBeurlingRestrictedKernelClosure`, `nymanBeurlingRestrictedKernelClosure_coe`,
`nymanBeurlingRestrictedKernelClosure_le`, and
`fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelClosure`. The key structural bridge is
that the restricted closure is contained in `nymanBeurlingKernelClosure`. The next loop should
fill `T2.nyman.restricted.density.predicate` by packaging density of the restricted span and
proving its basic closure forms.

## Loop 111 Update

`T2.nyman.restricted.density.predicate` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`nymanBeurlingRestrictedKernelDense` as density of `nymanBeurlingRestrictedKernelSpan`, and proves
`nymanBeurlingRestrictedKernelDense_iff_closure_eq_top` plus
`nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`. This mirrors the earlier unrestricted
density predicate without claiming that the restricted density hypothesis is true. The next loop
should fill `T2.nyman.restricted.density.implies.unrestricted` by proving restricted density
implies `nymanBeurlingKernelDense`.

## Loop 112 Update

`T2.nyman.restricted.density.implies.unrestricted` is closed.
`LeanLab.Riemann.NymanBeurling` now proves `nymanBeurlingKernelDense_of_restricted`, deriving the
existing unrestricted density predicate from `nymanBeurlingRestrictedKernelDense`. The proof uses
`nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure`,
`nymanBeurlingKernelDense_iff_forall_mem_closure`, and
`nymanBeurlingRestrictedKernelClosure_le`. The next loop should fill
`T2.nyman.restricted.density.concrete.approx` by composing this bridge with
`nymanBeurlingConcreteApprox_of_dense`.

## Loop 113 Update

`T2.nyman.restricted.density.concrete.approx` is closed.
`LeanLab.Riemann.NymanBeurling` now proves
`nymanBeurlingConcreteApprox_of_restrictedKernelDense`, deriving the existing concrete
approximation predicate from `nymanBeurlingRestrictedKernelDense`. This is an unrestricted
concrete approximation bridge; the restricted-support concrete statement still needs a separate
restricted closure-to-finite-sum chain. The next loop should fill
`T2.nyman.restricted.density.one.closure` by proving that restricted density places
`unitIntervalOneL2` in `nymanBeurlingRestrictedKernelClosure`.

## Loop 114 Update

`T2.nyman.restricted.density.one.closure` is closed.
`LeanLab.Riemann.NymanBeurling` now proves
`unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense`, by instantiating
`nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure` at `unitIntervalOneL2`. The next loop
should fill `T2.nyman.restricted.one.closure.epsilon`, the restricted analogue of the existing
closure-to-epsilon approximation theorem.

## Loop 115 Update

`T2.nyman.restricted.one.closure.epsilon` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt`, converting restricted closure
membership of `unitIntervalOneL2` into epsilon-distance approximation by elements of
`nymanBeurlingRestrictedKernelSpan`. It also proves
`exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense`. The next
loop should fill `T2.nyman.restricted.span.finite.approx` by unpacking restricted-span membership
into finite sums indexed by restricted parameters.

## Loop 116 Update

`T2.nyman.restricted.span.finite.approx` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`restrictedFractionalPartKernelL2`, proves `nymanBeurlingRestrictedKernelSet_eq_range`, and proves
`mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum`, unpacking restricted-span
membership into finite real linear combinations indexed by `nymanBeurlingRestrictedParameterSet`.
The next loop should fill `T2.nyman.restricted.finite.approx.dist` by combining this finite-sum
unpacking with the restricted epsilon approximant theorem.

## Loop 117 Update

`T2.nyman.restricted.finite.approx.dist` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense`,
which derives a subtype-indexed finite coefficient family over restricted parameters whose
packaged finite sum is within any positive tolerance of `unitIntervalOneL2`. The next loop should
fill `T2.nyman.restricted.finite.approx.norm` by rewriting the distance inequality as a norm
inequality.

## Loop 118 Update

`T2.nyman.restricted.finite.approx.norm` is closed. `LeanLab.Riemann.NymanBeurling` now proves
`exists_restricted_finsupp_sum_norm_sub_lt_of_dense`, which rewrites the subtype-indexed
restricted finite-sum approximation from distance form to the norm of
`unitIntervalOneL2` minus the packaged finite combination. The next loop should fill
`T2.nyman.restricted.finite.approx.integral.inventory` by checking reuse of the existing
norm-square-to-integral bridge for restricted finite sums.

## Loop 119 Update

`T2.nyman.restricted.finite.approx.integral.inventory` is closed. The inventory is recorded as
`research/tier2_nyman_restricted_finite_approx_integral_inventory_20260710.md`, and
`LeanLab.Riemann.NymanBeurling` now proves
`norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self`. This shows the generic `unitIntervalL2`
norm-square-to-integral bridge applies directly to subtype-indexed restricted finite sums. The next
loop should fill `T2.nyman.restricted.finite.approx.representatives` by identifying the restricted
finite-sum representative with the corresponding concrete fractional-part finite sum.

## Loop 120 Update

`T2.nyman.restricted.finite.approx.representatives` is closed. `LeanLab.Riemann.NymanBeurling`
now proves `restricted_finsupp_sum_fractionalPartKernelL2_coeFn`,
`unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn`, and
`norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete`. This identifies subtype-indexed
restricted finite sums and their difference from `unitIntervalOneL2` with concrete
fractional-part representatives, then rewrites the restricted norm-square integral as a concrete
squared-error integral. The next loop should fill
`T2.nyman.restricted.finite.approx.integral.epsilon`.

## Loop 121 Update

`T2.nyman.restricted.finite.approx.integral.epsilon` is closed.
`LeanLab.Riemann.NymanBeurling` now proves
`exists_restricted_finsupp_integral_sq_lt_of_dense`, combining the restricted finite-sum norm
approximation, the concrete norm-square integral theorem, and `sq_lt_sq₀`. The next loop should
fill `T2.nyman.restricted.finite.approx.integral.tolerance` by replacing the squared tolerance
with an arbitrary positive tolerance via `Real.sqrt`.

## Loop 122 Update

`T2.nyman.restricted.finite.approx.integral.tolerance` is closed.
`LeanLab.Riemann.NymanBeurling` now proves
`exists_restricted_finsupp_integral_lt_of_dense_tolerance`, instantiating the restricted
epsilon-square theorem with `Real.sqrt δ` and simplifying by `Real.sq_sqrt`. The next loop should
fill `T2.nyman.restricted.finite.approx.real.support`, because the reusable project predicate
`nymanBeurlingRestrictedConcreteApprox` is indexed by `ℝ` with an explicit support restriction,
whereas the current theorem is indexed by the restricted subtype.

## Loop 123 Update

`T2.nyman.restricted.finite.approx.real.support` is closed.
`LeanLab.Riemann.NymanBeurling` now proves `exists_real_finsupp_of_restricted_finsupp` and
`exists_real_finsupp_integral_lt_of_restricted`. The proof uses `Finsupp.embDomain` along the
subtype embedding, `Finsupp.support_embDomain`, and `Finsupp.sum_embDomain` to preserve concrete
finite sums and expose the support condition `0 < a ∧ a ≤ 1`. The next loop should fill
`T2.nyman.restricted.concrete.approx.of.dense`.

## Loop 124 Update

`T2.nyman.restricted.concrete.approx.of.dense` is closed. `LeanLab.Riemann.NymanBeurling` now
proves `nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense`, packaging the
positive-tolerance subtype approximation and real-support bridge into
`nymanBeurlingRestrictedConcreteApprox`. The next loop should fill
`T2.nyman.restricted.route.summary` before choosing the next structural bridge.

## Loop 125 Update

`T2.nyman.restricted.route.summary` is closed. The route summary is recorded as
`research/tier2_nyman_restricted_route_summary_20260710.md`. It records the compiled project-local
chain from `nymanBeurlingRestrictedKernelDense` to `nymanBeurlingRestrictedConcreteApprox`, then
separates that result from the remaining classical Báez-Duarte/Nyman-Beurling gaps. The next loop
should fill `T2.nyman.baez.duarte.natural.index.inventory`.

## Loop 126 Update

`T2.nyman.baez.duarte.natural.index.inventory` is closed. The inventory is recorded as
`research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md`. Following the arch review,
this loop stayed bounded: it did not claim a classical criterion bridge or any implication to
`RiemannHypothesis`. It selected `{n : Nat // 0 < n}` as the first natural-index shape and the
reciprocal map `n ↦ ((n : Real)⁻¹)` into `nymanBeurlingRestrictedParameterSet` as the next formal
bridge. The next loop should close `T2.nyman.baez.duarte.reciprocal.map`.

## Loop 127 Update

`T2.nyman.baez.duarte.reciprocal.map` is closed. `LeanLab.Riemann.NymanBeurling` now defines
`baezDuartePositiveNatIndex`, proves `baezDuarte_reciprocal_mem_restricted`, packages the map as
`baezDuarteReciprocalParameter`, and proves injectivity by defining
`baezDuarteReciprocalEmbedding`. The next loop should close
`T2.nyman.baez.duarte.natural.finsupp.bridge`.

## Loop 128 Update

`T2.nyman.baez.duarte.natural.finsupp.bridge` is closed.
`LeanLab.Riemann.NymanBeurling` now proves
`exists_restricted_finsupp_of_baezDuarte_finsupp`, using `Finsupp.embDomain` along
`baezDuarteReciprocalEmbedding` to transport positive-natural-indexed finite coefficients to
restricted-parameter coefficients while preserving the concrete reciprocal-parameter finite sum.
The next loop should close `T2.nyman.baez.duarte.natural.integral.bridge`.

## Loop 129 Update

`T2.nyman.baez.duarte.natural.integral.bridge` is closed.
`LeanLab.Riemann.NymanBeurling` now proves
`exists_restricted_finsupp_integral_lt_of_baezDuarte`, transporting a positive-natural reciprocal
squared-error integral bound to a restricted-parameter squared-error integral bound by rewriting
the integrand through `exists_restricted_finsupp_of_baezDuarte_finsupp`. The next loop should close
`T2.nyman.baez.duarte.natural.concrete.approx.predicate`.

## Loop 130 Update

`T2.nyman.baez.duarte.natural.concrete.approx.predicate` is closed.
`LeanLab.Riemann.NymanBeurling` now defines `nymanBeurlingBaezDuarteConcreteApprox` and proves
`nymanBeurlingRestrictedConcreteApprox_of_baezDuarte`, connecting the positive-natural reciprocal
approximation predicate back to the existing restricted concrete approximation predicate. This is
still only a project-local approximation predicate, not a classical criterion or an RH bridge. The
next loop should close `T2.nyman.baez.duarte.natural.concrete.approx.unrestricted`.
