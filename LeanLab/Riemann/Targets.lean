import LeanLab.Riemann.LiScaffold
import LeanLab.Riemann.NymanBeurling
import LeanLab.Riemann.BalazardSaias
import LeanLab.Riemann.ReciprocalZetaSubpower
import LeanLab.Riemann.TruncatedPerron
import LeanLab.Riemann.BalazardSaiasContour
import LeanLab.Riemann.BaezDuarteReverse

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Target ledger for RH proof-engineering work

This file is deliberately a compiled ledger, not a source of unproved
mathematical facts. Planned theorem statements live as strings until they are
proved elsewhere and linked back here by name.

The next loops should decrease this ledger or fill a blueprint node, rather
than merely adding convenient rewrite lemmas.
-/

namespace LeanLab.Riemann

/-- Coarse research tier for the target ledger. -/
inductive TargetTier where
  | tier1
  | tier2
  | tier3
  deriving DecidableEq, Repr

/-- Current status of a research target. -/
inductive TargetStatus where
  | planned
  | inProgress
  | proven
  | parked
  deriving DecidableEq, Repr

/--
A compiled bookkeeping entry for the RH project.

`statement` is text only; a target is usable as mathematics only after
`leanName` points at an existing theorem and `status = proven`.
-/
structure ResearchTarget where
  id : String
  tier : TargetTier
  title : String
  statement : String
  leanName : Option Lean.Name := (none : Option Lean.Name)
  status : TargetStatus
  note : String

/-- Current target ledger after the 2026-07-09 architectural review. -/
def rhTargets : List ResearchTarget :=
  [ { id := "T1.m1.baez.duarte.reverse"
      tier := .tier1
      title := "Formalize the reverse strong Baez-Duarte implication"
      statement :=
        "Prove that membership of the aligned complex positive-natural target in the kernel closure implies Mathlib.RiemannHypothesis."
      leanName := some ``baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis
      status := .proven
      note := "Batch M1-16 proves the exact reverse implication by the Mellin zero obstruction on source-structured full-line errors; no general Nyman-Beurling or Hardy-space premise is assumed. The forward RH-to-closure convergence assembly remains open." },
    { id := "T1.m1.balazard.saias"
      tier := .tier1
      title := "Compile the RH-specialized Balazard-Saias Mobius estimate"
      statement :=
        "Under Mathlib.RiemannHypothesis, prove the uniform N^(-delta/3)(1+|Im(s)|)^eta error bound for Mobius Dirichlet partial sums on 1/2+delta<=Re(s)<=1, using the analytic reciprocal of zeta at s=1."
      leanName := some ``RiemannHypothesis.exists_balazardSaias_specialized_bound_compiled
      status := .proven
      note := "Batch M1-15 compiles the preregistered RH specialization by contour shifting and quantitative error balancing, and discharges the Balazard-Saias premise from the Burnol forward consumer. The stronger general-alpha zero-free-half-plane proposition BalazardSaiasEstimate remains encoded but unproved." },
    { id := "T1.m1.truncated.perron"
      tier := .tier1
      title := "Formalize the source-specialized Mobius truncated Perron estimate"
      statement :=
        "Uniformly approximate the Mobius Dirichlet partial sum by the c=2, x=N+1/2 truncated Perron integral with an absolute C*(N+1)^2/T error."
      leanName := some ``exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le
      status := .proven
      note := "Batch M1-14 proves the exact source target via an explicit 2*pi*i rectangle residue calculation, positive and negative kernel estimates, dominated Mobius-series integration, half-integral logarithmic spacing, and a summable n^(-3/2) majorant." },
    { id := "T1.m1.reciprocal.zeta.subpower"
      tier := .tier1
      title := "Close the RH reciprocal-zeta subpower component of F1"
      statement :=
        "Under RH, uniformly bound reciprocal zeta by C*(1+|Im(s)|)^eta on every closed substrip 1/2+delta<=Re(s)<=1, for arbitrary delta and eta positive."
      leanName := some ``RiemannHypothesis.exists_reciprocalZeta_subpower_bound
      status := .proven
      note := "Batch M1-12 formalizes Titchmarsh 14.2 via an RH zero-free logarithm branch, Borel-Caratheodory, Hadamard three-circles, strict sublinear log growth, asymptotic exponentiation, and a compact low-height patch." },
    { id := "T1.m1.zeta.convexity.three.eighths"
      tier := .tier1
      title := "Close the unconditional zeta-convexity component of F1"
      statement :=
        "Prove an unconditional critical-line Riemann zeta bound with exponent 3/8 for |t| >= 1."
      leanName := some ``exists_norm_riemannZeta_criticalLine_le_rpow
      status := .proven
      note := "Batch M1-09 formalized Fiori's corrected midpoint Phragmen-Lindelof argument. Balazard-Saias remains open, so F1 itself is not closed." },
    { id := "T1.xi.completed.bridge"
      tier := .tier1
      title := "Bridge local xi to the completed zeta variant outside the poles"
      statement :=
        "For s != 0 and s != 1, relate riemannXi s to the completed Riemann zeta expression used by mathlib."
      leanName := some ``riemannXi_eq_mul_completedRiemannZeta
      status := .proven
      note := "Proved from completedRiemannZeta_eq by clearing the two pole-removal terms." },
    { id := "T1.xi.zero.bridge"
      tier := .tier1
      title := "Bridge local xi zeros to project nontrivial zeta zeros"
      statement :=
        "State and prove the precise correspondence between zeros of riemannXi and IsNontrivialZero, with pole and trivial-zero edge cases handled explicitly."
      leanName := some ``isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial
      status := .proven
      note := "Proved with the trivial-zero exclusion explicit on the riemannXi-zero side." },
    { id := "T1.li1.positivity"
      tier := .tier1
      title := "Finish positivity of the second local Li candidate"
      statement :=
        "Prove 0 < (liCoefficientCandidate 1).re, or record a precise library gap after a bounded inventory."
      leanName := some ``liCoefficientCandidate_one_re_pos
      status := .proven
      note := "Proved in Loop 84 by bounding the log-weighted Mellin term by 17/160 and proving that this is below the Li-side threshold." },
    { id := "T1.note.li.scaffold"
      tier := .tier1
      title := "Write a short result note for the xi and Li scaffold"
      statement :=
        "Summarize the local xi bridge, center scaffold, and first two local Li-candidate positivity results, including explicit limits."
      leanName := none
      status := .proven
      note := "Documentation target completed as research/li_scaffold_note_20260709.md; it cites compiled theorem names and separates local results from global RH claims." },
    { id := "T2.inventory.li.hadamard"
      tier := .tier2
      title := "Inventory mathlib support for a Li-criterion statement route"
      statement :=
        "Inspect available Hadamard product, entire function, zero multiset, and log-derivative infrastructure before choosing this route."
      leanName := none
      status := .proven
      note := "Inventory completed as research/tier2_li_hadamard_inventory_20260709.md; recommendation is not to choose this as the immediate Tier 2 route until global product and zero-enumeration bridges exist." },
    { id := "T2.inventory.nyman.beurling"
      tier := .tier2
      title := "Inventory mathlib support for the Nyman-Beurling route"
      statement :=
        "Inspect L2, closure, density, step functions, and fractional-part infrastructure before choosing this route."
      leanName := none
      status := .proven
      note := "Inventory completed as research/tier2_nyman_beurling_inventory_20260709.md; recommendation is to prefer this route for the immediate Tier 2 pivot because the first missing nodes are small L2/measurability lemmas." },
    { id := "T2.pivot"
      tier := .tier2
      title := "Choose one structural Tier 2 route after inventory"
      statement :=
        "Commit the next blueprint to either the Li/Hadamard route or the Nyman-Beurling route."
      leanName := none
      status := .proven
      note := "Loop 88 chooses the Nyman-Beurling foundation route, because the first formal nodes are bounded fractional-part kernels in L2." },
    { id := "T2.nyman.kernel.l2"
      tier := .tier2
      title := "Package the first Nyman-Beurling fractional-part kernel in L2"
      statement :=
        "For every real a, the function x ↦ Int.fract (a / x) belongs to L2 on the unit interval."
      leanName := some ``fractionalPartKernel_memLp_two_unitInterval
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; the stronger theorem fractionalPartKernel_memLp_unitInterval works for every exponent p, and fractionalPartKernelL2 packages the kernel as an L2 element." },
    { id := "T2.nyman.span.scaffold"
      tier := .tier2
      title := "Define the span generated by Nyman-Beurling kernels"
      statement :=
        "Define the real submodule of L2 on the unit interval generated by fractionalPartKernelL2, and prove each generator belongs to it."
      leanName := some ``fractionalPartKernelL2_mem_nymanBeurlingKernelSpan
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; nymanBeurlingKernelSpan is the real span of the packaged L2 kernels, with generator membership and the span minimality lemma nymanBeurlingKernelSpan_le." },
    { id := "T2.nyman.closure.scaffold"
      tier := .tier2
      title := "Define the closure of the Nyman-Beurling kernel span"
      statement :=
        "Define the topological closure of nymanBeurlingKernelSpan and prove the span is contained in its closure."
      leanName := some ``nymanBeurlingKernelSpan_le_closure
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; nymanBeurlingKernelClosure is the topological closure, with span inclusion, closedness, set-closure equality, and generator membership." },
    { id := "T2.nyman.density.predicate"
      tier := .tier2
      title := "Package the Nyman-Beurling density predicate"
      statement :=
        "Define the project-local density predicate for the kernel span and prove its equivalence with nymanBeurlingKernelClosure = top."
      leanName := some ``nymanBeurlingKernelDense_iff_closure_eq_top
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; nymanBeurlingKernelDense is Dense of the kernel span, equivalent to closure equals top and to pointwise membership in nymanBeurlingKernelClosure." },
    { id := "T2.nyman.orthogonal.reformulation"
      tier := .tier2
      title := "Reformulate kernel-span density by orthogonal complement"
      statement :=
        "Prove that nymanBeurlingKernelDense is equivalent to the orthogonal complement of nymanBeurlingKernelSpan being bottom."
      leanName := some ``nymanBeurlingKernelDense_iff_orthogonal_eq_bot
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using Submodule.topologicalClosure_eq_top_iff after the local closure-density bridge." },
    { id := "T2.nyman.orthogonal.pointwise"
      tier := .tier2
      title := "Unpack orthogonality against every Nyman-Beurling generator"
      statement :=
        "For f in unitIntervalL2, express f in nymanBeurlingKernelSpan orthogonal complement as vanishing inner product against every fractionalPartKernelL2 a."
      leanName := some ``mem_nymanBeurlingKernelSpan_orthogonal_iff
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by span induction from the packaged fractional-part generators." },
    { id := "T2.nyman.density.pointwise"
      tier := .tier2
      title := "Reformulate density as absence of generator-orthogonal vectors"
      statement :=
        "Prove that nymanBeurlingKernelDense is equivalent to every f in unitIntervalL2 being zero whenever its inner product with every fractionalPartKernelL2 a vanishes."
      leanName := some ``nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by combining the orthogonal-bottom density theorem with the pointwise generator-orthogonality theorem." },
    { id := "T2.nyman.inner.integral.inventory"
      tier := .tier2
      title := "Inventory Lp inner-product formulas for packaged kernels"
      statement :=
        "Inspect mathlib support for rewriting inner products with fractionalPartKernelL2 as integrals over the restricted unit interval."
      leanName := some ``inner_fractionalPartKernelL2_eq_integral
      status := .proven
      note := "Inventory recorded in research/tier2_nyman_inner_integral_inventory_20260710.md; mathlib's L2.inner_def plus fractionalPartKernelL2_coeFn gives the first compiled inner-product-to-integral bridge." },
    { id := "T2.nyman.density.integral"
      tier := .tier2
      title := "Reformulate density by integral orthogonality"
      statement :=
        "Prove that nymanBeurlingKernelDense is equivalent to every f in unitIntervalL2 being zero whenever the integral of fractionalPartKernel a times f is zero for every real a."
      leanName := some ``nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by combining the density pointwise theorem with inner_fractionalPartKernelL2_eq_integral." },
    { id := "T2.nyman.constant.one.l2"
      tier := .tier2
      title := "Package the constant one function in unitIntervalL2"
      statement :=
        "Define the constant-one function as an element of unitIntervalL2 and prove its almost-everywhere representative theorem."
      leanName := some ``unitIntervalOneL2_coeFn
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling; unitIntervalOne packages the constant-one function, unitIntervalOneL2 is its L2 representative, and unitIntervalOneL2_coeFn identifies the representative almost everywhere." },
    { id := "T2.nyman.density.one.closure"
      tier := .tier2
      title := "Use density to place constant one in the Nyman-Beurling closure"
      statement :=
        "Prove that nymanBeurlingKernelDense implies unitIntervalOneL2 belongs to nymanBeurlingKernelClosure."
      leanName := some ``unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling by applying the pointwise closure form of nymanBeurlingKernelDense to unitIntervalOneL2; this remains conditional on density." },
    { id := "T2.nyman.one.closure.epsilon"
      tier := .tier2
      title := "Reformulate constant-one closure membership by epsilon approximation"
      statement :=
        "Prove an epsilon-distance formulation of unitIntervalOneL2 belonging to nymanBeurlingKernelClosure, with approximants drawn from nymanBeurlingKernelSpan."
      leanName := some ``unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using Metric.mem_closure_iff; also added exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense as the density-conditioned approximation corollary." },
    { id := "T2.nyman.span.finite.approx"
      tier := .tier2
      title := "Unpack span approximants as finite kernel combinations"
      statement :=
        "Reformulate the epsilon approximant from nymanBeurlingKernelSpan as a finite real linear combination of packaged fractional-part kernels."
      leanName := some ``unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using Finsupp.mem_span_range_iff_exists_finsupp; also added the density-conditioned finite-combination approximation corollary." },
    { id := "T2.nyman.finite.approx.norm"
      tier := .tier2
      title := "Rewrite finite kernel approximation distance as an L2 norm"
      statement :=
        "Reformulate the finite-kernel epsilon approximation statement using the norm of unitIntervalOneL2 minus the finite kernel combination."
      leanName := some ``unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt
      status := .proven
      note := "Proved in LeanLab.Riemann.NymanBeurling using dist_eq_norm; also added the density-conditioned norm-approximation corollary." },
    { id := "T2.nyman.finite.approx.integral.inventory"
      tier := .tier2
      title := "Inventory L2 norm-square formulas for finite kernel approximants"
      statement :=
        "Inspect mathlib support for rewriting the L2 norm of unitIntervalOneL2 minus a finite kernel combination as an integral of a squared representative."
      leanName := some ``unitIntervalL2_norm_sq_eq_integral_mul_self
      status := .proven
      note := "Inventory recorded in research/tier2_nyman_finite_approx_integral_inventory_20260710.md; proved the generic L2 norm-square-to-integral bridge and its finite-combination specialization." },
    { id := "T2.nyman.finite.approx.representatives"
      tier := .tier2
      title := "Identify finite kernel combinations with concrete representatives"
      statement :=
        "Prove an almost-everywhere representative theorem for c.sum fun a r => r • fractionalPartKernelL2 a, rewriting it as the corresponding finite sum of fractionalPartKernel functions."
      leanName := some ``finsupp_sum_fractionalPartKernelL2_coeFn
      status := .proven
      note := "Loop 103 proved the finite-combination representative theorem, the constant-one-minus-finite-combination representative theorem, and the concrete norm-square integral formula." },
    { id := "T2.nyman.finite.approx.integral.epsilon"
      tier := .tier2
      title := "Convert concrete finite approximation into an integral-square bound"
      statement :=
        "Assuming nymanBeurlingKernelDense and 0 < eps, derive a finite coefficient family whose concrete squared-error integral is below eps^2."
      leanName := some ``exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense
      status := .proven
      note := "Loop 104 combined the density-conditioned norm approximation, the concrete norm-square integral identity, and sq_lt_sq₀ to derive the concrete squared-error integral bound." },
    { id := "T2.nyman.finite.approx.integral.tolerance"
      tier := .tier2
      title := "Remove the squared tolerance from the concrete integral approximation"
      statement :=
        "Assuming nymanBeurlingKernelDense and 0 < delta, derive a finite coefficient family whose concrete squared-error integral is below delta."
      leanName := some ``exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance
      status := .proven
      note := "Loop 105 instantiated the epsilon-square theorem with Real.sqrt delta and simplified by Real.sq_sqrt." },
    { id := "T2.nyman.concrete.approx.predicate"
      tier := .tier2
      title := "Package the concrete Nyman-Beurling approximation predicate"
      statement :=
        "Define a project-local predicate saying every positive tolerance has a finite fractional-part approximation with concrete squared-error integral below that tolerance, and prove nymanBeurlingKernelDense implies it."
      leanName := some ``nymanBeurlingConcreteApprox_of_dense
      status := .proven
      note := "Loop 106 defined nymanBeurlingConcreteApprox and proved nymanBeurlingKernelDense implies it." },
    { id := "T2.nyman.classical.criterion.inventory"
      tier := .tier2
      title := "Inventory the gap to the classical Nyman-Beurling criterion"
      statement :=
        "Compare nymanBeurlingConcreteApprox with the classical Nyman-Beurling/Baez-Duarte criterion and record the exact formal gaps before attempting an RH bridge."
      leanName := none
      status := .proven
      note := "Loop 107 recorded the first inventory. M0 batches 02-05 rejected the bad local predicates and aligned the positive-natural criterion in real and complex L2(0,infinity), including the full tail, endpoint, closure/tolerance form, and coefficient field. Fixed node M0 is complete." },
    { id := "T2.nyman.restricted.concrete.approx.predicate"
      tier := .tier2
      title := "Package a restricted-parameter concrete approximation predicate"
      statement :=
        "Define a concrete approximation predicate requiring finite coefficient support to lie in 0 < a and a <= 1, and prove it implies nymanBeurlingConcreteApprox."
      leanName := some ``nymanBeurlingConcreteApprox_of_restricted
      status := .proven
      note := "Loop 108 defined the project-local restricted predicate. M0 batch 02 proved its exact local closure equivalence but confirmed it is not Beurling's published space because it lacks the zero-moment condition." },
    { id := "T2.nyman.restricted.span.scaffold"
      tier := .tier2
      title := "Scaffold the restricted-parameter kernel span"
      statement :=
        "Define the submodule generated by fractionalPartKernelL2 a for parameters satisfying 0 < a and a <= 1, and prove it is contained in nymanBeurlingKernelSpan."
      leanName := some ``nymanBeurlingRestrictedKernelSpan_le
      status := .proven
      note := "Loop 109 defined the restricted parameter set, restricted kernel set, restricted kernel span, generator membership, and the inclusion into nymanBeurlingKernelSpan." },
    { id := "T2.nyman.restricted.closure.scaffold"
      tier := .tier2
      title := "Scaffold the restricted-parameter kernel closure"
      statement :=
        "Define the topological closure of nymanBeurlingRestrictedKernelSpan, prove the restricted span lies in it, and prove it is contained in nymanBeurlingKernelClosure."
      leanName := some ``nymanBeurlingRestrictedKernelClosure_le
      status := .proven
      note := "Loop 110 defined nymanBeurlingRestrictedKernelClosure, proved span-to-closure, closedness, the closure coercion formula, inclusion into nymanBeurlingKernelClosure, and restricted generator membership in the closure." },
    { id := "T2.nyman.restricted.density.predicate"
      tier := .tier2
      title := "Package the restricted-parameter kernel density predicate"
      statement :=
        "Define density of nymanBeurlingRestrictedKernelSpan and prove its basic closure-top and pointwise-closure forms."
      leanName := some ``nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure
      status := .proven
      note := "Loop 111 defined nymanBeurlingRestrictedKernelDense and proved its closure-top and pointwise restricted-closure equivalences." },
    { id := "T2.nyman.restricted.density.implies.unrestricted"
      tier := .tier2
      title := "Bridge restricted density to unrestricted density"
      statement :=
        "Prove nymanBeurlingRestrictedKernelDense implies nymanBeurlingKernelDense."
      leanName := some ``nymanBeurlingKernelDense_of_restricted
      status := .proven
      note := "Loop 112 used the pointwise closure forms and nymanBeurlingRestrictedKernelClosure_le to prove restricted density implies unrestricted density." },
    { id := "T2.nyman.restricted.density.concrete.approx"
      tier := .tier2
      title := "Derive concrete approximation from restricted density"
      statement :=
        "Prove nymanBeurlingRestrictedKernelDense implies nymanBeurlingConcreteApprox."
      leanName := some ``nymanBeurlingConcreteApprox_of_restrictedKernelDense
      status := .proven
      note := "Loop 113 composed nymanBeurlingKernelDense_of_restricted with nymanBeurlingConcreteApprox_of_dense to derive the existing concrete approximation predicate from restricted density." },
    { id := "T2.nyman.restricted.density.one.closure"
      tier := .tier2
      title := "Place the constant-one target in the restricted closure"
      statement :=
        "Prove nymanBeurlingRestrictedKernelDense implies unitIntervalOneL2 belongs to nymanBeurlingRestrictedKernelClosure."
      leanName := some ``unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense
      status := .proven
      note := "Loop 114 instantiated the pointwise restricted-closure form of nymanBeurlingRestrictedKernelDense at unitIntervalOneL2." },
    { id := "T2.nyman.restricted.one.closure.epsilon"
      tier := .tier2
      title := "Convert restricted closure membership to epsilon approximation"
      statement :=
        "Prove unitIntervalOneL2 belongs to nymanBeurlingRestrictedKernelClosure iff it can be epsilon-approximated by elements of nymanBeurlingRestrictedKernelSpan."
      leanName := some ``unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt
      status := .proven
      note := "Loop 115 proved the restricted closure epsilon-distance equivalence and the restricted-density approximant existence corollary." },
    { id := "T2.nyman.restricted.span.finite.approx"
      tier := .tier2
      title := "Unpack restricted-span approximants into finite sums"
      statement :=
        "Prove membership in nymanBeurlingRestrictedKernelSpan is equivalent to a finite real linear combination of fractionalPartKernelL2 indexed by restricted parameters."
      leanName := some ``mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum
      status := .proven
      note := "Loop 116 defined restrictedFractionalPartKernelL2, proved the restricted kernel set is its range, and unpacked restricted-span membership into subtype-indexed finite sums." },
    { id := "T2.nyman.restricted.finite.approx.dist"
      tier := .tier2
      title := "Get subtype-indexed finite-sum distance approximants"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < eps, derive a finite coefficient family over restricted parameters whose packaged finite sum is within eps of unitIntervalOneL2."
      leanName := some ``exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense
      status := .proven
      note := "Loop 117 combined the restricted span epsilon approximant theorem with subtype-indexed finite-sum unpacking." },
    { id := "T2.nyman.restricted.finite.approx.norm"
      tier := .tier2
      title := "Rewrite restricted finite-sum approximation in norm form"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < eps, derive a subtype-indexed finite coefficient family whose packaged finite-sum difference from unitIntervalOneL2 has norm below eps."
      leanName := some ``exists_restricted_finsupp_sum_norm_sub_lt_of_dense
      status := .proven
      note := "Loop 118 rewrote the restricted finite-sum distance approximation as a norm inequality using dist_eq_norm." },
    { id := "T2.nyman.restricted.finite.approx.integral.inventory"
      tier := .tier2
      title := "Inventory norm-square integral bridge for restricted finite sums"
      statement :=
        "Inspect whether the existing L2 norm-square-to-integral bridge applies to subtype-indexed restricted finite kernel combinations."
      leanName := some ``norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self
      status := .proven
      note := "Loop 119 recorded the inventory and proved the restricted finite-sum specialization of the generic L2 norm-square bridge." },
    { id := "T2.nyman.restricted.finite.approx.representatives"
      tier := .tier2
      title := "Identify restricted finite sums with concrete representatives"
      statement :=
        "Prove almost-everywhere representative theorems for subtype-indexed restricted finite kernel sums and their difference from unitIntervalOneL2."
      leanName := some ``restricted_finsupp_sum_fractionalPartKernelL2_coeFn
      status := .proven
      note := "Loop 120 proved the restricted finite-sum representative bridge, the constant-one difference bridge, and the concrete norm-square integral theorem." },
    { id := "T2.nyman.restricted.finite.approx.integral.epsilon"
      tier := .tier2
      title := "Convert restricted finite approximation into an integral-square bound"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < eps, derive a subtype-indexed restricted finite coefficient family whose concrete squared-error integral is below eps^2."
      leanName := some ``exists_restricted_finsupp_integral_sq_lt_of_dense
      status := .proven
      note := "Loop 121 combined the restricted norm approximation with the concrete norm-square integral theorem." },
    { id := "T2.nyman.restricted.finite.approx.integral.tolerance"
      tier := .tier2
      title := "Remove the squared tolerance from restricted concrete approximation"
      statement :=
        "Assuming nymanBeurlingRestrictedKernelDense and 0 < delta, derive a subtype-indexed restricted finite coefficient family whose concrete squared-error integral is below delta."
      leanName := some ``exists_restricted_finsupp_integral_lt_of_dense_tolerance
      status := .proven
      note := "Loop 122 instantiated the epsilon-square theorem with Real.sqrt delta to obtain an arbitrary positive tolerance." },
    { id := "T2.nyman.restricted.finite.approx.real.support"
      tier := .tier2
      title := "Push restricted subtype coefficients to real-indexed support"
      statement :=
        "Convert subtype-indexed restricted finite coefficients into real-indexed finite coefficients with support contained in 0 < a and a <= 1, preserving the concrete finite sum."
      leanName := some ``exists_real_finsupp_integral_lt_of_restricted
      status := .proven
      note := "Loop 123 used Finsupp.embDomain along the subtype embedding to push restricted coefficients to real-indexed coefficients with explicit support restriction." },
    { id := "T2.nyman.restricted.concrete.approx.of.dense"
      tier := .tier2
      title := "Derive restricted concrete approximation from restricted density"
      statement :=
        "Prove nymanBeurlingRestrictedConcreteApprox from nymanBeurlingRestrictedKernelDense."
      leanName := some ``nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense
      status := .proven
      note := "Loop 124 packaged the subtype positive-tolerance approximation and real-support bridge into the restricted concrete approximation predicate." },
    { id := "T2.nyman.restricted.route.summary"
      tier := .tier2
      title := "Summarize the completed restricted concrete approximation branch"
      statement :=
        "Record the compiled chain from nymanBeurlingRestrictedKernelDense to nymanBeurlingRestrictedConcreteApprox and onward to nymanBeurlingConcreteApprox, with remaining classical criterion gaps."
      leanName := none
      status := .proven
      note := "Loop 125 recorded the local restricted chain. M0 batch 02 corrected the summary by isolating the missing zero-moment/full-line-tail condition." },
    { id := "T2.nyman.baez.duarte.natural.index.inventory"
      tier := .tier2
      title := "Inventory Baez-Duarte natural-parameter indexing"
      statement :=
        "Inspect candidate Lean index types and reciprocal maps for representing Baez-Duarte natural-parameter finite approximants, and choose the next small formal bridge."
      leanName := none
      status := .proven
      note := "Loop 126 recorded research/tier2_nyman_baez_duarte_natural_index_inventory_20260710.md and selected the transparent positive-natural subtype plus reciprocal map as the next bridge shape." },
    { id := "T2.nyman.baez.duarte.reciprocal.map"
      tier := .tier2
      title := "Map positive natural indices to restricted real parameters"
      statement :=
        "Define or verify the reciprocal map from positive natural indices into nymanBeurlingRestrictedParameterSet, preparing the natural-indexed finite-sum bridge."
      leanName := some ``baezDuarteReciprocalEmbedding
      status := .proven
      note := "Loop 127 added baezDuartePositiveNatIndex, verified reciprocal membership in the restricted parameter set, and packaged the map as baezDuarteReciprocalEmbedding." },
    { id := "T2.nyman.baez.duarte.natural.finsupp.bridge"
      tier := .tier2
      title := "Push positive-natural coefficients to restricted parameters"
      statement :=
        "Use baezDuarteReciprocalEmbedding to transport positive-natural-indexed finite coefficients into restricted-parameter coefficients while preserving the concrete reciprocal-parameter finite sum."
      leanName := some ``exists_restricted_finsupp_of_baezDuarte_finsupp
      status := .proven
      note := "Loop 128 used Finsupp.embDomain along baezDuarteReciprocalEmbedding to push positive-natural coefficients to restricted-parameter coefficients while preserving the concrete reciprocal finite sum." },
    { id := "T2.nyman.baez.duarte.natural.integral.bridge"
      tier := .tier2
      title := "Push positive-natural integral bounds to restricted parameters"
      statement :=
        "Use the positive-natural finite-sum bridge to transport a concrete squared-error integral bound from reciprocal natural parameters to restricted-parameter coefficients."
      leanName := some ``exists_restricted_finsupp_integral_lt_of_baezDuarte
      status := .proven
      note := "Loop 129 used the positive-natural finite-sum bridge to transport a reciprocal-natural squared-error integral bound to restricted-parameter coefficients." },
    { id := "T2.nyman.baez.duarte.natural.concrete.approx.predicate"
      tier := .tier2
      title := "Package positive-natural concrete approximation"
      statement :=
        "Define the Baez-Duarte positive-natural concrete approximation predicate and prove that it implies nymanBeurlingRestrictedConcreteApprox."
      leanName := some ``nymanBeurlingRestrictedConcreteApprox_of_baezDuarte
      status := .proven
      note := "Loop 130 defined a local positive-natural predicate. M0 batch 02 found its missing full-line tail; Batch 03 added the separate source-faithful predicate nymanBeurlingBaezDuarteFullLineConcreteApprox. This local target remains only a weak consequence." },
    { id := "T2.nyman.baez.duarte.natural.concrete.approx.unrestricted"
      tier := .tier2
      title := "Forget the Baez-Duarte restriction to the concrete predicate"
      statement :=
        "Prove nymanBeurlingBaezDuarteConcreteApprox implies nymanBeurlingConcreteApprox by composing through nymanBeurlingRestrictedConcreteApprox."
      leanName := some ``nymanBeurlingConcreteApprox_unconditional
      status := .parked
      note := "M0 audit AUDIT-20260710-M0-01 proved the conclusion unconditionally using opposite signed parameters. The implication is obsolete as a criterion target, and the unrestricted predicate must not be used for M1." },
    { id := "T3.rh.horizon"
      tier := .tier3
      title := "Riemann Hypothesis horizon"
      statement :=
        "Keep mathlib's RiemannHypothesis as the long-run horizon, not as a direct loop target."
      leanName := some ``riemannHypothesis_iff_nontrivial_zeros_on_line
      status := .parked
      note := "Useful for orientation, but not an admissible immediate loop target." } ]

/-- Targets that still require work before they can be considered discharged. -/
def openRhTargets : List ResearchTarget :=
  rhTargets.filter (fun target => target.status != .proven)

/-- Tier 1 targets that should be preferred before structural route selection. -/
def tierOneRhTargets : List ResearchTarget :=
  rhTargets.filter (fun target => target.tier == .tier1)

end LeanLab.Riemann
