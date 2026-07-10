import LeanLab.Riemann.Targets

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Target ledger checks

This file is an engineering witness layer for `LeanLab.Riemann.Targets`.
Every `.proven` target with a `leanName` is checked here by Lean name
resolution. Selected high-value bridge targets also get exact statement
examples.
-/

namespace LeanLab.Riemann

/-- Name-resolution witness for every `.proven` ledger target with a `leanName`. -/
def checkedTargetNames : List Lean.Name :=
  [ ``riemannXi_eq_mul_completedRiemannZeta,
    ``isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial,
    ``liCoefficientCandidate_one_re_pos,
    ``fractionalPartKernel_memLp_two_unitInterval,
    ``fractionalPartKernelL2_mem_nymanBeurlingKernelSpan,
    ``nymanBeurlingKernelSpan_le_closure,
    ``nymanBeurlingKernelDense_iff_closure_eq_top,
    ``nymanBeurlingKernelDense_iff_orthogonal_eq_bot,
    ``mem_nymanBeurlingKernelSpan_orthogonal_iff,
    ``nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero,
    ``inner_fractionalPartKernelL2_eq_integral,
    ``nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero,
    ``unitIntervalOneL2_coeFn,
    ``unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense,
    ``unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt,
    ``unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt,
    ``unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt,
    ``unitIntervalL2_norm_sq_eq_integral_mul_self,
    ``finsupp_sum_fractionalPartKernelL2_coeFn,
    ``exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense,
    ``exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance,
    ``nymanBeurlingConcreteApprox_of_dense,
    ``nymanBeurlingConcreteApprox_of_restricted,
    ``nymanBeurlingRestrictedKernelSpan_le,
    ``nymanBeurlingRestrictedKernelClosure_le,
    ``nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure,
    ``nymanBeurlingKernelDense_of_restricted,
    ``nymanBeurlingConcreteApprox_of_restrictedKernelDense,
    ``unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense,
    ``unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt,
    ``mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum,
    ``exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense,
    ``exists_restricted_finsupp_sum_norm_sub_lt_of_dense,
    ``norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self,
    ``restricted_finsupp_sum_fractionalPartKernelL2_coeFn,
    ``exists_restricted_finsupp_integral_sq_lt_of_dense,
    ``exists_restricted_finsupp_integral_lt_of_dense_tolerance,
    ``exists_real_finsupp_integral_lt_of_restricted,
    ``nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense,
    ``baezDuarteReciprocalEmbedding,
    ``exists_restricted_finsupp_of_baezDuarte_finsupp,
    ``exists_restricted_finsupp_integral_lt_of_baezDuarte,
    ``nymanBeurlingRestrictedConcreteApprox_of_baezDuarte,
    ``riemannHypothesis_iff_nontrivial_zeros_on_line ]

example {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s :=
  riemannXi_eq_mul_completedRiemannZeta hs0 hs1

example (s : ℂ) :
    IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬IsTrivialZeroPoint s :=
  isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial s

example :
    0 < (liCoefficientCandidate 1).re :=
  liCoefficientCandidate_one_re_pos

example (h : nymanBeurlingKernelDense) :
    nymanBeurlingConcreteApprox :=
  nymanBeurlingConcreteApprox_of_dense h

example (h : nymanBeurlingRestrictedConcreteApprox) :
    nymanBeurlingConcreteApprox :=
  nymanBeurlingConcreteApprox_of_restricted h

example (h : nymanBeurlingBaezDuarteConcreteApprox) :
    nymanBeurlingRestrictedConcreteApprox :=
  nymanBeurlingRestrictedConcreteApprox_of_baezDuarte h

example :
    RiemannHypothesis ↔ ∀ (s : ℂ), IsNontrivialZero s → OnCriticalLine s :=
  riemannHypothesis_iff_nontrivial_zeros_on_line

end LeanLab.Riemann
