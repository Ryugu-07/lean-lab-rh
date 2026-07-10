import LeanLab.Riemann.Targets
import LeanLab.Riemann.BaezDuarteZetaRatio

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

open scoped ENNReal FourierTransform

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

example :
    nymanBeurlingConcreteApprox :=
  nymanBeurlingConcreteApprox_unconditional

example (h : nymanBeurlingRestrictedConcreteApprox) :
    nymanBeurlingConcreteApprox :=
  nymanBeurlingConcreteApprox_of_restricted h

example :
    unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure ↔
      nymanBeurlingRestrictedConcreteApprox :=
  unitIntervalOneL2_mem_restrictedClosure_iff_concreteApprox

example (c : ℝ →₀ ℝ) (hc : ∀ a ∈ c.support, 0 < a ∧ a ≤ 1) :
    (∫ x : ℝ in Set.Ioi 1,
      (c.sum fun a r => r * fractionalPartKernel a x) *
        (c.sum fun a r => r * fractionalPartKernel a x)) =
      (c.sum fun a r => r * a) ^ 2 :=
  restricted_finsupp_tail_error_eq_moment_sq c hc

example (h : nymanBeurlingBaezDuarteConcreteApprox) :
    nymanBeurlingRestrictedConcreteApprox :=
  nymanBeurlingRestrictedConcreteApprox_of_baezDuarte h

example :
    nymanBeurlingBaezDuarteFullLineConcreteApprox ↔
      ∀ δ : ℝ, 0 < δ →
        ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
          baezDuarteUnitIntervalError c + baezDuarteReciprocalMoment c ^ 2 < δ :=
  nymanBeurlingBaezDuarteFullLineConcreteApprox_iff

example (h : nymanBeurlingBaezDuarteFullLineConcreteApprox) :
    nymanBeurlingBaezDuarteConcreteApprox :=
  nymanBeurlingBaezDuarteConcreteApprox_of_fullLine h

example :
    RiemannHypothesis ↔ ∀ (s : ℂ), IsNontrivialZero s → OnCriticalLine s :=
  riemannHypothesis_iff_nontrivial_zeros_on_line

example (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun x : ℝ => (fractionalPartKernel 1 x : ℂ)) s
      (-riemannZeta s / s) :=
  hasMellin_fractionalPartKernel_one s hs0 hs1

example (n : baezDuartePositiveNatIndex) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin
      (fun x : ℝ =>
        (fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℂ)) s
      (((n : ℕ) : ℂ) ^ (-s) * (-riemannZeta s / s)) :=
  hasMellin_baezDuarteKernel n s hs0 hs1

noncomputable example :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 :=
  weightedLogPullback

example (f : positiveHalfLineComplexL2) :
    weightedLogPullback f =ᵐ[MeasureTheory.volume]
      fun u : ℝ => (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u)) :=
  weightedLogPullback_coeFn f

example (g : realLineComplexL2) :
    weightedLogPullback.symm g
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * g (-Real.log x) :=
  weightedLogPullback_symm_coeFn g

noncomputable example :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 :=
  baezDuarteFourierMellinL2

example (f : ℝ → ℂ) (τ : ℝ) :
    mellin f ((1 / 2 : ℂ) + τ * Complex.I) =
      𝓕 (fun u : ℝ =>
        (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u)))
        (τ / (2 * Real.pi)) :=
  mellin_criticalLine_eq_fourier f τ

example (β : ℝ) (hβ : β < 1 / 2) :
    MeasureTheory.MemLp (baezDuarteVerticalMajorant β) (2 : ℝ≥0∞)
      MeasureTheory.volume :=
  baezDuarteVerticalMajorant_memLp β hβ

example (ε : ℝ) (hε : ε < 1 / 4) :
    MeasureTheory.MemLp (baezDuarteVerticalMajorant (2 * ε)) (2 : ℝ≥0∞)
      MeasureTheory.volume :=
  baezDuarteFirstConvergenceMajorant_memLp ε hε

example :
    baezDuarteCriticalLineZetaZeroOrdinates.Countable :=
  baezDuarteCriticalLineZetaZeroOrdinates_countable

example :
    ∀ᵐ τ : ℝ ∂MeasureTheory.volume,
      Filter.Tendsto (fun ε : ℝ => baezDuarteZetaRatio ε τ)
        (nhds 0) (nhds 1) :=
  ae_tendsto_baezDuarteZetaRatio_one

example (ε : ℝ) (N : ℕ) {x : ℝ} (hx : 1 < x) :
    baezDuarteMobiusApprox (2 * ε) N x =
      (∑ a ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          (a : ℝ) ^ (-(1 + 2 * ε))) / x :=
  baezDuarteMobiusApprox_two_mul_eq_dirichletTail_of_one_lt ε N hx

example (ε m : ℝ) (hε : 0 ≤ ε)
    (f w : positiveHalfLineL2)
    (hweighted :
      w =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε) * f x)
    (htail :
      ∀ᵐ x : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        1 < x → f x = m / x) :
    ‖f‖ ^ 2 ≤ (1 + 2 * ε) * ‖w‖ ^ 2 :=
  baezDuarte_weightedTail_norm_sq_le ε m hε f w hweighted htail

example (ε : ℝ) (hε : 0 ≤ ε)
    (c : baezDuartePositiveNatIndex →₀ ℝ) (w : positiveHalfLineL2)
    (hweighted :
      w =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε) *
          (c.sum fun n r => r • baezDuarteKernelL2 n) x) :
    ‖c.sum fun n r => r • baezDuarteKernelL2 n‖ ^ 2 ≤
      (1 + 2 * ε) * ‖w‖ ^ 2 :=
  baezDuarte_finsupp_norm_sq_le_of_weighted ε hε c w hweighted

example :
    ∃ C ε₀ K : ℝ,
      0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ C * ε₀ < 1 / 2 ∧ 0 < K ∧
      ∀ (ε τ : ℝ), 0 ≤ ε → ε ≤ ε₀ →
        ‖baezDuarteZetaRatio ε τ‖ ≤
          K * (1 + |τ|) ^ (C * ε) :=
  exists_baezDuarteZetaRatio_bound

example :
    ∃ C ε₀ K : ℝ,
      0 < C ∧ 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ C * ε₀ < 1 / 2 ∧ 0 < K ∧
      MeasureTheory.MemLp
        (fun τ : ℝ =>
          ((5 * K : ℝ) : ℂ) * baezDuarteVerticalMajorant (C * ε₀) τ)
        (2 : ℝ≥0∞) MeasureTheory.volume ∧
      ∀ (ε τ : ℝ), 0 ≤ ε → ε ≤ ε₀ →
        ‖baezDuarteZetaRatioIntegrand ε τ‖ ≤
          ‖((5 * K : ℝ) : ℂ) * baezDuarteVerticalMajorant (C * ε₀) τ‖ :=
  exists_baezDuarteZetaRatioIntegrand_majorant

end LeanLab.Riemann
