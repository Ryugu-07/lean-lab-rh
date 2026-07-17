import LeanLab.Riemann.Targets
import LeanLab.Riemann.DeBruijnNewmanHeat
import LeanLab.Riemann.DeBruijnNewmanZeros
import LeanLab.Riemann.DeBruijnNewmanThreshold
import LeanLab.Riemann.DeBruijnNewmanForward
import LeanLab.Riemann.DeBruijnNewmanUpperHalf
import LeanLab.Riemann.DeBruijnNewmanDynamics
import LeanLab.Riemann.DeBruijnNewmanLiMoments
import LeanLab.Riemann.DeBruijnNewmanThirdLi
import LeanLab.Riemann.DeBruijnNewmanLiCriterion
import LeanLab.Riemann.FinitePowerSumRigidity
import LeanLab.Riemann.H6GapVelocityAudit
import LeanLab.Riemann.H6PositiveCoshLiAudit
import LeanLab.Riemann.H6ReverseHeatLiAudit
import LeanLab.Riemann.LiSymmetricZeroFormula
import LeanLab.Riemann.LiReverseCriterion
import LeanLab.Riemann.LiWeilGram
import LeanLab.Riemann.WeilTestAlgebra
import LeanLab.Riemann.WeilConvolution
import LeanLab.Riemann.WeilStripClass
import LeanLab.Riemann.WeilExplicitIntegrand
import LeanLab.Riemann.WeilZeroCutoff
import LeanLab.Riemann.WeilGaussianHeight
import LeanLab.Riemann.WeilGaussianExplicitFormula
import LeanLab.Riemann.WeilSymmetricGaussianFamily
import LeanLab.Riemann.WeilFiniteGaussianTestCore
import LeanLab.Riemann.WeilGaussianQuadraticPositivity
import LeanLab.Riemann.WeilGaussianPositivityCriterion
import LeanLab.Riemann.WeilGaussianFixedWidthCriterion
import LeanLab.Riemann.WeilCompactLaplaceSeparator
import LeanLab.Riemann.WeilCompactLaplaceZeroCutoff
import LeanLab.Riemann.WeilCompactLaplaceArithmeticFormula
import LeanLab.Riemann.WeilGaussianPrimeKernelSignAudit
import LeanLab.Riemann.PolsonGGCContinuationAudit
import LeanLab.Riemann.FreedmanGreenLiftAudit
import LeanLab.Riemann.BaezDuarteZetaRatio
import LeanLab.Riemann.BaezDuarteQTwo
import LeanLab.Riemann.BurnolLowerBound
import LeanLab.Riemann.BurnolA
import LeanLab.Riemann.BurnolHardy
import LeanLab.Riemann.BurnolY
import LeanLab.Riemann.BurnolGram
import LeanLab.Riemann.BurnolFiniteLowerBound
import LeanLab.Riemann.BurnolFullLowerBound
import LeanLab.Riemann.M2ProjectionNormAudit
import LeanLab.Riemann.M2LadderFrequencyAudit
import LeanLab.Riemann.M2GramGeometry
import LeanLab.Riemann.M2SparseObstruction

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

example
    (h : baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure) :
    RiemannHypothesis :=
  baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis h

open scoped BigOperators ComplexConjugate ContDiff ENNReal FourierTransform InnerProductSpace Topology

/-- Name-resolution witness for every `.proven` ledger target with a `leanName`. -/
def checkedTargetNames : List Lean.Name :=
  [ ``riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure,
    ``riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure,
    ``RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2,
    ``exists_norm_riemannZeta_criticalLine_le_rpow,
    ``riemannXi_eq_mul_completedRiemannZeta,
    ``isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial,
    ``support_riemannXiZeroDivisor,
    ``exists_riemannXi_hadamard_factorization,
    ``exists_liCoefficientCandidate_eq_hadamard_zero_formula,
    ``liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm,
    ``riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg,
    ``riemannHypothesis_iff_forall_liWeilQuadratic_nonneg,
    ``mellin_weilStar_criticalLine,
    ``mellin_weilConvolution_star_criticalLine,
    ``IsWeilStripAdmissible.weilAutocorrelation,
    ``exists_weilExplicitIntegrand_eq_hadamardZeroSum,
    ``rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum,
    ``exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral,
    ``gaussianXi_arithmetic_explicit_formula,
    ``symmetricGaussianXi_arithmetic_explicit_formula,
    ``symmetricGaussianXiPacket_arithmetic_explicit_formula,
    ``RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg,
    ``riemannHypothesis_iff_gaussianXiArithmeticQuadratic_re_nonneg,
    ``riemannHypothesis_iff_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg,
    ``exists_compactSupport_xiDivisor_laplace_tsum_separator,
    ``not_integrableOn_polsonImaginaryFrullaniComponent,
    ``freedmanGreenLift_listedPremises_do_not_force_contraction,
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
    ``RiemannHypothesis.baezDuarteNaturalDistance_liminf_ge_fullZeroSum,
    ``deBruijnNewman_zeroCoordinate_framework,
    ``deBruijnNewmanHeat_firstTwoLi_endpoint,
    ``riemannHypothesis_iff_nontrivial_zeros_on_line ]

example :
    RiemannHypothesis ↔
      baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure :=
  riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure

example :
    RiemannHypothesis ↔
      baezDuarteQTwoComplexTargetL2 ∈
        baezDuarteQTwoComplexKernelClosure :=
  riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure

example {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s :=
  riemannXi_eq_mul_completedRiemannZeta hs0 hs1

example :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (3 / 8 : ℝ) :=
  exists_norm_riemannZeta_criticalLine_le_rpow

example (s : ℂ) :
    IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬IsTrivialZeroPoint s :=
  isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial s

example (s : ℂ) :
    IsNontrivialZero s ↔ riemannXi s = 0 :=
  isNontrivialZero_iff_riemannXi_eq_zero s

example {s : ℂ} (hs : IsTrivialZeroPoint s) :
    riemannXi s ≠ 0 :=
  riemannXi_ne_zero_of_isTrivialZeroPoint hs

example (s : ℂ) :
    riemannXiZeroDivisor s = (riemannXiZeroMultiplicity s : ℤ) :=
  riemannXiZeroDivisor_apply s

example :
    Function.support riemannXiZeroDivisor = {s : ℂ | IsNontrivialZero s} :=
  support_riemannXiZeroDivisor

example (s : ℂ) :
    0 < riemannXiZeroMultiplicity s ↔ IsNontrivialZero s :=
  riemannXiZeroMultiplicity_pos_iff s

example (s : ℂ) :
    riemannXiZeroMultiplicity (1 - s) = riemannXiZeroMultiplicity s :=
  riemannXiZeroMultiplicity_one_sub s

example {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {s : ℂ | IsNontrivialZero s}).Finite :=
  compact_inter_nontrivialZeros_finite hK

example : riemannXi = Complex.riemannXi :=
  riemannXi_eq_complex_riemannXi

example (s : ℂ) :
    Int.toNat (MeromorphicOn.divisor riemannXi Set.univ s) =
      riemannXiZeroMultiplicity s :=
  riemannXi_divisor_toNat_eq_zeroMultiplicity s

example (ρ : ℂ) :
    (∃ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      Complex.Hadamard.divisorZeroIndex₀_val p = ρ) ↔ IsNontrivialZero ρ :=
  exists_riemannXiDivisorZeroIndex_val_iff ρ

example :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) riemannXi :=
  riemannXi_entireOfOrderAtMost_one

example :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) =>
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) :=
  summable_riemannXiDivisorZeroIndex_norm_inv_sq

example :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
      riemannXi z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z :=
  exists_riemannXi_hadamard_factorization

example {z : ℂ} (hz : ¬IsNontrivialZero z) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      logDeriv riemannXi z = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum hz

example :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      ∀ n : ℕ, liCoefficientCandidate n =
        (∑ i ∈ Finset.range (n + 1),
            ((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
              (iteratedDeriv (n - i)
                  (fun z : ℂ => Polynomial.eval z P.derivative) 1 +
                ∑' p : RiemannXiDivisorZeroIndex,
                  riemannXiLogDerivZeroDerivativeTerm (n - i) p 1)) /
          (n.factorial : ℂ) :=
  exists_liCoefficientCandidate_eq_hadamard_zero_formula

example (n : ℕ) :
    Summable (riemannXiSymmetrizedLiZeroTerm n) :=
  summable_riemannXiSymmetrizedLiZeroTerm n

example (n : ℕ) :
    liCoefficientCandidate n =
      ∑' p : RiemannXiDivisorZeroIndex, riemannXiSymmetrizedLiZeroTerm n p :=
  liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm n

example (hRH : RiemannHypothesis) (n : ℕ) :
    liCoefficientCandidate n =
      ∑' p : RiemannXiDivisorZeroIndex,
        (Complex.normSq
          (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p)) : ℂ) / 2 :=
  RiemannHypothesis.liCoefficientCandidate_eq_tsum_normSq hRH n

example (hRH : RiemannHypothesis) (n : ℕ) :
    (liCoefficientCandidate n).im = 0 ∧ 0 ≤ (liCoefficientCandidate n).re :=
  ⟨RiemannHypothesis.liCoefficientCandidate_im_eq_zero hRH n,
    RiemannHypothesis.liCoefficientCandidate_re_nonneg hRH n⟩

example (hLi : ∀ n : ℕ, 0 ≤ (liCoefficientCandidate n).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg hLi

example :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (liCoefficientCandidate n).re :=
  riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg

example (n m : ℕ) :
    liWeilGram n m =
      liCoefficientCandidate n + liCoefficientCandidate m -
        if n = m then 0 else liCoefficientCandidate (Nat.dist n m - 1) :=
  liWeilGram_eq_liCoefficients n m

example (n : ℕ) :
    liWeilGram n n = 2 * liCoefficientCandidate n :=
  liWeilGram_diagonal n

example : liWeilGram 0 1 = liCoefficientCandidate 1 := by
  rw [liWeilGram_eq_liCoefficients]
  norm_num [Nat.dist]

example :
    liWeilGram 0 2 =
      liCoefficientCandidate 0 + liCoefficientCandidate 2 - liCoefficientCandidate 1 := by
  rw [liWeilGram_eq_liCoefficients]
  norm_num [Nat.dist]

example (hRH : RiemannHypothesis) (c : ℕ →₀ ℝ) :
    liWeilQuadratic c =
      ∑' p : RiemannXiDivisorZeroIndex,
        Complex.normSq (liWeilCombination c p) :=
  RiemannHypothesis.liWeilQuadratic_eq_tsum_normSq hRH c

example :
    RiemannHypothesis ↔ ∀ c : ℕ →₀ ℝ, 0 ≤ liWeilQuadratic c :=
  riemannHypothesis_iff_forall_liWeilQuadratic_nonneg

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

example (hRH : RiemannHypothesis)
    {δ η : ℝ} (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (t : ℝ), 2 ≤ N →
      ‖burnolMobiusTransformedError δ N t‖ ≤
        K * (N : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖ :=
  RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le_compiled
    hRH hδ hδ_top hη

example {η : ℝ} (hη : η < 1 / 8) :
    MeasureTheory.MemLp (baezDuarteVerticalMajorant (3 / 8 + η))
      (2 : ℝ≥0∞) MeasureTheory.volume :=
  burnolMobiusMajorant_memLp hη

example {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ / 3))
      Filter.atTop (nhds 0) :=
  tendsto_natCast_rpow_neg_delta_div_three hδ

example (N : ℕ) (hN : 0 < N) :
    baezDuarteFiniteComplexKernelSpan N ≤
      burnolKernelSpan ((N : ℝ)⁻¹) :=
  baezDuarteFiniteComplexKernelSpan_le_burnolKernelSpan N hN

example (N : ℕ) (hN : 0 < N) :
    burnolDistance ((N : ℝ)⁻¹) ≤ baezDuarteNaturalDistance N :=
  burnolDistance_inv_natCast_le_baezDuarteNaturalDistance N hN

example :
    Filter.Tendsto (fun N : ℕ => ((N : ℝ)⁻¹)) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
  tendsto_natCast_inv_nhdsWithin_Ioi_zero

example {t : ℝ} (ht : 1 < t) :
    burnolA t = 0 :=
  burnolA_eq_zero_of_one_lt ht

example {t : ℝ} (ht : 0 < t) :
    burnolA t =
      (∫ u : ℝ in Set.Ioi t, burnolFractionalPartDiv u) - fractionalPartKernel 1 t :=
  burnolA_eq_tailIntegral_sub_fractionalPart ht

example :
    MeasureTheory.MemLp burnolA (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  burnolA_memLp_two_positiveHalfLine

noncomputable example : positiveHalfLineComplexL2 :=
  burnolComplexAL2

example :
    burnolComplexAL2
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))]
        fun t => (burnolA t : ℂ) :=
  burnolComplexAL2_coeFn

example (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun t : ℝ => (burnolA t : ℂ)) s
      ((s - 1) * riemannZeta s / s ^ 2) :=
  hasMellin_burnolA s hs0 hs1

noncomputable example :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] positiveHalfLineComplexL2 :=
  burnolHardyInverseL2

example :
    burnolHardyInverseL2 baezDuarteComplexTargetL2 = burnolChiOneL2 :=
  burnolHardyInverseL2_target

example (theta : burnolContinuousParameter) :
    burnolHardyInverseL2 (burnolContinuousKernelL2 theta) =
      -burnolModelKernelL2 theta :=
  burnolHardyInverseL2_kernel theta

example (cutoff : ℝ) :
    (burnolKernelSpan cutoff).map burnolHardyInverseL2.toLinearMap =
      burnolModelKernelSpan cutoff :=
  burnolHardyInverseL2_map_kernelSpan cutoff

example (cutoff : ℝ) :
    burnolDistance cutoff = burnolModelDistance cutoff :=
  burnolDistance_eq_modelDistance cutoff

example {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs : s.re = 1 / 2) :
    Filter.Tendsto (fun w : ℂ => burnolPreY lambda w k)
      (𝓝[{w : ℂ | w.re < 1 / 2}] s)
      (𝓝 (burnolY lambda s k)) :=
  tendsto_burnolPreY hlambda0 hlambda1 s k hs

example {lambda t : ℝ} (hlt : t < lambda) (s : ℂ) (k : ℕ) :
    burnolYTransformed lambda s k t = 0 :=
  burnolYTransformed_eq_zero_of_lt hlt s k

example {lambda t : ℝ} (hlambdaT : lambda ≤ t)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolYTransformed lambda s k t -
        iteratedDeriv k
          (fun z : ℂ => burnolVSpectral z * (t : ℂ) ^ (-z)) s‖ ≤
      4 * burnolPhiSeriesBound k :=
  norm_burnolYTransformed_sub_V_cpow_le
    hlambdaT s k hs0 hs1 ht0 ht1

example {lambda t : ℝ} (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht : 1 ≤ t) :
    ‖burnolYTransformed lambda s k t‖ ≤
      burnolPhiHardySquareLargeCoeff s k *
        (1 + |Real.log t|) ^ 2 / t :=
  norm_burnolYTransformed_le_large hlambda1 s k hs0 hs1 ht

example {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) (hs : s.re = 1 / 2) :
    inner (𝕜 := ℂ) (burnolY lambda s k)
        (burnolNormalizedModelKernelL2 theta) =
      (-1 : ℂ) ^ k *
        iteratedDeriv k (burnolDirectPairingSource theta) s :=
  inner_burnolY_normalizedModelKernel
    hlambda0 hlambda1 theta s k hlambdaTheta hs

example {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs : s.re = 1 / 2)
    (hzeta : riemannZeta s = 0)
    (horder : (k + 1 : ℕ∞) ≤ analyticOrderAt riemannZeta s) :
    burnolY lambda s k ∈ (burnolModelKernelSpan lambda)ᗮ :=
  burnolY_mem_modelKernelSpan_orthogonal
    hlambda0 hlambda1 s k hs hzeta horder

example {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Filter.Tendsto (fun lambda : ℝ =>
      inner ℂ (burnolX lambda s₂ l) (burnolX lambda s₁ k))
      (𝓝[>] (0 : ℝ))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) :=
  tendsto_inner_burnolX hs₁ hs₂ k l

example :
    burnolChiOnePhase =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) :=
  burnolChiOnePhase_isBigO_sq

example :
    burnolAPhaseL2 burnolChiOneL2 = burnolChiOnePhaseL2 :=
  burnolAPhaseL2_chiOne

example {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) :
    Filter.Tendsto (fun lambda : ℝ =>
      ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
        inner ℂ (burnolX lambda s k) burnolChiOneL2)
      (𝓝[>] (0 : ℝ))
      (nhds (if k = 0 then (s - 1) / s ^ 2 else 0)) :=
  tendsto_sqrtLog_inner_chiOne_burnolX hs k

example (m : ℕ) : IsUnit (burnolHilbertMatrix m).det :=
  burnolHilbertMatrix_isUnit_det m

example (n : ℕ) :
    (burnolHilbertMatrix (n + 1))⁻¹
        (0 : Fin (n + 1)) (0 : Fin (n + 1)) =
      (((n + 1 : ℕ) : ℂ)) ^ 2 :=
  burnolHilbertMatrix_inv_zero_zero n

example {s : ℂ} (hs : s.re = 1 / 2) (m : ℕ) :
    Filter.Tendsto (fun lambda : ℝ => (burnolGramMatrix lambda s m)⁻¹)
      (𝓝[>] (0 : ℝ)) (nhds (burnolHilbertMatrix m)⁻¹) :=
  tendsto_burnolGramMatrix_inv hs m

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (m : ℕ) :
    Filter.Tendsto (fun lambda : ℝ => burnolBlockGramMatrix lambda rho m)
      (𝓝[>] (0 : ℝ))
      (nhds (burnolHilbertBlockMatrix (ι := ι) m)) :=
  tendsto_burnolBlockGramMatrix hcritical hinjective m

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (m : ℕ) :
    Filter.Tendsto (fun lambda : ℝ => (burnolBlockGramMatrix lambda rho m)⁻¹)
      (𝓝[>] (0 : ℝ))
      (nhds (burnolHilbertBlockMatrix (ι := ι) m)⁻¹) :=
  tendsto_burnolBlockGramMatrix_inv hcritical hinjective m

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Filter.Tendsto (fun lambda : ℝ =>
      burnolFiniteGramMatrix lambda rho multiplicity)
      (𝓝[>] (0 : ℝ))
      (nhds (burnolFiniteHilbertMatrix multiplicity)) :=
  tendsto_burnolFiniteGramMatrix hcritical hinjective multiplicity

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) :
    IsUnit (burnolFiniteHilbertMatrix multiplicity).det :=
  burnolFiniteHilbertMatrix_isUnit_det multiplicity

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Filter.Tendsto (fun lambda : ℝ =>
      (burnolFiniteGramMatrix lambda rho multiplicity)⁻¹)
      (𝓝[>] (0 : ℝ))
      (nhds (burnolFiniteHilbertMatrix multiplicity)⁻¹) :=
  tendsto_burnolFiniteGramMatrix_inv hcritical hinjective multiplicity

example (hRH : RiemannHypothesis)
    (R : Finset {rho : ℂ // IsNontrivialZero rho}) :
    ENNReal.ofReal (Real.sqrt (
      ∑ rho ∈ R,
        (burnolZetaZeroMultiplicity (rho : ℂ) : ℝ) ^ 2 /
          ‖(rho : ℂ)‖ ^ 2)) ≤
      Filter.liminf (fun lambda : ℝ =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Set.Ioi 0)) :=
  RiemannHypothesis.burnolDistance_liminf_ge_finset hRH R

example (hRH : RiemannHypothesis) :
    burnolFullZeroLowerConstant ≤
      Filter.liminf (fun lambda : ℝ =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Set.Ioi 0)) :=
  RiemannHypothesis.burnolDistance_liminf_ge_fullZeroSum hRH

example (hRH : RiemannHypothesis) :
    burnolFullZeroLowerConstant ≤
      Filter.liminf (fun N : ℕ =>
        ENNReal.ofReal (baezDuarteNaturalDistance N) *
          ENNReal.ofReal (Real.sqrt (Real.log (N : ℝ)))) Filter.atTop :=
  RiemannHypothesis.baezDuarteNaturalDistance_liminf_ge_fullZeroSum hRH

example :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      P.transpose = P ∧ P * P = P ∧
        ¬ ∀ x : Fin 2 → ℝ,
          finTwoMaxNorm (Matrix.mulVec P x) ≤ finTwoMaxNorm x :=
  exists_symmetric_idempotent_not_maxNorm_nonexpansive

example :
    ¬ ∀ x : Fin 5 → ℝ,
      finFiveMaxNorm (Matrix.mulVec m2AuditWongPThree x) ≤ finFiveMaxNorm x :=
  not_m2AuditWongPThree_maxNorm_nonexpansive

example :
    ¬ min (Real.log 2) (Real.log 3) *
        (m2AuditCarvillLadderDistance 0 2 3 0 : ℝ) ≤
      |m2AuditCarvillLadderFrequency 0 2 3 0| :=
  not_m2Audit_carvill_source_frequency_lower_bound

example (c : Nat →₀ Complex) :
    (1 / 40 : Real) * (∑ i ∈ c.support, ‖c i‖ ^ 2) <=
      ‖sparseGramCombination c‖ ^ 2 :=
  sparseGram_lower_frame_bound c

example : (Matrix.gram Real finiteGramWitnessVector).PosDef :=
  finiteGramWitness_posDef

example (i : Fin 1) :
    ⟪finiteGramWitnessVector i, finiteGramWitnessTarget⟫_Real = 0 :=
  finiteGramWitness_target_orthogonal i

example (j : Nat) :
    ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j),
        sparseTargetWitnessL2⟫_Complex = 0 :=
  inner_sparseGramKernel_sparseTargetWitness_eq_zero j

example {x : Real} (hx : x ∈ Set.Ioc (1 / 2 : Real) (2 / 3)) :
    (1 : Real) = -fractionalPartKernel 1 x + 1 / x :=
  one_eq_neg_fractionalPartKernel_add_div_on_sparseInterval_one hx

example :
    (1 / 6 : Real) * (11 / 225) - (1 / 15) * (7 / 72) = 1 / 600 :=
  sparseTarget_two_piece_moment_determinant

example :
    ⟪baezDuarteComplexTargetL2, sparseTargetWitnessL2⟫_Complex =
      (1 / 9 : Complex) :=
  inner_target_sparseTargetWitness

example : baezDuarteComplexTargetL2 ∉ sparseGramKernelClosure :=
  baezDuarteComplexTargetL2_not_mem_sparseGramKernelClosure

example (hRH : RiemannHypothesis) {δ : ℝ}
    (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) :
    ∃ f : positiveHalfLineL2,
      Filter.Tendsto (baezDuarteMobiusApproxL2 δ) Filter.atTop (nhds f) ∧
        f ∈ baezDuarteKernelClosure :=
  RiemannHypothesis.exists_tendsto_baezDuarteMobiusApproxL2 hRH hδ hδ_top

example (f : ℝ → ℂ) (s : ℂ) :
    mellin (weilInvolution f) s = mellin f (1 - s) :=
  mellin_weilInvolution f s

example (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (weilStar f) s ↔
      MellinConvergent f (1 - conj s) :=
  mellinConvergent_weilStar_iff f s

example (f : ℝ → ℂ) (t : ℝ) :
    mellin (weilStar f) (1 / 2 + (t : ℂ) * Complex.I) =
      conj (mellin f (1 / 2 + (t : ℂ) * Complex.I)) :=
  mellin_weilStar_criticalLine f t

example {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (weilConvolution f g) s :=
  mellinConvergent_weilConvolution hf hg

example {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (weilConvolution f g) s = mellin f s * mellin g s :=
  mellin_weilConvolution hf hg

example {f g : ℝ → ℂ} (t : ℝ)
    (hf : MellinConvergent f (1 / 2 + (t : ℂ) * Complex.I))
    (hg : MellinConvergent g (1 / 2 + (t : ℂ) * Complex.I)) :
    mellin (weilConvolution f (weilStar g)) (1 / 2 + (t : ℂ) * Complex.I) =
      mellin f (1 / 2 + (t : ℂ) * Complex.I) *
        conj (mellin g (1 / 2 + (t : ℂ) * Complex.I)) :=
  mellin_weilConvolution_star_criticalLine t hf hg

example {f : ℝ → ℂ} (t : ℝ)
    (hf : MellinConvergent f (1 / 2 + (t : ℂ) * Complex.I)) :
    mellin (weilConvolution f (weilStar f)) (1 / 2 + (t : ℂ) * Complex.I) =
      Complex.normSq (mellin f (1 / 2 + (t : ℂ) * Complex.I)) :=
  mellin_weilAutocorrelation_criticalLine t hf

example {δ : ℝ} (hδ : 0 < δ) :
    IsWeilStripAdmissible δ (0 : ℝ → ℂ) :=
  isWeilStripAdmissible_zero hδ

example {δ : ℝ} {f g : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) (hg : IsWeilStripAdmissible δ g) :
    IsWeilStripAdmissible δ (f + g) :=
  hf.add hg

example {δ : ℝ} {f : ℝ → ℂ} (hf : IsWeilStripAdmissible δ f) (c : ℂ) :
    IsWeilStripAdmissible δ (c • f) :=
  hf.const_smul c

example {δ : ℝ} {f : ℝ → ℂ} (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ (weilInvolution f) :=
  hf.weilInvolution

example {δ : ℝ} {f : ℝ → ℂ} (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ (weilStar f) :=
  hf.weilStar

example {δ : ℝ} {f g : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) (hg : IsWeilStripAdmissible δ g) :
    IsWeilStripAdmissible δ (weilConvolution f g) :=
  hf.weilConvolution hg

example {δ : ℝ} {f : ℝ → ℂ} (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ (weilConvolution f (weilStar f)) :=
  hf.weilAutocorrelation

example {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s -
        LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt hs

example {s : ℂ} (hs : 1 < s.re) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      Polynomial.eval s P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) =
        1 / s + 1 / (s - 1) + logDeriv Complex.Gammaℝ s -
          LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
  exists_weilExplicitIntegrand_eq_hadamardZeroSum hs

example {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z) l r b t =
      2 * (Real.pi : ℂ) * Complex.I *
        ∑ᶠ p : RiemannXiDivisorZeroIndex,
          if riemannXiZeroStrictlyInsideRectangle l r b t p then
            F (riemannXiDivisorZeroValue p)
          else 0 :=
  rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum
    hF hlr hbt hboundary

example {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    ∃ T : ℕ → ℝ,
      Filter.Tendsto T Filter.atTop Filter.atTop ∧
      (∀ n : ℕ, ∀ p : RiemannXiDivisorZeroIndex,
        ¬riemannXiZeroOnRectangleBoundary (1 - c) c (-T n) (T n) p) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ y : ℝ in -T n..T n,
            riemannXiGaussianWeight a ((c : ℂ) + y * Complex.I) *
              logDeriv riemannXi ((c : ℂ) + y * Complex.I))
        Filter.atTop
        (nhds ((Real.pi : ℂ) *
          ∑' p : RiemannXiDivisorZeroIndex,
            riemannXiGaussianWeight a (riemannXiDivisorZeroValue p))) :=
  exists_gaussianXiZeroFreeHeight_tendsto_rightVerticalIntegral ha hc

example {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Summable (gaussianVonMangoldtWeight a) :=
  summable_gaussianVonMangoldtWeight ha hc

example {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    MeasureTheory.Integrable (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * Complex.I) *
        logDeriv Complex.Gammaℝ ((c : ℂ) + y * Complex.I)) :=
  integrable_gaussianXiArchimedean ha hc

example {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiGaussianWeight a (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * Real.exp (a / 4) +
        gaussianXiArchimedeanIntegral a c -
          ∑' n : ℕ, gaussianVonMangoldtWeight a n :=
  gaussianXi_arithmetic_explicit_formula ha hc

example {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianWeight a b (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) *
          (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) +
        symmetricGaussianXiArchimedeanIntegral a b c -
          ∑' n : ℕ, symmetricGaussianVonMangoldtWeight a b n :=
  symmetricGaussianXi_arithmetic_explicit_formula ha hc

example {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 0 < a i)
    {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianPacketWeight a b w (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * symmetricGaussianXiPacketPoleFactor a b w +
        symmetricGaussianXiPacketArchimedeanIntegral a b w c -
          ∑' n : ℕ, symmetricGaussianPacketVonMangoldtWeight a b w n :=
  symmetricGaussianXiPacket_arithmetic_explicit_formula a b w ha hc

example {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (b w : ι → ℝ) :
    Summable (gaussianXiZeroSquareTerm a b w) :=
  RiemannHypothesis.summable_gaussianXiZeroSquareTerm hRH ha b w

example {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    (a : ℝ) (b w : ι → ℝ) :
    gaussianXiZeroQuadratic a b w =
      ((∑' p : RiemannXiDivisorZeroIndex,
        gaussianXiZeroSquareTerm a b w p : ℝ) : ℂ) :=
  RiemannHypothesis.gaussianXiZeroQuadratic_eq_tsum_square hRH a b w

example {ι : Type*} [Fintype ι]
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b w : ι → ℝ) :
    (Real.pi : ℂ) * gaussianXiZeroQuadratic a b w =
      gaussianXiArithmeticQuadratic a b w c :=
  gaussianXiZeroQuadratic_arithmetic_formula ha hc b w

example {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b w : ι → ℝ) :
    0 ≤ (gaussianXiArithmeticQuadratic a b w c).re :=
  RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg hRH ha hc b w

example :
    RiemannHypothesis ↔
      ∀ (ι : Type) [Fintype ι] {a : ℝ}, 0 < a →
        ∀ b w : ι → ℝ,
          0 ≤ (gaussianXiArithmeticQuadratic a b w 2).re :=
  riemannHypothesis_iff_gaussianXiArithmeticQuadratic_re_nonneg

example
    (hpos : ∀ (ι : Type) [Fintype ι] {a : ℝ}, 0 < a →
      ∀ b w : ι → ℝ,
        0 ≤ (gaussianXiArithmeticQuadratic a b w 2).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_gaussianXiArithmeticQuadratic_re_nonneg hpos

example {a0 : ℝ} (ha0 : 0 < a0) :
    RiemannHypothesis ↔
      ∀ (ι : Type) [Fintype ι], ∀ b w : ι → ℝ,
        0 ≤ (gaussianXiArithmeticQuadratic a0 b w 2).re :=
  riemannHypothesis_iff_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg ha0

example {a0 : ℝ} (ha0 : 0 < a0)
    (hpos : ∀ (ι : Type) [Fintype ι], ∀ b w : ι → ℝ,
      0 ≤ (gaussianXiArithmeticQuadratic a0 b w 2).re) :
    RiemannHypothesis :=
  riemannHypothesis_of_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg ha0 hpos

example (p0 : RiemannXiDivisorZeroIndex) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℂ,
      ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧
      compactLaplaceTransform f (riemannXiDivisorZeroValue p0) = 1 ∧
      Summable (fun p : RiemannXiDivisorZeroIndex ↦
        ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) ∧
      ∑' p : RiemannXiDivisorZeroIndex,
        (if riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0 then 0
        else ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) < ε :=
  exists_compactSupport_xiDivisor_laplace_tsum_separator p0 hε

example {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Filter.Tendsto
      (selectedXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c)
      Filter.atTop
      (nhds ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          symmetrizedCompactLaplaceWeight f
            (riemannXiDivisorZeroValue p))) :=
  tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral hf hfsupp hc

example {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Filter.Tendsto
      (selectedXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c)
      Filter.atTop
      (nhds ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          symmetrizedCompactLaplaceWeight f
            (riemannXiDivisorZeroValue p))) :=
  tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral_sixContDiff hf hfsupp hc

example {f : ℝ → ℂ} (hfsupp : HasCompactSupport f) :
    Function.HasFiniteSupport (compactSymmetrizedVonMangoldtWeight f) :=
  hasFiniteSupport_compactSymmetrizedVonMangoldtWeight hfsupp

example {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) * ∑' p : RiemannXiDivisorZeroIndex,
        symmetrizedCompactLaplaceWeight f
          (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1 +
        compactSymmetrizedXiArchimedeanIntegral f c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n :=
  symmetrizedCompactLaplaceXi_arithmetic_explicit_formula hf hfsupp hc

example {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) * ∑' p : RiemannXiDivisorZeroIndex,
        symmetrizedCompactLaplaceWeight f
          (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1 +
        compactSymmetrizedXiArchimedeanIntegral f c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n :=
  symmetrizedCompactLaplaceXi_arithmetic_explicit_formula_sixContDiff hf hfsupp hc

example :
    ∃ a : ℝ, ∃ b : Fin 2 → ℝ,
      0 < a ∧
      ¬(symmetricGaussianPrimeKernelMatrix a b 2).PosSemidef ∧
      ¬(-symmetricGaussianPrimeKernelMatrix a b 2).PosSemidef :=
  exists_pos_symmetricGaussianPrimeKernelMatrix_indefinite

example {gamma y : ℝ} (hgamma : 0 < gamma) (hy : 2 * gamma ^ 2 < y ^ 2) :
    ¬ MeasureTheory.IntegrableOn
      (polsonImaginaryFrullaniIntegrand gamma y) (Set.Ioi 1) :=
  not_integrableOn_polsonImaginaryFrullaniIntegrand hgamma hy

example {gamma y : ℝ} (hgamma : 0 < gamma) (hy : 2 * gamma ^ 2 < y ^ 2) :
    ¬ MeasureTheory.IntegrableOn
      (polsonImaginaryFrullaniComponent gamma y) (Set.Ioi 1) :=
  not_integrableOn_polsonImaginaryFrullaniComponent hgamma hy

example :
    (∀ x, freedmanGreenAuditTrace (freedmanGreenAuditRepresentative x) = x) ∧
    (∃ h : FreedmanGreenAuditSpace, h ≠ 0 ∧ freedmanGreenAuditTrace h = 0) ∧
    (∀ x h, freedmanGreenAuditTrace h = 0 →
      freedmanGreenAuditForm (freedmanGreenAuditRepresentative x) h = 0) ∧
    (∀ t, |freedmanGreenAuditMultiplier t| ≤ |t|) ∧
    (∀ x, freedmanGreenAuditNegativeFeature (freedmanGreenAuditRepresentative x) =
      freedmanGreenAuditCompression
        (freedmanGreenAuditMultiplier
          (freedmanGreenAuditLift
            (freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x))))) ∧
    (¬ ∀ x,
      |freedmanGreenAuditCompression
        (freedmanGreenAuditMultiplier
          (freedmanGreenAuditLift
            (freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x))))| ≤
        |freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x)|) ∧
    freedmanGreenAuditForm (freedmanGreenAuditRepresentative 1)
      (freedmanGreenAuditRepresentative 1) < 0 :=
  freedmanGreenLift_listedPremises_do_not_force_contraction

example {C K E : ℝ → ℝ}
    (hC : ∀ t, |C t| ≤ |t|)
    (hK : ∀ t, |K t| ≤ |t|)
    (hE : ∀ t, |E t| ≤ |t|) :
    ∀ t, |C (K (E t))| ≤ |t| :=
  contraction_comp_three hC hK hE

example {ι : Type*} [Fintype ι] (a : ℝ) (b : ι → ℝ) (c : ℝ) :
    gaussianXiArithmeticQuadratic a b (fun _ => 0) c = 0 :=
  gaussianXiArithmeticQuadratic_zero a b c

example (F : Finset ℂ)
    (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (hzero : 0 ∈ F) (hone : 1 ∈ F) :
    RiemannHypothesis ↔
      ∀ g : ℝ → ℂ,
        ContDiff ℝ ∞ g →
        HasCompactSupport g →
        (∀ z ∈ F, compactLaplaceTransform g z = 0) →
        0 ≤ (compactWeilArithmeticQuadratic g).re :=
  riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg
    F hFzero hzero hone

example (z : ℂ) :
    completedRiemannZeta₀ ((1 + Complex.I * z) / 2) =
      8 * ∫ u : ℝ in Set.Ioi 0,
        (deBruijnNewmanThetaTail u : ℂ) * Complex.cos (z * (u : ℂ)) :=
  completedRiemannZeta₀_critical_line_eq_thetaTailIntegral z

example (z : ℂ) :
    deBruijnNewmanH 0 z =
      (1 / 8) * riemannXi ((1 + Complex.I * z) / 2) :=
  deBruijnNewmanH_zero_eq_riemannXi z

example (c : ℝ) (hc : 0 ≤ c) (d : ℝ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
        ‖deBruijnNewmanPhi u‖) (Set.Ioi 0) :=
  integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi c hc d

example (t : ℝ) (z : ℂ) :
    HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanH tau z)
      (deBruijnNewmanHSecondMoment t z) t :=
  hasDerivAt_deBruijnNewmanH_time t z

example (t : ℝ) : Differentiable ℂ (deBruijnNewmanH t) :=
  differentiable_deBruijnNewmanH t

example (t : ℝ) (z : ℂ) :
    deriv (deriv (deBruijnNewmanH t)) z =
      -deBruijnNewmanHSecondMoment t z :=
  deriv_deriv_deBruijnNewmanH t z

example (t : ℝ) (z : ℂ) :
    deriv (fun tau : ℝ ↦ deBruijnNewmanH tau z) t =
      -deriv (deriv (deBruijnNewmanH t)) z :=
  deBruijnNewmanH_backward_heat_equation t z

example :
    (∀ z : ℂ, deBruijnNewmanH 0 z = 0 ↔
      IsNontrivialZero ((1 + Complex.I * z) / 2)) ∧
    (∀ s : ℂ, deBruijnNewmanH 0 (deBruijnNewmanZeroCoordinate s) = 0 ↔
      IsNontrivialZero s) ∧
    (∀ z : ℂ, deBruijnNewmanH 0 z = 0 → z.im ∈ Set.Ioo (-1) 1) ∧
    (RiemannHypothesis ↔ deBruijnNewmanAllZerosReal 0) :=
  deBruijnNewman_zeroCoordinate_framework

example : deBruijnNewmanH 0 Complex.I ≠ 0 :=
  deBruijnNewmanH_zero_I_ne_zero

example : deBruijnNewmanH 0 (-Complex.I) ≠ 0 :=
  deBruijnNewmanH_zero_neg_I_ne_zero

example {u : ℝ} (hu : 0 ≤ u) : 0 < deBruijnNewmanPhi u :=
  deBruijnNewmanPhi_pos hu

example (t : ℝ) : deBruijnNewmanH t 0 ≠ 0 :=
  deBruijnNewmanH_zero_ne_zero t

example : Continuous (fun p : ℝ × ℂ ↦ deBruijnNewmanH p.1 p.2) :=
  continuous_deBruijnNewmanH_joint

example : IsClosed {t : ℝ | deBruijnNewmanAllZerosReal t} :=
  isClosed_setOf_deBruijnNewmanAllZerosReal

example {t tau : ℝ} (htt : t ≤ tau)
    (ht : deBruijnNewmanAllZerosReal t) :
    deBruijnNewmanAllZerosReal tau :=
  deBruijnNewmanAllZerosReal_mono htt ht

example {t : ℝ} (ht0 : 0 ≤ t) (hthalf : t ≤ (1 : ℝ) / 2)
    {z : ℂ} (hz : deBruijnNewmanH t z = 0) :
    z.im ^ 2 ≤ 1 - 2 * t :=
  deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 hthalf hz

example : deBruijnNewmanAllZerosReal ((1 : ℝ) / 2) :=
  deBruijnNewmanAllZerosReal_one_half

example : Continuous
    (fun p : ℝ × ℂ ↦ deBruijnNewmanHSecondMoment p.1 p.2) :=
  continuous_deBruijnNewmanHSecondMoment_joint

example (t : ℝ) (r : ℂ) :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀
          (deBruijnNewmanH t) (Set.univ : Set ℂ) ↦
        if Complex.Hadamard.divisorZeroIndex₀_val p = r then 0
        else 1 / (r - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) :=
  summable_deBruijnNewman_regularizedZeroForceTerm t r

example {t : ℝ} {r : ℂ}
    (hr : deBruijnNewmanH t r = 0)
    (hsimple : deriv (deBruijnNewmanH t) r ≠ 0) :
    deriv (deriv (deBruijnNewmanH t)) r /
        (2 * deriv (deBruijnNewmanH t) r) =
      deBruijnNewmanRegularizedZeroForce t r :=
  deBruijnNewmanH_second_deriv_div_two_deriv_eq_regularizedZeroForce hr hsimple

example {x : ℝ → ℂ} {t : ℝ} {v : ℂ} (hx : HasDerivAt x v t) :
    HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanH tau (x tau))
      (deBruijnNewmanHSecondMoment t (x t) +
        deriv (deBruijnNewmanH t) (x t) * v) t :=
  hasDerivAt_deBruijnNewmanH_along hx

example {x : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hx : HasDerivAt x v t)
    (hzero : ∀ tau : ℝ, deBruijnNewmanH tau (x tau) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (x t) ≠ 0) :
    v = 2 * deBruijnNewmanRegularizedZeroForce t (x t) :=
  deBruijnNewman_simpleZeroPath_velocity hx hzero hsimple

example {x : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hx : HasDerivAt x v t)
    (hzero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (x tau) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (x t) ≠ 0) :
    v = 2 * deBruijnNewmanRegularizedZeroForce t (x t) :=
  deBruijnNewman_simpleZeroPath_velocity_of_eventually hx hzero hsimple

example {t r : ℝ}
    (hr : deBruijnNewmanH t (r : ℂ) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (r : ℂ) ≠ 0) :
    ∃ x : ℝ → ℂ,
      x t = (r : ℂ) ∧
      Filter.Tendsto x (nhds t) (nhds (r : ℂ)) ∧
      HasDerivAt x (2 * deBruijnNewmanRegularizedZeroForce t (r : ℂ)) t ∧
      (∀ᶠ tau in nhds t,
        deBruijnNewmanH tau (x tau) = 0 ∧ (x tau).im = 0) ∧
      (∀ᶠ p : ℝ × ℂ in nhds (t, (r : ℂ)),
        deBruijnNewmanH p.1 p.2 = 0 ↔ x p.1 = p.2) :=
  exists_deBruijnNewman_localRealSimpleZeroPath hr hsimple

example {t r s : ℝ} (hrs : r < s)
    (hr : deBruijnNewmanH t (r : ℂ) = 0)
    (hs : deBruijnNewmanH t (s : ℂ) = 0)
    (hrSimple : deriv (deBruijnNewmanH t) (r : ℂ) ≠ 0)
    (hsSimple : deriv (deBruijnNewmanH t) (s : ℂ) ≠ 0) :
    ∃ x y : ℝ → ℂ,
      x t = (r : ℂ) ∧ y t = (s : ℂ) ∧
      HasDerivAt x (2 * deBruijnNewmanRegularizedZeroForce t (r : ℂ)) t ∧
      HasDerivAt y (2 * deBruijnNewmanRegularizedZeroForce t (s : ℂ)) t ∧
      (∀ᶠ tau in nhds t,
        deBruijnNewmanH tau (x tau) = 0 ∧
        (x tau).im = 0 ∧
        deBruijnNewmanH tau (y tau) = 0 ∧
        (y tau).im = 0 ∧
        (x tau).re < (y tau).re) :=
  exists_deBruijnNewman_orderedLocalRealSimpleZeroPaths hrs hr hs hrSimple hsSimple

example {x y : ℝ → ℂ} {t : ℝ} {vx vy : ℂ}
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ ((y tau).re - (x tau).re) ^ 2)
      (4 * ((y t).re - (x t).re) *
        (deBruijnNewmanRegularizedZeroForce t (y t) -
          deBruijnNewmanRegularizedZeroForce t (x t)).re) t :=
  hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq
    hx hy hxZero hyZero hxSimple hySimple

example {t : ℝ} {r s : ℂ} (hrs : r ≠ s)
    (hr : deBruijnNewmanH t r = 0)
    (hs : deBruijnNewmanH t s = 0)
    (hrSimple : deriv (deBruijnNewmanH t) r ≠ 0)
    (hsSimple : deriv (deBruijnNewmanH t) s ≠ 0) :
    deBruijnNewmanRegularizedZeroForce t s -
        deBruijnNewmanRegularizedZeroForce t r =
      2 / (s - r) + deBruijnNewmanZeroPairForceRemainder t r s :=
  deBruijnNewmanRegularizedZeroForce_sub_eq_two_div_add_pairRemainder
    hrs hr hs hrSimple hsSimple

example {x y : ℝ → ℂ} {t r s : ℝ} {vx vy : ℂ} (hrs : r < s)
    (hxAnchor : x t = (r : ℂ)) (hyAnchor : y t = (s : ℂ))
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ ((y tau).re - (x tau).re) ^ 2)
      (8 + 4 * (s - r) *
        (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re) t :=
  hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq_pairRemainder
    hrs hxAnchor hyAnchor hx hy hxZero hyZero hxSimple hySimple

example (t : ℝ)
    (p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ)) :
    deBruijnNewmanH t (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 :=
  deBruijnNewmanH_divisorZeroIndex₀_val_eq_zero t p

example {r u s : ℝ} (hru : r < u) (hus : u < s) :
    0 < (1 / ((s : ℂ) - (u : ℂ)) - 1 / ((r : ℂ) - (u : ℂ))).re :=
  realPairForceContribution_re_pos_of_between hru hus

example {t r s : ℝ} (hall : deBruijnNewmanAllZerosReal t)
    (hadj : deBruijnNewmanAdjacentRealZeros t r s) :
    (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re ≤ 0 :=
  deBruijnNewmanZeroPairForceRemainder_re_nonpos hall hadj

example {x y : ℝ → ℂ} {t r s : ℝ} {vx vy : ℂ}
    (hall : deBruijnNewmanAllZerosReal t)
    (hadj : deBruijnNewmanAdjacentRealZeros t r s)
    (hxAnchor : x t = (r : ℂ)) (hyAnchor : y t = (s : ℂ))
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ ((y tau).re - (x tau).re) ^ 2)
        (8 + 4 * (s - r) *
          (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re) t ∧
      8 + 4 * (s - r) *
          (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re ≤ 8 :=
  hasDerivAt_deBruijnNewman_adjacentSimpleZeroPath_realGapSq_and_deriv_le_eight
    hall hadj hxAnchor hyAnchor hx hy hxZero hyZero hxSimple hySimple

example {x y : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hall : ∀ t ∈ Set.Icc a b, deBruijnNewmanAllZerosReal t)
    (hadj : ∀ t ∈ Set.Icc a b,
      deBruijnNewmanAdjacentRealZeros t (x t).re (y t).re)
    (hxZero : ∀ t : ℝ, deBruijnNewmanH t (x t) = 0)
    (hyZero : ∀ t : ℝ, deBruijnNewmanH t (y t) = 0)
    (hxDiff : ∀ t ∈ Set.Icc a b, ∃ v : ℂ, HasDerivAt x v t)
    (hyDiff : ∀ t ∈ Set.Icc a b, ∃ v : ℂ, HasDerivAt y v t)
    (hxSimple : ∀ t ∈ Set.Icc a b, deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : ∀ t ∈ Set.Icc a b, deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    ((y b).re - (x b).re) ^ 2 - 8 * (b - a) ≤
      ((y a).re - (x a).re) ^ 2 :=
  deBruijnNewman_adjacentSimpleZeroPath_realGapSq_lower_bound
    hab hall hadj hxZero hyZero hxDiff hyDiff hxSimple hySimple

example (b epsilon t z : ℂ) :
    deriv (fun tau : ℂ ↦ h6GapAuditHeatPolynomial b epsilon tau z) t =
      -deriv (deriv (h6GapAuditHeatPolynomial b epsilon t)) z :=
  h6GapAuditHeatPolynomial_backwardHeatEquation b epsilon t z

example {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ^ 2 / 8 < delta ∧
      h6GapAuditHeatPolynomial 0 epsilon 0 (-epsilon / 2) = 0 ∧
      h6GapAuditHeatPolynomial 0 epsilon 0 (epsilon / 2) = 0 ∧
      deriv (h6GapAuditHeatPolynomial 0 epsilon 0) (-epsilon / 2) ≠ 0 ∧
      deriv (h6GapAuditHeatPolynomial 0 epsilon 0) (epsilon / 2) ≠ 0 ∧
      h6GapAuditHeatPolynomial 0 epsilon (h6GapAuditCollisionTime 0 epsilon) 0 = 0 ∧
      deriv (h6GapAuditHeatPolynomial 0 epsilon (h6GapAuditCollisionTime 0 epsilon)) 0 = 0 :=
  exists_h6GapAuditHeatPolynomial_collision_within hdelta

example {ι : Type*} [Fintype ι] (alpha : ι → ℂ)
    {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, ‖finiteComplexPowerSum alpha n‖ ≤ C * R ^ n) :
    ∀ i, ‖alpha i‖ ≤ R :=
  norm_le_of_forall_norm_finiteComplexPowerSum_le alpha hR hC hbound

example {ι : Type*} [Fintype ι] (alpha : ι → ℂ) (sigma : Equiv.Perm ι)
    {q C : ℝ} (hq : 0 < q) (hC : 0 ≤ C)
    (hpair : ∀ i, alpha (sigma i) * alpha i = (q : ℂ))
    (hbound : ∀ n : ℕ,
      ‖finiteComplexPowerSum alpha n‖ ≤ C * Real.sqrt q ^ n) :
    ∀ i, ‖alpha i‖ = Real.sqrt q :=
  norm_eq_sqrt_of_powerSum_bound_and_reciprocal alpha sigma hq hC hpair hbound

example :
    (∀ s : ℂ, Differentiable ℂ (fun t : ℂ ↦ h6AuditHeatXiQuadratic t s)) ∧
    (∀ t : ℂ, Differentiable ℂ (h6AuditHeatXiQuadratic t)) ∧
    (∀ t s : ℂ, h6AuditHeatXiQuadratic t (1 - s) = h6AuditHeatXiQuadratic t s) ∧
    (∀ t s : ℂ, deriv (fun u : ℂ ↦ h6AuditHeatXiQuadratic u s) t =
      (1 / 4) * deriv (deriv (h6AuditHeatXiQuadratic t)) s) ∧
    (∀ t : ℝ, 0 ≤ t → h6AuditHeatXiQuadratic t 1 ≠ 0) ∧
    (∀ s : ℂ, h6AuditHeatXiQuadratic 1 s = 0 → OnCriticalLine s) ∧
    (h6AuditHeatXiQuadratic 0 (3 / 4) = 0 ∧ ¬ OnCriticalLine (3 / 4 : ℂ)) ∧
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 0) = -64 / 9 ∧
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 1) = 448 / 121 :=
  h6AuditHeatXiQuadratic_falsifies_reverseLiTransfer

example (t : ℝ) (s : ℂ) :
    deBruijnNewmanHeatXi t (1 - s) = deBruijnNewmanHeatXi t s :=
  deBruijnNewmanHeatXi_one_sub t s

example (s : ℂ) : deBruijnNewmanHeatXi 0 s = riemannXi s :=
  deBruijnNewmanHeatXi_zero_eq_riemannXi s

example (t : ℝ) (s : ℂ) :
    deriv (fun tau : ℝ ↦ deBruijnNewmanHeatXi tau s) t =
      (1 / 4 : ℂ) * deriv (deriv (deBruijnNewmanHeatXi t)) s :=
  deBruijnNewmanHeatXi_heat_equation t s

example (t : ℝ) :
    deBruijnNewmanHeatXi t 1 ≠ 0 ∧
    deBruijnNewmanHeatLiOne t =
      ((2 * deBruijnNewmanHeatLiMomentB t / deBruijnNewmanHeatLiMomentA t : ℝ) : ℂ) ∧
    0 < (deBruijnNewmanHeatLiOne t).re ∧
    (deBruijnNewmanHeatLiOne t).im = 0 ∧
    deBruijnNewmanHeatLiMomentB t ^ 2 ≤
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t ∧
    deBruijnNewmanHeatLiTwo t =
      ((4 * (deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentB t +
        deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t -
        deBruijnNewmanHeatLiMomentB t ^ 2) /
        deBruijnNewmanHeatLiMomentA t ^ 2 : ℝ) : ℂ) ∧
    0 < (deBruijnNewmanHeatLiTwo t).re ∧
    (deBruijnNewmanHeatLiTwo t).im = 0 :=
  deBruijnNewmanHeat_firstTwoLi_endpoint t

example :
    (∀ t : ℝ, MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2) *
        deBruijnNewmanPhi u * Real.sinh u) (Set.Ioi 0)) ∧
    (∀ t : ℝ, deriv (deriv (deriv (deBruijnNewmanHeatXi t))) 1 =
      64 * (deBruijnNewmanHeatLiMomentD t : ℂ)) ∧
    (∀ t : ℝ, deBruijnNewmanHeatLiMomentB t *
      deBruijnNewmanHeatLiMomentC t ≤
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentD t) ∧
    (∀ t : ℝ, deBruijnNewmanHeatLiThree t =
      (((6 * deBruijnNewmanHeatLiMomentB t /
          deBruijnNewmanHeatLiMomentA t +
        12 * (deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t -
          (deBruijnNewmanHeatLiMomentB t /
            deBruijnNewmanHeatLiMomentA t) ^ 2) +
        4 * deBruijnNewmanHeatLiMomentD t /
          deBruijnNewmanHeatLiMomentA t -
        12 * deBruijnNewmanHeatLiMomentB t *
          deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t ^ 2 +
        8 * deBruijnNewmanHeatLiMomentB t ^ 3 /
          deBruijnNewmanHeatLiMomentA t ^ 3 : ℝ) : ℂ))) ∧
    deBruijnNewmanHeatLiThree 0 = liCoefficientCandidate 2 ∧
    0 < (liCoefficientCandidate 2).re ∧
    (liCoefficientCandidate 2).im = 0 :=
  deBruijnNewmanHeat_thirdLi_covariance_endpoint

example (t : ℝ) (n : ℕ) :
    deBruijnNewmanHeatLiCoefficient t n =
      ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        pairedLiZeroTerm (fun q : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
          deBruijnNewmanHeatXiDivisorZeroValue q) n p :=
  deBruijnNewmanHeatLiCoefficient_eq_tsum_pairedLiZeroTerm t n

example (t : ℝ) :
    deBruijnNewmanAllZerosReal t ↔
      ∀ n : ℕ, 0 ≤ (deBruijnNewmanHeatLiCoefficient t n).re :=
  deBruijnNewmanAllZerosReal_iff_forall_heatLiCoefficient_re_nonneg t

example (n : ℕ) :
    deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n :=
  deBruijnNewmanHeatLiCoefficient_zero_eq n

example :
    RiemannHypothesis ↔
      ∀ n : ℕ, 0 ≤ (deBruijnNewmanHeatLiCoefficient 0 n).re :=
  riemannHypothesis_iff_forall_deBruijnNewmanHeatLiCoefficient_zero_re_nonneg

example :
    (∀ n, deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n) ∧
    (∀ t : ℝ, 0 ≤ t →
      (deBruijnNewmanAllZerosReal t ↔
        ∀ n, 0 ≤ (deBruijnNewmanHeatLiCoefficient t n).re)) :=
  deBruijnNewmanHeat_allIndexLi_endpoint

example :
    Differentiable ℂ h6PositiveCoshAudit ∧
    (∀ s : ℂ, h6PositiveCoshAudit (1 - s) = h6PositiveCoshAudit s) ∧
    (0 < (1 / 8 : ℝ) / Real.cosh h6PositiveCoshAuditL ∧
      0 < (7 / 8 : ℝ) / Real.cosh (10 * h6PositiveCoshAuditL)) ∧
    h6PositiveCoshAudit 1 = 1 ∧
    h6PositiveCoshAuditLiOne =
      (2 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL : ℝ) ∧
    h6PositiveCoshAuditLiTwo =
      (4 * (h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
        (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL ^ 2) : ℝ) ∧
    h6PositiveCoshAuditLiThree =
      ((6 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditL +
        12 * (h6PositiveCoshAuditGamma - h6PositiveCoshAuditBeta ^ 2) *
          h6PositiveCoshAuditL ^ 2 +
        (4 * h6PositiveCoshAuditDelta -
          12 * h6PositiveCoshAuditBeta * h6PositiveCoshAuditGamma +
          8 * h6PositiveCoshAuditBeta ^ 3) * h6PositiveCoshAuditL ^ 3 : ℝ) : ℂ) ∧
    0 < h6PositiveCoshAuditLiOne.re ∧ h6PositiveCoshAuditLiOne.im = 0 ∧
    0 < h6PositiveCoshAuditLiTwo.re ∧ h6PositiveCoshAuditLiTwo.im = 0 ∧
    h6PositiveCoshAuditLiThree.re < 0 ∧ h6PositiveCoshAuditLiThree.im = 0 :=
  h6PositiveCoshAudit_falsifies_allOrder_positiveKernelLi

end LeanLab.Riemann
