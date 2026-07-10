import LeanLab.Riemann.BaezDuarteMellin
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# The weighted-log Fourier-Mellin isometry

This file packages the logarithmic change of variables that identifies
`L²(0, infinity)` with `L²(real line)` and then composes it with Fourier Plancherel.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LeanLab.Riemann

/-- The decreasing exponential parametrization of the positive half-line. -/
def expNeg (u : ℝ) : ℝ :=
  Real.exp (-u)

theorem expNeg_hasDerivWithinAt :
    ∀ u ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt expNeg (-Real.exp (-u)) Set.univ u := by
  intro u _hu
  change HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-u)) Set.univ u
  have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)
  simpa only [mul_neg, mul_one] using
    (h.hasDerivWithinAt : HasDerivWithinAt (Real.exp ∘ Neg.neg)
      (Real.exp (-u) * -1) Set.univ u)

theorem measurable_expNeg : Measurable expNeg := by
  change Measurable (Real.exp ∘ Neg.neg)
  fun_prop

theorem expNeg_image_univ :
    expNeg '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
  change (Real.exp ∘ Neg.neg) '' (Set.univ : Set ℝ) = Set.Ioi 0
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective,
    Set.image_univ, Real.range_exp]

theorem expNeg_injOn_univ :
    (Set.univ : Set ℝ).InjOn expNeg := by
  exact Real.exp_injective.injOn.comp neg_injective.injOn
    (Set.univ.mapsTo_univ _)

/-- Pulling back along `u ↦ exp(-u)` preserves almost-everywhere equality from
the positive half-line to the real line. -/
theorem expNeg_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving expNeg volume
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨measurable_expNeg, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply measurable_expNeg hs]
  have hchange :=
    lintegral_image_eq_lintegral_abs_deriv_mul
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      expNeg_hasDerivWithinAt expNeg_injOn_univ
      (s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
  have hleft :
      ∫⁻ x in expNeg '' (Set.univ : Set ℝ),
          s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) x = 0 := by
    rw [expNeg_image_univ]
    simpa [lintegral_indicator hs] using hs0
  have hright :
      ∫⁻ u in (Set.univ : Set ℝ),
          ENNReal.ofReal (|(-Real.exp (-u))|) *
            s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (expNeg u) = 0 := by
    rw [← hchange]
    exact hleft
  rw [Measure.restrict_univ] at hright
  have hzero :
      ∀ᵐ u : ℝ ∂volume,
        ENNReal.ofReal (|(-Real.exp (-u))|) *
          s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (expNeg u) = 0 := by
    apply (lintegral_eq_zero_iff' ?_).mp hright
    exact ((by fun_prop : Measurable fun u : ℝ =>
        ENNReal.ofReal (|(-Real.exp (-u))|)).mul
      ((measurable_const.indicator hs).comp measurable_expNeg)).aemeasurable
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hzero] with u hu
  intro hus
  have hus' : expNeg u ∈ s := hus
  have hweight : ENNReal.ofReal (|(-Real.exp (-u))|) ≠ 0 := by
    simp [Real.exp_pos]
  have hindicator :
      s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) (expNeg u) = 1 := by
    simp [hus']
  rw [hindicator, mul_one] at hu
  exact hweight hu

/-- Complex `L²` on the full real line. -/
abbrev realLineComplexL2 : Type :=
  Lp (α := ℝ) ℂ (2 : ℝ≥0∞) volume

/-- A representative of the weighted logarithmic pullback. -/
def weightedLogForwardFun (f : positiveHalfLineComplexL2) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) * f (expNeg u)

/-- A representative of the inverse weighted logarithmic pullback. -/
def weightedLogInverseFun (g : realLineComplexL2) (x : ℝ) : ℂ :=
  (Real.exp (-Real.log x / 2) : ℂ) * g (-Real.log x)

theorem weightedLogForwardFun_stronglyMeasurable
    (f : positiveHalfLineComplexL2) :
    StronglyMeasurable (weightedLogForwardFun f) := by
  exact (by fun_prop : StronglyMeasurable fun u : ℝ =>
      (Real.exp (-u / 2) : ℂ)).mul
    ((Lp.stronglyMeasurable f).comp_measurable measurable_expNeg)

theorem weightedLogInverseFun_stronglyMeasurable
    (g : realLineComplexL2) :
    StronglyMeasurable (weightedLogInverseFun g) := by
  exact (by fun_prop : StronglyMeasurable fun x : ℝ =>
      (Real.exp (-Real.log x / 2) : ℂ)).mul
    ((Lp.stronglyMeasurable g).comp_measurable Real.measurable_log.neg)

theorem weightedLogForwardFun_sq_norm
    (f : positiveHalfLineComplexL2) (u : ℝ) :
    ‖weightedLogForwardFun f u‖ ^ 2 =
      |(-Real.exp (-u))| • ‖f (expNeg u)‖ ^ 2 := by
  rw [weightedLogForwardFun, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, abs_neg,
    abs_of_pos (Real.exp_pos _), smul_eq_mul]
  congr 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem weightedLogInverseFun_sq_norm_after_expNeg
    (g : realLineComplexL2) (u : ℝ) :
    |(-Real.exp (-u))| • ‖weightedLogInverseFun g (expNeg u)‖ ^ 2 =
      ‖g u‖ ^ 2 := by
  rw [weightedLogInverseFun, expNeg, Real.log_exp, neg_neg, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    abs_neg, abs_of_pos (Real.exp_pos _), smul_eq_mul]
  have hexp : Real.exp (-u) * Real.exp (u / 2) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [← mul_assoc, hexp, one_mul]

theorem weightedLogForwardFun_integrable_sq_norm
    (f : positiveHalfLineComplexL2) :
    Integrable (fun u : ℝ => ‖weightedLogForwardFun f u‖ ^ 2) := by
  have hsource :
      IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2) (Set.Ioi 0) := by
    exact (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hchange :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      expNeg_hasDerivWithinAt expNeg_injOn_univ
      (fun x : ℝ => ‖f x‖ ^ 2)).mp (by
        rwa [expNeg_image_univ])
  rw [integrableOn_univ] at hchange
  exact hchange.congr (ae_of_all volume fun u =>
    (weightedLogForwardFun_sq_norm f u).symm)

theorem weightedLogInverseFun_integrable_sq_norm
    (g : realLineComplexL2) :
    IntegrableOn (fun x : ℝ => ‖weightedLogInverseFun g x‖ ^ 2)
      (Set.Ioi 0) := by
  have htarget : Integrable (fun u : ℝ => ‖g u‖ ^ 2) :=
    (Lp.memLp g).integrable_norm_pow (by norm_num)
  have hweighted :
      IntegrableOn
        (fun u : ℝ => |(-Real.exp (-u))| •
          ‖weightedLogInverseFun g (expNeg u)‖ ^ 2)
        Set.univ := by
    rw [integrableOn_univ]
    exact htarget.congr (ae_of_all volume fun u =>
      (weightedLogInverseFun_sq_norm_after_expNeg g u).symm)
  have hchange :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      expNeg_hasDerivWithinAt expNeg_injOn_univ
      (fun x : ℝ => ‖weightedLogInverseFun g x‖ ^ 2)).mpr hweighted
  rwa [expNeg_image_univ] at hchange

theorem weightedLogForwardFun_memLp
    (f : positiveHalfLineComplexL2) :
    MemLp (weightedLogForwardFun f) (2 : ℝ≥0∞) volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (weightedLogForwardFun_stronglyMeasurable f).aestronglyMeasurable]
  exact weightedLogForwardFun_integrable_sq_norm f

theorem weightedLogInverseFun_memLp
    (g : realLineComplexL2) :
    MemLp (weightedLogInverseFun g) (2 : ℝ≥0∞)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq_norm
    (weightedLogInverseFun_stronglyMeasurable g).aestronglyMeasurable]
  exact weightedLogInverseFun_integrable_sq_norm g

theorem integral_weightedLogForwardFun_sq_norm
    (f : positiveHalfLineComplexL2) :
    (∫ u : ℝ, ‖weightedLogForwardFun f u‖ ^ 2) =
      ∫ x : ℝ in Set.Ioi 0, ‖f x‖ ^ 2 := by
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      expNeg_hasDerivWithinAt expNeg_injOn_univ
      (fun x : ℝ => ‖f x‖ ^ 2)
  rw [expNeg_image_univ, setIntegral_univ] at hchange
  calc
    (∫ u : ℝ, ‖weightedLogForwardFun f u‖ ^ 2) =
        ∫ u : ℝ, |(-Real.exp (-u))| • ‖f (expNeg u)‖ ^ 2 :=
      integral_congr_ae (ae_of_all volume fun u =>
        weightedLogForwardFun_sq_norm f u)
    _ = ∫ x : ℝ in Set.Ioi 0, ‖f x‖ ^ 2 := hchange.symm

theorem integral_weightedLogInverseFun_sq_norm
    (g : realLineComplexL2) :
    (∫ x : ℝ in Set.Ioi 0, ‖weightedLogInverseFun g x‖ ^ 2) =
      ∫ u : ℝ, ‖g u‖ ^ 2 := by
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      expNeg_hasDerivWithinAt expNeg_injOn_univ
      (fun x : ℝ => ‖weightedLogInverseFun g x‖ ^ 2)
  rw [expNeg_image_univ, setIntegral_univ] at hchange
  calc
    (∫ x : ℝ in Set.Ioi 0, ‖weightedLogInverseFun g x‖ ^ 2) =
        ∫ u : ℝ, |(-Real.exp (-u))| •
          ‖weightedLogInverseFun g (expNeg u)‖ ^ 2 := hchange
    _ = ∫ u : ℝ, ‖g u‖ ^ 2 :=
      integral_congr_ae (ae_of_all volume fun u =>
        weightedLogInverseFun_sq_norm_after_expNeg g u)

theorem eLpNorm_weightedLogForwardFun
    (f : positiveHalfLineComplexL2) :
    eLpNorm (weightedLogForwardFun f) (2 : ℝ≥0∞) volume =
      eLpNorm f (2 : ℝ≥0∞) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [(weightedLogForwardFun_memLp f).eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num),
    (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [integral_weightedLogForwardFun_sq_norm]

theorem eLpNorm_weightedLogInverseFun
    (g : realLineComplexL2) :
    eLpNorm (weightedLogInverseFun g) (2 : ℝ≥0∞)
        (volume.restrict (Set.Ioi (0 : ℝ))) =
      eLpNorm g (2 : ℝ≥0∞) volume := by
  rw [(weightedLogInverseFun_memLp g).eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num),
    (Lp.memLp g).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [integral_weightedLogInverseFun_sq_norm]

/-- The weighted logarithmic pullback as an `L²` element. -/
def weightedLogForward (f : positiveHalfLineComplexL2) : realLineComplexL2 :=
  (weightedLogForwardFun_memLp f).toLp (weightedLogForwardFun f)

/-- The explicit inverse candidate as an `L²(0, infinity)` element. -/
def weightedLogInverse (g : realLineComplexL2) : positiveHalfLineComplexL2 :=
  (weightedLogInverseFun_memLp g).toLp (weightedLogInverseFun g)

theorem weightedLogForward_coeFn (f : positiveHalfLineComplexL2) :
    weightedLogForward f =ᵐ[volume] weightedLogForwardFun f := by
  exact MemLp.coeFn_toLp (weightedLogForwardFun_memLp f)

theorem weightedLogInverse_coeFn (g : realLineComplexL2) :
    weightedLogInverse g
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] weightedLogInverseFun g := by
  exact MemLp.coeFn_toLp (weightedLogInverseFun_memLp g)

theorem weightedLogForward_add
    (f g : positiveHalfLineComplexL2) :
    weightedLogForward (f + g) = weightedLogForward f + weightedLogForward g := by
  apply Lp.ext
  filter_upwards [weightedLogForward_coeFn (f + g),
    Lp.coeFn_add (weightedLogForward f) (weightedLogForward g),
    weightedLogForward_coeFn f, weightedLogForward_coeFn g,
    expNeg_quasiMeasurePreserving.ae_eq (Lp.coeFn_add f g)] with
      u hout hadd hf hg hsource
  rw [hout, hadd]
  change weightedLogForwardFun (f + g) u =
    weightedLogForward f u + weightedLogForward g u
  rw [hf, hg]
  change (Real.exp (-u / 2) : ℂ) * (f + g) (expNeg u) =
    (Real.exp (-u / 2) : ℂ) * f (expNeg u) +
      (Real.exp (-u / 2) : ℂ) * g (expNeg u)
  change (f + g) (expNeg u) = f (expNeg u) + g (expNeg u) at hsource
  rw [hsource, mul_add]

theorem weightedLogForward_smul
    (c : ℂ) (f : positiveHalfLineComplexL2) :
    weightedLogForward (c • f) = c • weightedLogForward f := by
  apply Lp.ext
  filter_upwards [weightedLogForward_coeFn (c • f),
    Lp.coeFn_smul c (weightedLogForward f), weightedLogForward_coeFn f,
    expNeg_quasiMeasurePreserving.ae_eq (Lp.coeFn_smul c f)] with
      u hout hsmul hf hsource
  rw [hout, hsmul]
  change weightedLogForwardFun (c • f) u = c • weightedLogForward f u
  rw [hf]
  change (Real.exp (-u / 2) : ℂ) * (c • f) (expNeg u) =
    c • ((Real.exp (-u / 2) : ℂ) * f (expNeg u))
  change (c • f) (expNeg u) = c • f (expNeg u) at hsource
  rw [hsource]
  simp only [smul_eq_mul]
  ring

/-- The weighted logarithmic pullback as a complex-linear map. -/
def weightedLogForwardLinearMap :
    positiveHalfLineComplexL2 →ₗ[ℂ] realLineComplexL2 where
  toFun := weightedLogForward
  map_add' := weightedLogForward_add
  map_smul' := weightedLogForward_smul

theorem norm_weightedLogForward (f : positiveHalfLineComplexL2) :
    ‖weightedLogForward f‖ = ‖f‖ := by
  rw [weightedLogForward, Lp.norm_toLp, Lp.norm_def,
    eLpNorm_weightedLogForwardFun]

/-- The weighted logarithmic pullback as a complex-linear isometry. -/
def weightedLogForwardLinearIsometry :
    positiveHalfLineComplexL2 →ₗᵢ[ℂ] realLineComplexL2 where
  toLinearMap := weightedLogForwardLinearMap
  norm_map' := norm_weightedLogForward

theorem weightedLogForward_inverse
    (g : realLineComplexL2) :
    weightedLogForward (weightedLogInverse g) = g := by
  apply Lp.ext
  filter_upwards [weightedLogForward_coeFn (weightedLogInverse g),
    expNeg_quasiMeasurePreserving.ae_eq (weightedLogInverse_coeFn g)] with
      u hout hinverse
  rw [hout]
  change (Real.exp (-u / 2) : ℂ) *
    weightedLogInverse g (expNeg u) = g u
  change weightedLogInverse g (expNeg u) =
    weightedLogInverseFun g (expNeg u) at hinverse
  rw [hinverse, weightedLogInverseFun, expNeg, Real.log_exp, neg_neg]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  have hzero : -(u : ℂ) / 2 + (u : ℂ) / 2 = 0 := by ring
  rw [hzero, Complex.exp_zero, one_mul]

theorem weightedLogForward_surjective :
    Function.Surjective weightedLogForward := by
  intro g
  exact ⟨weightedLogInverse g, weightedLogForward_inverse g⟩

/-- The weighted logarithmic change of variables as a complex-linear isometric
equivalence from `L²(0, infinity)` to `L²(real line)`. -/
noncomputable def weightedLogPullback :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 :=
  LinearIsometryEquiv.ofSurjective weightedLogForwardLinearIsometry
    weightedLogForward_surjective

theorem weightedLogPullback_apply (f : positiveHalfLineComplexL2) :
    weightedLogPullback f = weightedLogForward f := by
  rfl

theorem weightedLogPullback_coeFn (f : positiveHalfLineComplexL2) :
    weightedLogPullback f =ᵐ[volume]
      fun u : ℝ => (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u)) := by
  filter_upwards [weightedLogForward_coeFn f] with u hu
  rw [weightedLogPullback_apply, hu]
  rfl

theorem weightedLogPullback_symm_eq_inverse (g : realLineComplexL2) :
    weightedLogPullback.symm g = weightedLogInverse g := by
  have hforward : weightedLogPullback (weightedLogInverse g) = g := by
    rw [weightedLogPullback_apply]
    exact weightedLogForward_inverse g
  calc
    weightedLogPullback.symm g =
        weightedLogPullback.symm (weightedLogPullback (weightedLogInverse g)) := by
      rw [hforward]
    _ = weightedLogInverse g := weightedLogPullback.symm_apply_apply _

theorem weightedLogPullback_symm_coeFn_expLog (g : realLineComplexL2) :
    weightedLogPullback.symm g
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => (Real.exp (-Real.log x / 2) : ℂ) * g (-Real.log x) := by
  rw [weightedLogPullback_symm_eq_inverse]
  exact weightedLogInverse_coeFn g

theorem weightedLogPullback_symm_coeFn (g : realLineComplexL2) :
    weightedLogPullback.symm g
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => ((x ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * g (-Real.log x) := by
  filter_upwards [weightedLogPullback_symm_coeFn_expLog g,
    ae_restrict_mem measurableSet_Ioi] with x hx hxpos
  rw [hx, Real.rpow_def_of_pos hxpos]
  congr 2
  ring_nf

/-- The Fourier-Mellin `L²` isometry in Baez-Duarte's normalization, before
the pointwise frequency rescaling `tau ↦ tau / (2*pi)`. -/
noncomputable def baezDuarteFourierMellinL2 :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 :=
  weightedLogPullback.trans (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)

theorem norm_baezDuarteFourierMellinL2
    (f : positiveHalfLineComplexL2) :
    ‖baezDuarteFourierMellinL2 f‖ = ‖f‖ := by
  exact baezDuarteFourierMellinL2.norm_map f

/-- On the critical line, mathlib's Mellin-to-Fourier change of variables uses
Fourier frequency `tau / (2*pi)`. -/
theorem mellin_criticalLine_eq_fourier
    (f : ℝ → ℂ) (τ : ℝ) :
    mellin f ((1 / 2 : ℂ) + τ * Complex.I) =
      𝓕 (fun u : ℝ =>
        (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u)))
        (τ / (2 * Real.pi)) := by
  have hre : ((1 / 2 : ℂ) + τ * Complex.I).re = 1 / 2 := by
    norm_num
  have him : ((1 / 2 : ℂ) + τ * Complex.I).im = τ := by
    simp
  rw [mellin_eq_fourier, hre, him]
  apply congrArg (fun h : ℝ → ℂ => 𝓕 h (τ / (2 * Real.pi)))
  funext u
  change (Real.exp (-(1 / 2) * u) : ℂ) * f (Real.exp (-u)) =
    (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u))
  congr 2
  ring_nf

end LeanLab.Riemann
