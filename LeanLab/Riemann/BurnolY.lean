import LeanLab.Riemann.BurnolHardy
import LeanLab.Riemann.BaezDuarteZetaRatio
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Burnol's boundary vectors

This file formalizes the second phase operator and the boundary vectors used in Burnol's
quantitative lower bound.  This operator is the phase of the Mellin transform of `burnolA`; it is
not the Hardy averaging inverse constructed in `BurnolHardy`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal FourierTransform NNReal Topology

namespace LeanLab.Riemann

/-- The Mellin transform of Burnol's explicit source function `A`. -/
def burnolZ (s : ℂ) : ℂ :=
  (s - 1) * riemannZeta s / s ^ 2

/-- `burnolZ` restricted to the Fourier--Mellin critical line. -/
def burnolZOnCriticalLine (xi : ℝ) : ℂ :=
  burnolZ (burnolCriticalLineAtFrequency xi)

theorem continuous_burnolZOnCriticalLine :
    Continuous burnolZOnCriticalLine := by
  rw [continuous_iff_continuousAt]
  intro xi
  have hs0 : burnolCriticalLineAtFrequency xi ≠ 0 :=
    burnolCriticalLineAtFrequency_ne_zero xi
  have hs1 : burnolCriticalLineAtFrequency xi ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [burnolCriticalLineAtFrequency] at hre
  have hs : ContinuousAt burnolCriticalLineAtFrequency xi :=
    continuous_burnolCriticalLineAtFrequency.continuousAt
  have hzeta := (differentiableAt_riemannZeta hs1).continuousAt.comp hs
  change ContinuousAt (fun x =>
    (burnolCriticalLineAtFrequency x - 1) *
      riemannZeta (burnolCriticalLineAtFrequency x) /
        burnolCriticalLineAtFrequency x ^ 2) xi
  exact ((hs.sub continuousAt_const).mul hzeta).div (hs.pow 2) (pow_ne_zero 2 hs0)

/-- Burnol's second phase, totalized at zeros of `Z` by the value `1`. -/
def burnolAPhaseMultiplier (xi : ℝ) : ℂ :=
  if burnolZOnCriticalLine xi = 0 then 1
  else (starRingEnd ℂ) (burnolZOnCriticalLine xi) / burnolZOnCriticalLine xi

theorem measurable_burnolAPhaseMultiplier :
    Measurable burnolAPhaseMultiplier := by
  exact Measurable.ite
    (measurableSet_eq_fun continuous_burnolZOnCriticalLine.measurable measurable_const)
    measurable_const
    (Complex.continuous_conj.measurable.comp continuous_burnolZOnCriticalLine.measurable |>.div
      continuous_burnolZOnCriticalLine.measurable)

theorem norm_burnolAPhaseMultiplier (xi : ℝ) :
    ‖burnolAPhaseMultiplier xi‖ = 1 := by
  by_cases hZ : burnolZOnCriticalLine xi = 0
  · simp [burnolAPhaseMultiplier, hZ]
  · rw [burnolAPhaseMultiplier, if_neg hZ, norm_div, Complex.norm_conj]
    exact div_self (norm_ne_zero_iff.mpr hZ)

theorem star_burnolCriticalLineAtFrequency (xi : ℝ) :
    (starRingEnd ℂ) (burnolCriticalLineAtFrequency xi) =
      1 - burnolCriticalLineAtFrequency xi := by
  apply Complex.ext
  · simp [burnolCriticalLineAtFrequency]
    ring_nf
  · simp [burnolCriticalLineAtFrequency]

theorem burnolCriticalLineAtFrequency_injective :
    Function.Injective burnolCriticalLineAtFrequency := by
  intro xi eta h
  have him := congrArg Complex.im h
  simp [burnolCriticalLineAtFrequency] at him
  nlinarith [Real.pi_pos]

/-- Frequencies at which the critical-line zeta factor vanishes. -/
def burnolCriticalLineZetaZeroFrequencies : Set ℝ :=
  {xi | riemannZeta (burnolCriticalLineAtFrequency xi) = 0}

theorem burnolCriticalLineZetaZeroFrequencies_countable :
    burnolCriticalLineZetaZeroFrequencies.Countable := by
  have hpreimage :=
    riemannZetaZeros_countable.preimage burnolCriticalLineAtFrequency_injective
  change (burnolCriticalLineAtFrequency ⁻¹' riemannZetaZeros).Countable
  exact hpreimage

theorem burnolCriticalLineZetaZeroFrequencies_measure_zero :
    volume burnolCriticalLineZetaZeroFrequencies = 0 :=
  burnolCriticalLineZetaZeroFrequencies_countable.measure_zero volume

theorem ae_riemannZeta_burnolCriticalLineAtFrequency_ne_zero :
    ∀ᵐ xi : ℝ ∂volume,
      riemannZeta (burnolCriticalLineAtFrequency xi) ≠ 0 := by
  simpa only [burnolCriticalLineZetaZeroFrequencies, Set.mem_setOf_eq] using
    (measure_eq_zero_iff_ae_notMem.mp
      burnolCriticalLineZetaZeroFrequencies_measure_zero)

theorem burnolZOnCriticalLine_ne_zero_of_riemannZeta_ne_zero
    (xi : ℝ) (hzeta : riemannZeta (burnolCriticalLineAtFrequency xi) ≠ 0) :
    burnolZOnCriticalLine xi ≠ 0 := by
  have hs0 := burnolCriticalLineAtFrequency_ne_zero xi
  have hs1 : burnolCriticalLineAtFrequency xi ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [burnolCriticalLineAtFrequency] at hre
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hs1) hzeta) (pow_ne_zero 2 hs0)

theorem star_burnolZOnCriticalLine (xi : ℝ) :
    (starRingEnd ℂ) (burnolZOnCriticalLine xi) =
      (-burnolCriticalLineAtFrequency xi) *
          riemannZeta (1 - burnolCriticalLineAtFrequency xi) /
        (1 - burnolCriticalLineAtFrequency xi) ^ 2 := by
  simp only [burnolZOnCriticalLine, burnolZ, map_div₀, map_mul, map_sub, map_one,
    map_pow, ← riemannZeta_conj, star_burnolCriticalLineAtFrequency]
  ring

/-- Away from zeta zeros, the total phase agrees with Burnol's source quotient. -/
theorem burnolAPhaseMultiplier_eq_source (xi : ℝ)
    (hzeta : riemannZeta (burnolCriticalLineAtFrequency xi) ≠ 0) :
    burnolAPhaseMultiplier xi =
      (burnolCriticalLineAtFrequency xi /
          (1 - burnolCriticalLineAtFrequency xi)) ^ 3 *
        (riemannZeta (1 - burnolCriticalLineAtFrequency xi) /
          riemannZeta (burnolCriticalLineAtFrequency xi)) := by
  have hs0 := burnolCriticalLineAtFrequency_ne_zero xi
  have hs1 : burnolCriticalLineAtFrequency xi ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [burnolCriticalLineAtFrequency] at hre
  have h1s0 : 1 - burnolCriticalLineAtFrequency xi ≠ 0 :=
    sub_ne_zero.mpr hs1.symm
  have hsSub : burnolCriticalLineAtFrequency xi - 1 ≠ 0 :=
    sub_ne_zero.mpr hs1
  rw [burnolAPhaseMultiplier,
    if_neg (burnolZOnCriticalLine_ne_zero_of_riemannZeta_ne_zero xi hzeta),
    star_burnolZOnCriticalLine, burnolZOnCriticalLine, burnolZ]
  field_simp [hs0, hsSub, h1s0, hzeta]
  ring

theorem ae_burnolAPhaseMultiplier_eq_source :
    ∀ᵐ xi : ℝ ∂volume,
      burnolAPhaseMultiplier xi =
        (burnolCriticalLineAtFrequency xi /
            (1 - burnolCriticalLineAtFrequency xi)) ^ 3 *
          (riemannZeta (1 - burnolCriticalLineAtFrequency xi) /
            riemannZeta (burnolCriticalLineAtFrequency xi)) := by
  filter_upwards [ae_riemannZeta_burnolCriticalLineAtFrequency_ne_zero] with xi hzeta
  exact burnolAPhaseMultiplier_eq_source xi hzeta

/-- The conjugate phase is the pointwise inverse of `burnolAPhaseMultiplier`. -/
def burnolAPhaseMultiplierInv (xi : ℝ) : ℂ :=
  (starRingEnd ℂ) (burnolAPhaseMultiplier xi)

theorem measurable_burnolAPhaseMultiplierInv :
    Measurable burnolAPhaseMultiplierInv := by
  exact Complex.continuous_conj.measurable.comp measurable_burnolAPhaseMultiplier

theorem norm_burnolAPhaseMultiplierInv (xi : ℝ) :
    ‖burnolAPhaseMultiplierInv xi‖ = 1 := by
  rw [burnolAPhaseMultiplierInv, Complex.norm_conj, norm_burnolAPhaseMultiplier]

theorem burnolAPhaseMultiplierInv_mul (xi : ℝ) :
    burnolAPhaseMultiplierInv xi * burnolAPhaseMultiplier xi = 1 := by
  rw [burnolAPhaseMultiplierInv, Complex.conj_mul', norm_burnolAPhaseMultiplier]
  norm_num

theorem burnolAPhaseMultiplier_mul_inv (xi : ℝ) :
    burnolAPhaseMultiplier xi * burnolAPhaseMultiplierInv xi = 1 := by
  rw [mul_comm, burnolAPhaseMultiplierInv_mul]

theorem burnolAPhaseMultiplier_memLp_top :
    MemLp burnolAPhaseMultiplier ∞ volume := by
  refine memLp_top_of_bound measurable_burnolAPhaseMultiplier.aestronglyMeasurable 1 ?_
  exact ae_of_all volume fun xi => (norm_burnolAPhaseMultiplier xi).le

theorem burnolAPhaseMultiplierInv_memLp_top :
    MemLp burnolAPhaseMultiplierInv ∞ volume := by
  refine memLp_top_of_bound measurable_burnolAPhaseMultiplierInv.aestronglyMeasurable 1 ?_
  exact ae_of_all volume fun xi => (norm_burnolAPhaseMultiplierInv xi).le

def burnolAPhaseMultiplierLInf : Lp (α := ℝ) ℂ ∞ volume :=
  burnolAPhaseMultiplier_memLp_top.toLp burnolAPhaseMultiplier

theorem burnolAPhaseMultiplierLInf_coeFn :
    burnolAPhaseMultiplierLInf =ᵐ[volume] burnolAPhaseMultiplier := by
  exact MemLp.coeFn_toLp burnolAPhaseMultiplier_memLp_top

def burnolAPhaseMultiplierInvLInf : Lp (α := ℝ) ℂ ∞ volume :=
  burnolAPhaseMultiplierInv_memLp_top.toLp burnolAPhaseMultiplierInv

theorem burnolAPhaseMultiplierInvLInf_coeFn :
    burnolAPhaseMultiplierInvLInf =ᵐ[volume] burnolAPhaseMultiplierInv := by
  exact MemLp.coeFn_toLp burnolAPhaseMultiplierInv_memLp_top

theorem burnolAPhaseFrequency_left_inv (g : realLineComplexL2) :
    burnolAPhaseMultiplierInvLInf •
        (burnolAPhaseMultiplierLInf • g : realLineComplexL2) = g := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolAPhaseMultiplierInvLInf
      (burnolAPhaseMultiplierLInf • g : realLineComplexL2),
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolAPhaseMultiplierLInf g,
    burnolAPhaseMultiplierInvLInf_coeFn,
    burnolAPhaseMultiplierLInf_coeFn] with xi hout hin hinv hphase
  rw [hout]
  change burnolAPhaseMultiplierInvLInf xi *
    (burnolAPhaseMultiplierLInf • g : realLineComplexL2) xi = g xi
  rw [hinv, hin]
  change burnolAPhaseMultiplierInv xi *
    (burnolAPhaseMultiplierLInf xi * g xi) = g xi
  rw [hphase, ← mul_assoc, burnolAPhaseMultiplierInv_mul, one_mul]

theorem burnolAPhaseFrequency_right_inv (g : realLineComplexL2) :
    burnolAPhaseMultiplierLInf •
        (burnolAPhaseMultiplierInvLInf • g : realLineComplexL2) = g := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolAPhaseMultiplierLInf
      (burnolAPhaseMultiplierInvLInf • g : realLineComplexL2),
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolAPhaseMultiplierInvLInf g,
    burnolAPhaseMultiplierLInf_coeFn,
    burnolAPhaseMultiplierInvLInf_coeFn] with xi hout hin hphase hinv
  rw [hout]
  change burnolAPhaseMultiplierLInf xi *
    (burnolAPhaseMultiplierInvLInf • g : realLineComplexL2) xi = g xi
  rw [hphase, hin]
  change burnolAPhaseMultiplier xi *
    (burnolAPhaseMultiplierInvLInf xi * g xi) = g xi
  rw [hinv, ← mul_assoc, burnolAPhaseMultiplier_mul_inv, one_mul]

def burnolAPhaseFrequencyLinearEquiv :
    realLineComplexL2 ≃ₗ[ℂ] realLineComplexL2 where
  toFun g := burnolAPhaseMultiplierLInf • g
  invFun g := burnolAPhaseMultiplierInvLInf • g
  map_add' g h := Lp.add_smul burnolAPhaseMultiplierLInf g h
  map_smul' c g := (Lp.smul_comm c burnolAPhaseMultiplierLInf g).symm
  left_inv := burnolAPhaseFrequency_left_inv
  right_inv := burnolAPhaseFrequency_right_inv

theorem norm_burnolAPhaseFrequency (g : realLineComplexL2) :
    ‖(burnolAPhaseMultiplierLInf • g : realLineComplexL2)‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolAPhaseMultiplierLInf g,
    burnolAPhaseMultiplierLInf_coeFn] with xi hmul hphase
  rw [hmul]
  change ‖burnolAPhaseMultiplierLInf xi * g xi‖ = ‖g xi‖
  rw [hphase, norm_mul, norm_burnolAPhaseMultiplier, one_mul]

/-- Multiplication by Burnol's second phase on frequency `L2`. -/
def burnolAPhaseFrequencyL2 :
    realLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 where
  toLinearEquiv := burnolAPhaseFrequencyLinearEquiv
  norm_map' := norm_burnolAPhaseFrequency

theorem burnolAPhaseFrequencyL2_apply (g : realLineComplexL2) :
    burnolAPhaseFrequencyL2 g = burnolAPhaseMultiplierLInf • g :=
  rfl

/-- Burnol's second phase transported to complex `L2(0,infinity)`. -/
def burnolAPhaseL2 :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] positiveHalfLineComplexL2 :=
  baezDuarteFourierMellinL2.trans
    (burnolAPhaseFrequencyL2.trans baezDuarteFourierMellinL2.symm)

theorem baezDuarteFourierMellinL2_burnolAPhaseL2
    (f : positiveHalfLineComplexL2) :
    baezDuarteFourierMellinL2 (burnolAPhaseL2 f) =
      burnolAPhaseFrequencyL2 (baezDuarteFourierMellinL2 f) := by
  simp [burnolAPhaseL2]

/-- Reflection on real-line `L2`, represented by `g(u) -> g(-u)`. -/
def burnolReflectRealLineL2 (g : realLineComplexL2) : realLineComplexL2 :=
  Lp.compMeasurePreserving (Neg.neg : ℝ → ℝ)
    (Measure.measurePreserving_neg volume) g

theorem burnolReflectRealLineL2_coeFn (g : realLineComplexL2) :
    burnolReflectRealLineL2 g =ᵐ[volume] fun u : ℝ => g (-u) := by
  unfold burnolReflectRealLineL2
  convert Lp.coeFn_compMeasurePreserving g (Measure.measurePreserving_neg volume) using 1
  funext u
  rfl

theorem burnolReflectRealLineL2_involutive (g : realLineComplexL2) :
    burnolReflectRealLineL2 (burnolReflectRealLineL2 g) = g := by
  apply Lp.ext
  have hneg := Measure.measurePreserving_neg (volume : Measure ℝ)
  filter_upwards [burnolReflectRealLineL2_coeFn (burnolReflectRealLineL2 g),
    hneg.quasiMeasurePreserving.ae_eq (burnolReflectRealLineL2_coeFn g)] with u hout hin
  have hin' : burnolReflectRealLineL2 g (-u) = g (-(-u)) := by
    simpa only [Function.comp_apply] using hin
  rw [hout, hin']
  simp

def burnolReflectRealLineLinearEquiv :
    realLineComplexL2 ≃ₗ[ℂ] realLineComplexL2 where
  toFun := burnolReflectRealLineL2
  invFun := burnolReflectRealLineL2
  map_add' g h := by
    exact map_add
      (Lp.compMeasurePreservingₗ ℂ (Neg.neg : ℝ → ℝ)
        (Measure.measurePreserving_neg volume)) g h
  map_smul' c g := by
    exact map_smul
      (Lp.compMeasurePreservingₗ ℂ (Neg.neg : ℝ → ℝ)
        (Measure.measurePreserving_neg volume)) c g
  left_inv := burnolReflectRealLineL2_involutive
  right_inv := burnolReflectRealLineL2_involutive

theorem norm_burnolReflectRealLineL2 (g : realLineComplexL2) :
    ‖burnolReflectRealLineL2 g‖ = ‖g‖ := by
  exact Lp.norm_compMeasurePreserving g (Measure.measurePreserving_neg volume)

/-- Reflection as a complex-linear `L2` isometric equivalence. -/
def burnolReflectRealLineL2Equiv :
    realLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 where
  toLinearEquiv := burnolReflectRealLineLinearEquiv
  norm_map' := norm_burnolReflectRealLineL2

/-- Physical time reversal `J f(t) = t^(-1) f(t^(-1))`, defined through logarithmic
coordinates. -/
def burnolTimeReverseL2 :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] positiveHalfLineComplexL2 :=
  weightedLogPullback.trans
    (burnolReflectRealLineL2Equiv.trans weightedLogPullback.symm)

theorem weightedLogPullback_burnolTimeReverseL2
    (f : positiveHalfLineComplexL2) :
    weightedLogPullback (burnolTimeReverseL2 f) =
      burnolReflectRealLineL2Equiv (weightedLogPullback f) := by
  simp [burnolTimeReverseL2]

/-- The inverse logarithmic coordinate on the positive half-line. -/
def burnolNegLog (t : ℝ) : ℝ :=
  -Real.log t

theorem measurable_burnolNegLog : Measurable burnolNegLog := by
  exact Real.measurable_log.neg

theorem burnolNegLog_preimage_inter_positive (s : Set ℝ) :
    burnolNegLog ⁻¹' s ∩ Ioi (0 : ℝ) = expNeg '' s := by
  ext t
  constructor
  · rintro ⟨hts, htpos⟩
    refine ⟨burnolNegLog t, hts, ?_⟩
    simp [burnolNegLog, expNeg, Real.exp_log htpos]
  · rintro ⟨u, hu, rfl⟩
    constructor
    · simpa [burnolNegLog, expNeg] using hu
    · exact Real.exp_pos _

/-- Pullback along `t -> -log t` preserves almost-everywhere equality from the real line to the
positive half-line. -/
theorem burnolNegLog_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving burnolNegLog
      (volume.restrict (Ioi (0 : ℝ))) volume := by
  refine ⟨measurable_burnolNegLog, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply measurable_burnolNegLog hs,
    Measure.restrict_apply (measurable_burnolNegLog hs),
    burnolNegLog_preimage_inter_positive]
  have hderiv : ∀ u ∈ s,
      HasDerivWithinAt expNeg (-Real.exp (-u)) s u := by
    intro u hu
    exact (expNeg_hasDerivWithinAt u (Set.mem_univ u)).mono (subset_univ s)
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul hs hderiv
    (expNeg_injOn_univ.mono (subset_univ s)) (fun _ : ℝ => (1 : ℝ≥0∞))
  have hright :
      (∫⁻ u : ℝ in s,
        ENNReal.ofReal (|-Real.exp (-u)|) * (1 : ℝ≥0∞)) = 0 := by
    exact setLIntegral_measure_zero s _ hs0
  rw [hright] at hchange
  simpa using hchange

theorem burnolTimeReverseL2_coeFn (f : positiveHalfLineComplexL2) :
    burnolTimeReverseL2 f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t : ℝ => (t⁻¹ : ℂ) * f t⁻¹ := by
  let g := weightedLogPullback f
  have hlogQMP :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.comp
      burnolNegLog_quasiMeasurePreserving
  have hreflect := burnolNegLog_quasiMeasurePreserving.ae_eq
    (burnolReflectRealLineL2_coeFn g)
  have hforward := hlogQMP.ae_eq (weightedLogPullback_coeFn f)
  filter_upwards [weightedLogPullback_symm_coeFn (burnolReflectRealLineL2Equiv g),
    hreflect, hforward, ae_restrict_mem measurableSet_Ioi] with t hout href hfor ht
  change weightedLogPullback.symm (burnolReflectRealLineL2Equiv g) t =
    (t⁻¹ : ℂ) * f t⁻¹
  rw [hout]
  have href' : burnolReflectRealLineL2 g (burnolNegLog t) =
      g (-burnolNegLog t) := by
    simpa only [Function.comp_apply] using href
  have hfor' : g (-burnolNegLog t) =
      (Real.exp (-(-burnolNegLog t) / 2) : ℂ) *
        f (Real.exp (-(-burnolNegLog t))) := by
    simpa only [Function.comp_apply] using hfor
  change ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      burnolReflectRealLineL2 g (burnolNegLog t) = (t⁻¹ : ℂ) * f t⁻¹
  rw [href', hfor']
  simp only [burnolNegLog, neg_neg]
  have hhalf : Real.exp (-Real.log t / 2) = t ^ (-1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  have hexpInv : Real.exp (-Real.log t) = t⁻¹ := by
    rw [Real.exp_neg, Real.exp_log ht]
  rw [hhalf, hexpInv]
  have hrpow : t ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) = t⁻¹ := by
    rw [← Real.rpow_add ht]
    norm_num
    rw [Real.rpow_neg_one]
  calc
    ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        (((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * f t⁻¹) =
      ((t ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * f t⁻¹ := by
        push_cast
        ring
    _ = (t⁻¹ : ℂ) * f t⁻¹ := by rw [hrpow, Complex.ofReal_inv]

/-- The unit endpoint of Burnol's continuous parameter interval. -/
def burnolUnitParameter : burnolContinuousParameter :=
  ⟨1, by norm_num⟩

theorem burnolModelKernelL2_unit_eq_A :
    burnolModelKernelL2 burnolUnitParameter = burnolComplexAL2 := by
  apply Lp.ext
  filter_upwards [burnolModelKernelL2_coeFn burnolUnitParameter,
    burnolComplexAL2_coeFn] with t hmodel hA
  rw [hmodel, hA]
  simp [burnolUnitParameter]

theorem burnolModelKernelTransform_unit (xi : ℝ) :
    burnolModelKernelTransform burnolUnitParameter xi = burnolZOnCriticalLine xi := by
  simp [burnolModelKernelTransform, burnolDilationFactor, burnolUnitParameter,
    burnolZOnCriticalLine, burnolZ]

theorem burnolZOnCriticalLine_memLp :
    MemLp burnolZOnCriticalLine (2 : ℝ≥0∞) volume := by
  exact (burnolModelKernelTransform_memLp burnolUnitParameter).ae_eq
    (ae_of_all volume burnolModelKernelTransform_unit)

theorem baezDuarteFourierMellinL2_burnolComplexAL2 :
    baezDuarteFourierMellinL2 burnolComplexAL2 =
      burnolZOnCriticalLine_memLp.toLp burnolZOnCriticalLine := by
  rw [← burnolModelKernelL2_unit_eq_A,
    baezDuarteFourierMellinL2_modelKernel_eq]
  exact MemLp.toLp_congr (burnolModelKernelTransform_memLp burnolUnitParameter)
    burnolZOnCriticalLine_memLp (ae_of_all volume burnolModelKernelTransform_unit)

/-- The conjugate critical-line representative of `Z`. -/
def burnolZConjOnCriticalLine (xi : ℝ) : ℂ :=
  (starRingEnd ℂ) (burnolZOnCriticalLine xi)

theorem burnolZConjOnCriticalLine_memLp :
    MemLp burnolZConjOnCriticalLine (2 : ℝ≥0∞) volume := by
  refine burnolZOnCriticalLine_memLp.of_le
    (Complex.continuous_conj.measurable.comp
      continuous_burnolZOnCriticalLine.measurable).aestronglyMeasurable ?_
  exact ae_of_all volume fun xi => by
    rw [burnolZConjOnCriticalLine, Complex.norm_conj]

theorem burnolAPhaseMultiplier_mul_Z (xi : ℝ) :
    burnolAPhaseMultiplier xi * burnolZOnCriticalLine xi =
      burnolZConjOnCriticalLine xi := by
  by_cases hZ : burnolZOnCriticalLine xi = 0
  · simp [burnolAPhaseMultiplier, burnolZConjOnCriticalLine, hZ]
  · rw [burnolAPhaseMultiplier, if_neg hZ, burnolZConjOnCriticalLine]
    exact div_mul_cancel₀ _ hZ

theorem burnolAPhaseFrequencyL2_Z :
    burnolAPhaseFrequencyL2
        (burnolZOnCriticalLine_memLp.toLp burnolZOnCriticalLine) =
      burnolZConjOnCriticalLine_memLp.toLp burnolZConjOnCriticalLine := by
  rw [burnolAPhaseFrequencyL2_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolAPhaseMultiplierLInf
      (burnolZOnCriticalLine_memLp.toLp burnolZOnCriticalLine),
    burnolAPhaseMultiplierLInf_coeFn,
    MemLp.coeFn_toLp burnolZOnCriticalLine_memLp,
    MemLp.coeFn_toLp burnolZConjOnCriticalLine_memLp] with
      xi hmul hphase hZ hconj
  rw [hmul]
  change burnolAPhaseMultiplierLInf xi *
      (burnolZOnCriticalLine_memLp.toLp burnolZOnCriticalLine) xi =
    (burnolZConjOnCriticalLine_memLp.toLp burnolZConjOnCriticalLine) xi
  rw [hphase, hZ, hconj]
  exact burnolAPhaseMultiplier_mul_Z xi

theorem baezDuarteFourierMellinL2_burnolAPhaseL2_A :
    baezDuarteFourierMellinL2 (burnolAPhaseL2 burnolComplexAL2) =
      burnolZConjOnCriticalLine_memLp.toLp burnolZConjOnCriticalLine := by
  rw [baezDuarteFourierMellinL2_burnolAPhaseL2,
    baezDuarteFourierMellinL2_burnolComplexAL2,
    burnolAPhaseFrequencyL2_Z]

theorem burnolCriticalLineAtFrequency_neg (xi : ℝ) :
    burnolCriticalLineAtFrequency (-xi) =
      (starRingEnd ℂ) (burnolCriticalLineAtFrequency xi) := by
  apply Complex.ext
  · simp [burnolCriticalLineAtFrequency]
  · simp [burnolCriticalLineAtFrequency]

theorem burnolZOnCriticalLine_neg (xi : ℝ) :
    burnolZOnCriticalLine (-xi) = burnolZConjOnCriticalLine xi := by
  rw [burnolZOnCriticalLine, burnolCriticalLineAtFrequency_neg,
    burnolZConjOnCriticalLine, burnolZOnCriticalLine]
  simp only [burnolZ, map_div₀, map_mul, map_sub, map_one, map_pow,
    ← riemannZeta_conj]

/-- The weighted logarithmic representative of the physical time reversal of `A`. -/
def burnolAReflectedWeightedLog (u : ℝ) : ℂ :=
  burnolModelKernelWeightedLog burnolUnitParameter (-u)

theorem burnolAReflectedWeightedLog_integrable :
    Integrable burnolAReflectedWeightedLog := by
  change Integrable
    (burnolModelKernelWeightedLog burnolUnitParameter ∘ (Neg.neg : ℝ → ℝ))
  exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable
    (burnolModelKernelWeightedLog_integrable burnolUnitParameter)

theorem burnolAReflectedWeightedLog_memLp :
    MemLp burnolAReflectedWeightedLog (2 : ℝ≥0∞) volume := by
  change MemLp
    (burnolModelKernelWeightedLog burnolUnitParameter ∘ (Neg.neg : ℝ → ℝ))
    (2 : ℝ≥0∞) volume
  exact (burnolModelKernelWeightedLog_memLp burnolUnitParameter).comp_measurePreserving
    (Measure.measurePreserving_neg volume)

theorem fourier_burnolAReflectedWeightedLog (xi : ℝ) :
    𝓕 burnolAReflectedWeightedLog xi = burnolZConjOnCriticalLine xi := by
  calc
    𝓕 burnolAReflectedWeightedLog xi =
        𝓕 (burnolModelKernelWeightedLog burnolUnitParameter) (-xi) := by
      change 𝓕 (burnolModelKernelWeightedLog burnolUnitParameter ∘
        fun u : ℝ => -u) xi = _
      simpa only [Function.comp_apply,
        LinearIsometryEquiv.coe_neg] using
        (Real.fourier_comp_linearIsometry
          (LinearIsometryEquiv.neg ℝ)
          (burnolModelKernelWeightedLog burnolUnitParameter) xi)
    _ = burnolModelKernelTransform burnolUnitParameter (-xi) :=
      fourier_burnolModelKernelWeightedLog burnolUnitParameter (-xi)
    _ = burnolZOnCriticalLine (-xi) := burnolModelKernelTransform_unit (-xi)
    _ = burnolZConjOnCriticalLine xi := burnolZOnCriticalLine_neg xi

theorem fourier_burnolAReflectedWeightedLog_memLp :
    MemLp (𝓕 burnolAReflectedWeightedLog) (2 : ℝ≥0∞) volume := by
  exact burnolZConjOnCriticalLine_memLp.ae_eq
    (ae_of_all volume fun xi => (fourier_burnolAReflectedWeightedLog xi).symm)

theorem fourierL2_burnolAReflectedWeightedLog :
    𝓕 (burnolAReflectedWeightedLog_memLp.toLp burnolAReflectedWeightedLog) =
      burnolZConjOnCriticalLine_memLp.toLp burnolZConjOnCriticalLine := by
  have hcompat := fourier_toLp_eq_toLp_fourier
    burnolAReflectedWeightedLog_integrable burnolAReflectedWeightedLog_memLp
    fourier_burnolAReflectedWeightedLog_memLp
  calc
    𝓕 (burnolAReflectedWeightedLog_memLp.toLp burnolAReflectedWeightedLog) =
        fourier_burnolAReflectedWeightedLog_memLp.toLp
          (𝓕 burnolAReflectedWeightedLog) := hcompat
    _ = burnolZConjOnCriticalLine_memLp.toLp burnolZConjOnCriticalLine :=
      MemLp.toLp_congr fourier_burnolAReflectedWeightedLog_memLp
        burnolZConjOnCriticalLine_memLp
        (ae_of_all volume fourier_burnolAReflectedWeightedLog)

theorem weightedLogPullback_burnolTimeReverseL2_A :
    weightedLogPullback (burnolTimeReverseL2 burnolComplexAL2) =
      burnolAReflectedWeightedLog_memLp.toLp burnolAReflectedWeightedLog := by
  rw [weightedLogPullback_burnolTimeReverseL2]
  have hAlog := burnolModelKernelWeightedLog_toLp burnolUnitParameter
  rw [burnolModelKernelL2_unit_eq_A] at hAlog
  rw [← hAlog]
  change Lp.compMeasurePreserving (Neg.neg : ℝ → ℝ)
      (Measure.measurePreserving_neg volume)
      ((burnolModelKernelWeightedLog_memLp burnolUnitParameter).toLp
        (burnolModelKernelWeightedLog burnolUnitParameter)) =
    burnolAReflectedWeightedLog_memLp.toLp burnolAReflectedWeightedLog
  rw [Lp.toLp_compMeasurePreserving]
  rfl

theorem baezDuarteFourierMellinL2_burnolTimeReverseL2_A :
    baezDuarteFourierMellinL2 (burnolTimeReverseL2 burnolComplexAL2) =
      burnolZConjOnCriticalLine_memLp.toLp burnolZConjOnCriticalLine := by
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply,
    weightedLogPullback_burnolTimeReverseL2_A]
  exact fourierL2_burnolAReflectedWeightedLog

/-- Burnol's second phase sends `A` to its physical time reversal. -/
theorem burnolAPhaseL2_A_eq_timeReverse :
    burnolAPhaseL2 burnolComplexAL2 = burnolTimeReverseL2 burnolComplexAL2 := by
  apply baezDuarteFourierMellinL2.injective
  rw [baezDuarteFourierMellinL2_burnolAPhaseL2_A,
    baezDuarteFourierMellinL2_burnolTimeReverseL2_A]

/-- The normalized Mellin dilation factor is the Fourier phase generated by logarithmic
translation. -/
theorem burnol_normalizedDilationFactor_eq_fourierChar
    (theta : burnolContinuousParameter) (xi : ℝ) :
    ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
        burnolDilationFactor theta (burnolCriticalLineAtFrequency xi) =
      (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) := by
  have htheta : 0 < (theta : ℝ) := theta.property.1
  have hthetaInv : 0 < (theta : ℝ)⁻¹ := inv_pos.mpr htheta
  have hsqrt :
      ((Real.sqrt (theta : ℝ) : ℝ) : ℂ) =
        Complex.exp (((Real.log (theta : ℝ) / 2 : ℝ) : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos htheta, Complex.ofReal_exp]
    congr 2
    ring
  rw [burnolDilationFactor,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hthetaInv.ne'),
    ← Complex.ofReal_log hthetaInv.le, Real.log_inv, hsqrt,
    ← Complex.exp_neg, ← Complex.exp_add, Real.fourierChar_apply]
  congr 1
  push_cast
  simp only [burnolCriticalLineAtFrequency]
  push_cast
  ring

theorem burnol_normalizedDilationFactor_one_sub
    (theta : burnolContinuousParameter) (w : ℂ) :
    ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
        burnolDilationFactor theta (1 - w) =
      ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w) := by
  have htheta : 0 < (theta : ℝ) := theta.property.1
  have hthetaInv : 0 < (theta : ℝ)⁻¹ := inv_pos.mpr htheta
  have hsqrt :
      ((Real.sqrt (theta : ℝ) : ℝ) : ℂ) =
        Complex.exp (((Real.log (theta : ℝ) / 2 : ℝ) : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos htheta, Complex.ofReal_exp]
    congr 2
    ring
  rw [burnolDilationFactor,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hthetaInv.ne'),
    ← Complex.ofReal_log hthetaInv.le, Real.log_inv, hsqrt,
    ← Complex.exp_neg, ← Complex.exp_add,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr htheta.ne'),
    ← Complex.ofReal_log htheta.le]
  congr 1
  push_cast
  ring

/-- The weighted-log representative of the normalized dilate `D_theta (J A)`. -/
def burnolNormalizedTimeReverseWeightedLog
    (theta : burnolContinuousParameter) (u : ℝ) : ℂ :=
  burnolAReflectedWeightedLog (u + Real.log (theta : ℝ))

theorem burnolNormalizedTimeReverseWeightedLog_integrable
    (theta : burnolContinuousParameter) :
    Integrable (burnolNormalizedTimeReverseWeightedLog theta) := by
  change Integrable (burnolAReflectedWeightedLog ∘
    fun u : ℝ => u + Real.log (theta : ℝ))
  exact burnolAReflectedWeightedLog_integrable.comp_add_right _

theorem burnolNormalizedTimeReverseWeightedLog_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolNormalizedTimeReverseWeightedLog theta)
      (2 : ℝ≥0∞) volume := by
  change MemLp (burnolAReflectedWeightedLog ∘
    fun u : ℝ => u + Real.log (theta : ℝ)) (2 : ℝ≥0∞) volume
  exact burnolAReflectedWeightedLog_memLp.comp_measurePreserving
    (measurePreserving_add_right volume (Real.log (theta : ℝ)))

theorem fourier_burnolNormalizedTimeReverseWeightedLog
    (theta : burnolContinuousParameter) (xi : ℝ) :
    𝓕 (burnolNormalizedTimeReverseWeightedLog theta) xi =
      (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) *
        burnolZConjOnCriticalLine xi := by
  have htranslate := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
      (innerₗ ℝ) burnolAReflectedWeightedLog (Real.log (theta : ℝ))) xi
  have hinner :
      (innerₗ ℝ) (Real.log (theta : ℝ)) xi =
        Real.log (theta : ℝ) * xi := by
    simp only [innerₗ_apply_apply, Real.inner_apply]
  calc
    𝓕 (burnolNormalizedTimeReverseWeightedLog theta) xi =
        (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) *
          𝓕 burnolAReflectedWeightedLog xi := by
      rw [← smul_eq_mul]
      change 𝓕 (burnolAReflectedWeightedLog ∘
        fun u : ℝ => u + Real.log (theta : ℝ)) xi = _
      change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          (burnolAReflectedWeightedLog ∘
            fun u : ℝ => u + Real.log (theta : ℝ)) xi =
        (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) •
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
            burnolAReflectedWeightedLog xi
      simpa only [Circle.smul_def, hinner] using htranslate
    _ = (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) *
        burnolZConjOnCriticalLine xi := by
      rw [fourier_burnolAReflectedWeightedLog]

/-- Frequency representative of the normalized dilate `D_theta (J A)`. -/
def burnolNormalizedTimeReverseTransform
    (theta : burnolContinuousParameter) (xi : ℝ) : ℂ :=
  (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) *
    burnolZConjOnCriticalLine xi

theorem burnolNormalizedTimeReverseTransform_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolNormalizedTimeReverseTransform theta)
      (2 : ℝ≥0∞) volume := by
  have hphaseMeasurable : Measurable (fun xi : ℝ =>
      (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ)) := by
    fun_prop
  have hphase : MemLp (fun xi : ℝ =>
      (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ)) ∞ volume := by
    refine memLp_top_of_bound hphaseMeasurable.aestronglyMeasurable 1 ?_
    exact ae_of_all volume fun xi => by simp
  change MemLp (fun xi : ℝ =>
    (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) •
      burnolZConjOnCriticalLine xi) (2 : ℝ≥0∞) volume
  exact burnolZConjOnCriticalLine_memLp.smul hphase

theorem fourier_burnolNormalizedTimeReverseWeightedLog_memLp
    (theta : burnolContinuousParameter) :
    MemLp (𝓕 (burnolNormalizedTimeReverseWeightedLog theta))
      (2 : ℝ≥0∞) volume := by
  exact (burnolNormalizedTimeReverseTransform_memLp theta).ae_eq
    (ae_of_all volume fun xi =>
      (fourier_burnolNormalizedTimeReverseWeightedLog theta xi).symm)

theorem fourierL2_burnolNormalizedTimeReverseWeightedLog
    (theta : burnolContinuousParameter) :
    𝓕 ((burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (burnolNormalizedTimeReverseWeightedLog theta)) =
      (burnolNormalizedTimeReverseTransform_memLp theta).toLp
        (burnolNormalizedTimeReverseTransform theta) := by
  have hcompat := fourier_toLp_eq_toLp_fourier
    (burnolNormalizedTimeReverseWeightedLog_integrable theta)
    (burnolNormalizedTimeReverseWeightedLog_memLp theta)
    (fourier_burnolNormalizedTimeReverseWeightedLog_memLp theta)
  calc
    𝓕 ((burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (burnolNormalizedTimeReverseWeightedLog theta)) =
      (fourier_burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (𝓕 (burnolNormalizedTimeReverseWeightedLog theta)) := hcompat
    _ = (burnolNormalizedTimeReverseTransform_memLp theta).toLp
        (burnolNormalizedTimeReverseTransform theta) :=
      MemLp.toLp_congr
        (fourier_burnolNormalizedTimeReverseWeightedLog_memLp theta)
        (burnolNormalizedTimeReverseTransform_memLp theta)
        (ae_of_all volume (fourier_burnolNormalizedTimeReverseWeightedLog theta))

/-- The physical `L2` vector `D_theta (J A)`. -/
def burnolNormalizedTimeReverseKernelL2
    (theta : burnolContinuousParameter) : positiveHalfLineComplexL2 :=
  weightedLogPullback.symm
    ((burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
      (burnolNormalizedTimeReverseWeightedLog theta))

theorem weightedLogPullback_burnolNormalizedTimeReverseKernelL2
    (theta : burnolContinuousParameter) :
    weightedLogPullback (burnolNormalizedTimeReverseKernelL2 theta) =
      (burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (burnolNormalizedTimeReverseWeightedLog theta) := by
  exact weightedLogPullback.apply_symm_apply _

theorem baezDuarteFourierMellinL2_burnolNormalizedTimeReverseKernelL2
    (theta : burnolContinuousParameter) :
    baezDuarteFourierMellinL2
        (burnolNormalizedTimeReverseKernelL2 theta) =
      (burnolNormalizedTimeReverseTransform_memLp theta).toLp
        (burnolNormalizedTimeReverseTransform theta) := by
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply,
    weightedLogPullback_burnolNormalizedTimeReverseKernelL2]
  exact fourierL2_burnolNormalizedTimeReverseWeightedLog theta

/-- Burnol's normalized dilation `D_theta A(t) = theta^(-1/2) A(t/theta)`. -/
def burnolNormalizedModelKernelL2
    (theta : burnolContinuousParameter) : positiveHalfLineComplexL2 :=
  ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) • burnolModelKernelL2 theta

theorem burnolModelKernelL2_eq_sqrt_smul_normalized
    (theta : burnolContinuousParameter) :
    ((Real.sqrt (theta : ℝ) : ℝ) : ℂ) • burnolNormalizedModelKernelL2 theta =
      burnolModelKernelL2 theta := by
  rw [burnolNormalizedModelKernelL2, smul_smul]
  have hsqrt : Real.sqrt (theta : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 theta.property.1).ne'
  simp [hsqrt]

theorem burnolNormalizedModelKernelL2_coeFn
    (theta : burnolContinuousParameter) :
    burnolNormalizedModelKernelL2 theta
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun t => ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
          (burnolA (t / (theta : ℝ)) : ℂ) := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt (theta : ℝ))⁻¹ : ℂ)
      (burnolModelKernelL2 theta), burnolModelKernelL2_coeFn theta] with t hsmul hkernel
  rw [burnolNormalizedModelKernelL2, hsmul]
  change ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) * burnolModelKernelL2 theta t = _
  rw [hkernel]

/-- Frequency representative of the normalized model kernel `D_theta A`. -/
def burnolNormalizedModelKernelTransform
    (theta : burnolContinuousParameter) (xi : ℝ) : ℂ :=
  ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) * burnolModelKernelTransform theta xi

theorem burnolNormalizedModelKernelTransform_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolNormalizedModelKernelTransform theta)
      (2 : ℝ≥0∞) volume := by
  change MemLp (((Real.sqrt (theta : ℝ))⁻¹ : ℂ) •
    burnolModelKernelTransform theta) (2 : ℝ≥0∞) volume
  exact (burnolModelKernelTransform_memLp theta).const_smul _

theorem baezDuarteFourierMellinL2_burnolNormalizedModelKernelL2
    (theta : burnolContinuousParameter) :
    baezDuarteFourierMellinL2 (burnolNormalizedModelKernelL2 theta) =
      (burnolNormalizedModelKernelTransform_memLp theta).toLp
        (burnolNormalizedModelKernelTransform theta) := by
  rw [burnolNormalizedModelKernelL2, map_smul,
    baezDuarteFourierMellinL2_modelKernel_eq]
  change ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) •
      (burnolModelKernelTransform_memLp theta).toLp
        (burnolModelKernelTransform theta) = _
  rw [← MemLp.toLp_const_smul]
  rfl

theorem burnolModelKernelTransform_eq_dilation_mul_Z
    (theta : burnolContinuousParameter) (xi : ℝ) :
    burnolModelKernelTransform theta xi =
      burnolDilationFactor theta (burnolCriticalLineAtFrequency xi) *
        burnolZOnCriticalLine xi := by
  rfl

theorem burnolAPhaseMultiplier_mul_normalizedModelKernelTransform
    (theta : burnolContinuousParameter) (xi : ℝ) :
    burnolAPhaseMultiplier xi *
        burnolNormalizedModelKernelTransform theta xi =
      burnolNormalizedTimeReverseTransform theta xi := by
  rw [burnolNormalizedModelKernelTransform,
    burnolModelKernelTransform_eq_dilation_mul_Z,
    burnolNormalizedTimeReverseTransform]
  calc
    burnolAPhaseMultiplier xi *
        (((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
          (burnolDilationFactor theta (burnolCriticalLineAtFrequency xi) *
            burnolZOnCriticalLine xi)) =
      (((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
          burnolDilationFactor theta (burnolCriticalLineAtFrequency xi)) *
        (burnolAPhaseMultiplier xi * burnolZOnCriticalLine xi) := by ring
    _ = (((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
          burnolDilationFactor theta (burnolCriticalLineAtFrequency xi)) *
        burnolZConjOnCriticalLine xi := by
      rw [burnolAPhaseMultiplier_mul_Z]
    _ = (Real.fourierChar (Real.log (theta : ℝ) * xi) : ℂ) *
        burnolZConjOnCriticalLine xi := by
      rw [burnol_normalizedDilationFactor_eq_fourierChar]

theorem burnolAPhaseFrequencyL2_normalizedModelKernelTransform
    (theta : burnolContinuousParameter) :
    burnolAPhaseFrequencyL2
        ((burnolNormalizedModelKernelTransform_memLp theta).toLp
          (burnolNormalizedModelKernelTransform theta)) =
      (burnolNormalizedTimeReverseTransform_memLp theta).toLp
        (burnolNormalizedTimeReverseTransform theta) := by
  rw [burnolAPhaseFrequencyL2_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolAPhaseMultiplierLInf
      ((burnolNormalizedModelKernelTransform_memLp theta).toLp
        (burnolNormalizedModelKernelTransform theta)),
    burnolAPhaseMultiplierLInf_coeFn,
    MemLp.coeFn_toLp (burnolNormalizedModelKernelTransform_memLp theta),
    MemLp.coeFn_toLp (burnolNormalizedTimeReverseTransform_memLp theta)] with
      xi hmul hphase hmodel hreflect
  rw [hmul]
  change burnolAPhaseMultiplierLInf xi *
      ((burnolNormalizedModelKernelTransform_memLp theta).toLp
        (burnolNormalizedModelKernelTransform theta)) xi =
    ((burnolNormalizedTimeReverseTransform_memLp theta).toLp
      (burnolNormalizedTimeReverseTransform theta)) xi
  rw [hphase, hmodel, hreflect,
    burnolAPhaseMultiplier_mul_normalizedModelKernelTransform]

/-- Burnol's second phase commutes with the normalized dilation of `A`, sending it to the
corresponding normalized dilate of `J A`. -/
theorem burnolAPhaseL2_normalizedModelKernel_eq_timeReverse
    (theta : burnolContinuousParameter) :
    burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta) =
      burnolNormalizedTimeReverseKernelL2 theta := by
  apply baezDuarteFourierMellinL2.injective
  rw [baezDuarteFourierMellinL2_burnolAPhaseL2,
    baezDuarteFourierMellinL2_burnolNormalizedModelKernelL2,
    burnolAPhaseFrequencyL2_normalizedModelKernelTransform,
    baezDuarteFourierMellinL2_burnolNormalizedTimeReverseKernelL2]

theorem weightedLogInverse_burnolNormalizedTimeReverse_pointwise
    (theta : burnolContinuousParameter) {t : ℝ} (ht : 0 < t) :
    ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        burnolNormalizedTimeReverseWeightedLog theta (-Real.log t) =
      ((Real.sqrt (theta : ℝ) : ℝ) : ℂ) * (t⁻¹ : ℂ) *
        (burnolA ((theta : ℝ) / t) : ℂ) := by
  have htheta : 0 < (theta : ℝ) := theta.property.1
  have hdiv : 0 < t / (theta : ℝ) := div_pos ht htheta
  have hsqrtExp :
      Real.exp (Real.log (theta : ℝ) / 2) = Real.sqrt (theta : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos htheta]
    congr 1
    ring
  have htHalf : Real.exp (-Real.log t / 2) = t ^ (-1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    ring
  have hhalf :
      Real.exp (-(Real.log t - Real.log (theta : ℝ)) / 2) =
        Real.sqrt (theta : ℝ) * t ^ (-1 / 2 : ℝ) := by
    rw [show -(Real.log t - Real.log (theta : ℝ)) / 2 =
        Real.log (theta : ℝ) / 2 + (-Real.log t / 2) by ring,
      Real.exp_add, hsqrtExp, htHalf]
  have hexpInv :
      Real.exp (-(Real.log t - Real.log (theta : ℝ))) =
        (theta : ℝ) / t := by
    rw [← Real.log_div ht.ne' htheta.ne', Real.exp_neg, Real.exp_log hdiv]
    field_simp
  simp only [burnolNormalizedTimeReverseWeightedLog,
    burnolAReflectedWeightedLog, burnolModelKernelWeightedLog,
    burnolModelKernel, burnolUnitParameter]
  rw [show -(-Real.log t + Real.log (theta : ℝ)) =
      Real.log t - Real.log (theta : ℝ) by ring,
    hhalf, hexpInv]
  push_cast
  have hrpow : t ^ (-1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) = t⁻¹ := by
    rw [← Real.rpow_add ht]
    norm_num
    rw [Real.rpow_neg_one]
  rw [← Complex.ofReal_inv, ← hrpow]
  push_cast
  ring

theorem burnolNormalizedTimeReverseKernelL2_coeFn
    (theta : burnolContinuousParameter) :
    burnolNormalizedTimeReverseKernelL2 theta
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun t => ((Real.sqrt (theta : ℝ) : ℝ) : ℂ) * (t⁻¹ : ℂ) *
          (burnolA ((theta : ℝ) / t) : ℂ) := by
  have hweighted := burnolNegLog_quasiMeasurePreserving.ae_eq
    (MemLp.coeFn_toLp (burnolNormalizedTimeReverseWeightedLog_memLp theta))
  filter_upwards [weightedLogPullback_symm_coeFn
      ((burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (burnolNormalizedTimeReverseWeightedLog theta)),
    hweighted, ae_restrict_mem measurableSet_Ioi] with t hout hinner ht
  rw [burnolNormalizedTimeReverseKernelL2, hout]
  change ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      ((burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (burnolNormalizedTimeReverseWeightedLog theta)) (burnolNegLog t) = _
  have hinner' :
      ((burnolNormalizedTimeReverseWeightedLog_memLp theta).toLp
        (burnolNormalizedTimeReverseWeightedLog theta)) (burnolNegLog t) =
      burnolNormalizedTimeReverseWeightedLog theta (burnolNegLog t) := by
    simpa only [Function.comp_apply] using hinner
  rw [hinner']
  exact weightedLogInverse_burnolNormalizedTimeReverse_pointwise theta ht

theorem burnolNormalizedTimeReverseKernelL2_eq_zero_ae_of_lt
    (theta : burnolContinuousParameter) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      t < (theta : ℝ) → burnolNormalizedTimeReverseKernelL2 theta t = 0 := by
  filter_upwards [burnolNormalizedTimeReverseKernelL2_coeFn theta,
    ae_restrict_mem measurableSet_Ioi] with t hkernel ht hlt
  rw [hkernel]
  have hratio : 1 < (theta : ℝ) / t := by
    rw [lt_div_iff₀ ht]
    simpa using hlt
  rw [burnolA_eq_zero_of_one_lt hratio]
  simp

/-- The physical cutoff preserves `L2(0,infinity)`. -/
theorem burnolCutoff_memLp (lambda : ℝ) (f : positiveHalfLineComplexL2) :
    MemLp ((Ici lambda).indicator (fun t : ℝ => f t)) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  exact (Lp.memLp f).indicator measurableSet_Ici

/-- Physical multiplication by the source cutoff `1_[lambda,infinity)`. -/
def burnolCutoffL2 (lambda : ℝ)
    (f : positiveHalfLineComplexL2) : positiveHalfLineComplexL2 :=
  (burnolCutoff_memLp lambda f).toLp
    ((Ici lambda).indicator (fun t : ℝ => f t))

theorem burnolCutoffL2_coeFn (lambda : ℝ) (f : positiveHalfLineComplexL2) :
    burnolCutoffL2 lambda f
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] (Ici lambda).indicator f := by
  unfold burnolCutoffL2
  exact MemLp.coeFn_toLp (burnolCutoff_memLp lambda f)

theorem burnolCutoffL2_idem (lambda : ℝ) (f : positiveHalfLineComplexL2) :
    burnolCutoffL2 lambda (burnolCutoffL2 lambda f) = burnolCutoffL2 lambda f := by
  apply Lp.ext
  filter_upwards [burnolCutoffL2_coeFn lambda (burnolCutoffL2 lambda f),
    burnolCutoffL2_coeFn lambda f] with t hout hin
  rw [hout]
  by_cases ht : t ∈ Ici lambda
  · rw [Set.indicator_of_mem ht, hin, Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht, hin, Set.indicator_of_notMem ht]

theorem burnolCutoffL2_normalizedTimeReverse_eq_self
    (lambda : ℝ) (theta : burnolContinuousParameter)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) :
    burnolCutoffL2 lambda (burnolNormalizedTimeReverseKernelL2 theta) =
      burnolNormalizedTimeReverseKernelL2 theta := by
  apply Lp.ext
  filter_upwards [burnolCutoffL2_coeFn lambda
      (burnolNormalizedTimeReverseKernelL2 theta),
    burnolNormalizedTimeReverseKernelL2_eq_zero_ae_of_lt theta] with
      t hcutoff hzero
  rw [hcutoff]
  by_cases ht : t ∈ Ici lambda
  · rw [Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht]
    exact (hzero ((not_le.mp ht).trans_le hlambdaTheta)).symm

theorem burnolCutoffL2_APhase_normalizedModelKernel_eq_self
    (lambda : ℝ) (theta : burnolContinuousParameter)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) :
    burnolCutoffL2 lambda
        (burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta)) =
      burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta) := by
  rw [burnolAPhaseL2_normalizedModelKernel_eq_timeReverse,
    burnolCutoffL2_normalizedTimeReverse_eq_self lambda theta hlambdaTheta]

theorem burnolCutoffL2_eq_zero_ae_of_lt (lambda : ℝ)
    (f : positiveHalfLineComplexL2) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      t < lambda → burnolCutoffL2 lambda f t = 0 := by
  filter_upwards [burnolCutoffL2_coeFn lambda f] with t ht hlt
  rw [ht]
  exact Set.indicator_of_notMem (not_le.mpr hlt) _

theorem inner_burnolCutoffL2 (lambda : ℝ)
    (f g : positiveHalfLineComplexL2) :
    inner (𝕜 := ℂ) (burnolCutoffL2 lambda f) g =
      inner (𝕜 := ℂ) f (burnolCutoffL2 lambda g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolCutoffL2_coeFn lambda f,
    burnolCutoffL2_coeFn lambda g] with t hf hg
  rw [hf, hg]
  by_cases ht : t ∈ Ici lambda <;> simp [Set.indicator, ht]

/-- Burnol's left-half-plane vector before undoing logarithmic coordinates. -/
def burnolPsiWeightedLog (w : ℂ) (k : ℕ) (u : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun v => (v : ℂ) ^ k * Complex.exp ((w - 1 / 2) * v)) u

theorem measurable_burnolPsiWeightedLog (w : ℂ) (k : ℕ) :
    Measurable (burnolPsiWeightedLog w k) := by
  exact (by fun_prop : Measurable fun v : ℝ =>
    (v : ℂ) ^ k * Complex.exp ((w - 1 / 2) * v)).indicator measurableSet_Ioi

theorem norm_sq_burnolPsiWeightedLog_of_pos
    (w : ℂ) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    ‖burnolPsiWeightedLog w k u‖ ^ 2 =
      u ^ (2 * (k : ℝ)) *
        Real.exp (-(1 - 2 * w.re) * u ^ (1 : ℝ)) := by
  have huMem : u ∈ Ioi (0 : ℝ) := hu
  rw [burnolPsiWeightedLog, Set.indicator_of_mem huMem]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu,
    Complex.norm_exp]
  rw [Complex.mul_re]
  norm_num
  have hexp : 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_natCast]
  have hpow : (u ^ k) ^ 2 = u ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    omega
  rw [mul_pow, hpow, pow_two, ← Real.exp_add]
  congr 1
  ring_nf

theorem burnolPsiWeightedLog_memLp (w : ℂ) (k : ℕ)
    (hw : w.re < 1 / 2) :
    MemLp (burnolPsiWeightedLog w k) (2 : ℝ≥0∞) volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (measurable_burnolPsiWeightedLog w k).aestronglyMeasurable]
  have hb : 0 < 1 - 2 * w.re := by linarith
  have hgamma : IntegrableOn
      (fun u : ℝ => u ^ (2 * (k : ℝ)) *
        Real.exp (-(1 - 2 * w.re) * u ^ (1 : ℝ))) (Ioi 0) := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hs : (-1 : ℝ) < 2 * (k : ℝ) := by linarith
    exact integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 2 * (k : ℝ)) (b := 1 - 2 * w.re) hs (by norm_num) hb
  have heq : (fun u : ℝ => ‖burnolPsiWeightedLog w k u‖ ^ 2) =
      (Ioi (0 : ℝ)).indicator (fun u : ℝ =>
        u ^ (2 * (k : ℝ)) *
          Real.exp (-(1 - 2 * w.re) * u ^ (1 : ℝ))) := by
    funext u
    by_cases hu : 0 < u
    · have huMem : u ∈ Ioi (0 : ℝ) := hu
      rw [norm_sq_burnolPsiWeightedLog_of_pos w k hu,
        Set.indicator_of_mem huMem]
    · have huMem : u ∉ Ioi (0 : ℝ) := hu
      rw [burnolPsiWeightedLog, Set.indicator_of_notMem huMem,
        Set.indicator_of_notMem huMem]
      simp
  rw [heq]
  exact hgamma.integrable_indicator measurableSet_Ioi

/-- The logarithmic `L2` vector, totalized by zero outside the source half-plane. -/
def burnolPsiWeightedLogL2 (w : ℂ) (k : ℕ) : realLineComplexL2 :=
  if hw : w.re < 1 / 2 then
    (burnolPsiWeightedLog_memLp w k hw).toLp (burnolPsiWeightedLog w k)
  else 0

theorem burnolPsiWeightedLogL2_coeFn (w : ℂ) (k : ℕ)
    (hw : w.re < 1 / 2) :
    burnolPsiWeightedLogL2 w k =ᵐ[volume] burnolPsiWeightedLog w k := by
  rw [burnolPsiWeightedLogL2, dif_pos hw]
  exact MemLp.coeFn_toLp (burnolPsiWeightedLog_memLp w k hw)

/-- The source representative `log(1/t)^k t^(-w) 1_(0,1)(t)`. The omitted endpoint is null. -/
def burnolPsi (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (Ioo (0 : ℝ) 1).indicator
    (fun x => (Real.log (1 / x) : ℂ) ^ k * (x : ℂ) ^ (-w)) t

/-- Burnol's source vector in physical `L2`, totalized by zero outside `Re(w)<1/2`. -/
def burnolPsiL2 (w : ℂ) (k : ℕ) : positiveHalfLineComplexL2 :=
  weightedLogPullback.symm (burnolPsiWeightedLogL2 w k)

theorem weightedLogInverse_burnolPsi_pointwise
    (w : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        burnolPsiWeightedLog w k (-Real.log t) = burnolPsi w k t := by
  by_cases ht1 : t < 1
  · have hu : 0 < -Real.log t := neg_pos.mpr (Real.log_neg ht ht1)
    have huMem : -Real.log t ∈ Ioi (0 : ℝ) := hu
    have htMem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
    have hlog : Real.log (1 / t) = -Real.log t := by
      rw [one_div, Real.log_inv]
    rw [burnolPsiWeightedLog, Set.indicator_of_mem huMem,
      burnolPsi, Set.indicator_of_mem htMem, hlog]
    push_cast
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hscalar :
        ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
            Complex.exp ((w - 1 / 2) * (-(Real.log t : ℂ))) =
          (t : ℂ) ^ (-w) := by
      rw [Real.rpow_def_of_pos ht, Complex.ofReal_exp,
        Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le,
        ← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
          ((-(Real.log t : ℂ)) ^ k *
            Complex.exp ((w - 1 / 2) * (-(Real.log t : ℂ)))) =
          (-(Real.log t : ℂ)) ^ k *
            (((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
              Complex.exp ((w - 1 / 2) * (-(Real.log t : ℂ)))) := by ring
      _ = (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-w) := by rw [hscalar]
  · have ht1' : 1 ≤ t := not_lt.mp ht1
    have hu : -Real.log t ≤ 0 := neg_nonpos.mpr (Real.log_nonneg ht1')
    have huNot : -Real.log t ∉ Ioi (0 : ℝ) := not_lt.mpr hu
    have htNot : t ∉ Ioo (0 : ℝ) 1 := fun h => ht1 h.2
    rw [burnolPsiWeightedLog, Set.indicator_of_notMem huNot,
      burnolPsi, Set.indicator_of_notMem htNot]
    simp

theorem burnolPsiL2_coeFn (w : ℂ) (k : ℕ) (hw : w.re < 1 / 2) :
    burnolPsiL2 w k =ᵐ[volume.restrict (Ioi (0 : ℝ))] burnolPsi w k := by
  have hweighted := burnolNegLog_quasiMeasurePreserving.ae_eq
    (burnolPsiWeightedLogL2_coeFn w k hw)
  filter_upwards [weightedLogPullback_symm_coeFn (burnolPsiWeightedLogL2 w k),
    hweighted, ae_restrict_mem measurableSet_Ioi] with t hout hinner ht
  rw [burnolPsiL2, hout]
  change ((t ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      burnolPsiWeightedLogL2 w k (burnolNegLog t) = burnolPsi w k t
  have hinner' : burnolPsiWeightedLogL2 w k (burnolNegLog t) =
      burnolPsiWeightedLog w k (burnolNegLog t) := by
    simpa only [Function.comp_apply] using hinner
  rw [hinner']
  exact weightedLogInverse_burnolPsi_pointwise w k ht

/-- Burnol's left-half-plane vector before taking the critical-line boundary limit. -/
def burnolPreY (lambda : ℝ) (w : ℂ) (k : ℕ) : positiveHalfLineComplexL2 :=
  burnolAPhaseL2.symm
    (burnolCutoffL2 lambda (burnolAPhaseL2 (burnolPsiL2 w k)))

/-- Before taking the boundary limit, unitarity and cutoff support reduce Burnol's pairing to the
source vector `psi(w,k)`. This is the orientation linear in `w` after translating the source
inner-product convention to Mathlib's convention. -/
theorem inner_normalizedModelKernel_burnolPreY
    (lambda : ℝ) (theta : burnolContinuousParameter) (w : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w k) =
      inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPsiL2 w k) := by
  rw [burnolPreY]
  calc
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolAPhaseL2.symm
          (burnolCutoffL2 lambda (burnolAPhaseL2 (burnolPsiL2 w k)))) =
      inner (𝕜 := ℂ)
        (burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta))
        (burnolAPhaseL2
          (burnolAPhaseL2.symm
            (burnolCutoffL2 lambda (burnolAPhaseL2 (burnolPsiL2 w k))))) :=
      (burnolAPhaseL2.inner_map_map
        (burnolNormalizedModelKernelL2 theta)
        (burnolAPhaseL2.symm
          (burnolCutoffL2 lambda (burnolAPhaseL2 (burnolPsiL2 w k))))).symm
    _ = inner (𝕜 := ℂ)
        (burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta))
        (burnolCutoffL2 lambda (burnolAPhaseL2 (burnolPsiL2 w k))) := by
      rw [burnolAPhaseL2.apply_symm_apply]
    _ = inner (𝕜 := ℂ)
        (burnolCutoffL2 lambda
          (burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta)))
        (burnolAPhaseL2 (burnolPsiL2 w k)) :=
      (inner_burnolCutoffL2 lambda
        (burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta))
        (burnolAPhaseL2 (burnolPsiL2 w k))).symm
    _ = inner (𝕜 := ℂ)
        (burnolAPhaseL2 (burnolNormalizedModelKernelL2 theta))
        (burnolAPhaseL2 (burnolPsiL2 w k)) := by
      rw [burnolCutoffL2_APhase_normalizedModelKernel_eq_self
        lambda theta hlambdaTheta]
    _ = inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPsiL2 w k) :=
      burnolAPhaseL2.inner_map_map
        (burnolNormalizedModelKernelL2 theta) (burnolPsiL2 w k)

theorem inner_normalizedModelKernel_burnolPsiL2_zero_eq_mellin
    (theta : burnolContinuousParameter) (w : ℂ)
    (hw : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPsiL2 w 0) =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
        mellin (fun t : ℝ => (burnolModelKernel theta t : ℂ)) (1 - w) := by
  rw [MeasureTheory.L2.inner_def, mellin, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [burnolNormalizedModelKernelL2_coeFn theta,
    burnolPsiL2_coeFn w 0 hw, ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with
      t hkernel hpsi ht htOne
  rw [hkernel, hpsi]
  rw [RCLike.inner_apply']
  by_cases ht1 : t < 1
  · have htMem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
    rw [burnolPsi, Set.indicator_of_mem htMem]
    simp only [pow_zero, one_mul, burnolModelKernel, map_mul, map_inv₀,
      Complex.conj_ofReal, smul_eq_mul]
    rw [show (1 : ℂ) - w - 1 = -w by ring]
    ring
  · have htGt : 1 < t := lt_of_le_of_ne (not_lt.mp ht1) (Ne.symm htOne)
    have htNot : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_ge htGt.le) h.2
    have hratio : 1 < t / (theta : ℝ) := by
      rw [lt_div_iff₀ theta.property.1]
      simpa only [one_mul] using theta.property.2.trans_lt htGt
    rw [burnolPsi, Set.indicator_of_notMem htNot,
      burnolModelKernel, burnolA_eq_zero_of_one_lt hratio]
    simp

theorem inner_normalizedModelKernel_burnolPsiL2_eq_mellin_log
    (theta : burnolContinuousParameter) (w : ℂ) (k : ℕ)
    (hw : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPsiL2 w k) =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) * ((-1 : ℂ) ^ k *
        mellin (fun t : ℝ =>
          (Real.log t : ℂ) ^ k * (burnolModelKernel theta t : ℂ)) (1 - w)) := by
  rw [MeasureTheory.L2.inner_def, mellin, ← integral_const_mul,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [burnolNormalizedModelKernelL2_coeFn theta,
    burnolPsiL2_coeFn w k hw, ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with
      t hkernel hpsi ht htOne
  rw [hkernel, hpsi]
  rw [RCLike.inner_apply']
  by_cases ht1 : t < 1
  · have htMem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
    rw [burnolPsi, Set.indicator_of_mem htMem]
    simp only [burnolModelKernel, map_mul, map_inv₀,
      Complex.conj_ofReal, smul_eq_mul]
    rw [show (1 : ℂ) - w - 1 = -w by ring, one_div, Real.log_inv]
    push_cast
    rw [neg_pow]
    ring
  · have htGt : 1 < t := lt_of_le_of_ne (not_lt.mp ht1) (Ne.symm htOne)
    have htNot : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_ge htGt.le) h.2
    have hratio : 1 < t / (theta : ℝ) := by
      rw [lt_div_iff₀ theta.property.1]
      simpa only [one_mul] using theta.property.2.trans_lt htGt
    rw [burnolPsi, Set.indicator_of_notMem htNot,
      burnolModelKernel, burnolA_eq_zero_of_one_lt hratio]
    simp

/-! ### Iterated Mellin differentiation of the explicit model kernel -/

/-- A convenient power majorant for Burnol's source function at the origin. -/
theorem abs_burnolA_le_six_mul_rpow
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |burnolA t| ≤ 6 * t ^ (-1 / 4 : ℝ) := by
  have hquarter : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlogMul :=
    Real.abs_log_mul_self_rpow_lt t (1 / 4 : ℝ) ht ht1 (by norm_num)
  rw [abs_mul, abs_of_pos hquarter] at hlogMul
  have hlog : |Real.log t| < 4 * t ^ (-1 / 4 : ℝ) := by
    calc
      |Real.log t| < 4 / t ^ (1 / 4 : ℝ) := by
        apply (lt_div_iff₀ hquarter).2
        simpa using hlogMul
      _ = 4 * t ^ (-1 / 4 : ℝ) := by
        rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num,
          Real.rpow_neg ht.le, div_eq_mul_inv]
  have hpower : 1 ≤ t ^ (-1 / 4 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by norm_num)
  have hA := abs_burnolA_le_two_add_abs_log ht ht1
  nlinarith

/-- Every logarithmic moment of the model kernel is locally integrable on the positive
half-line. -/
theorem locallyIntegrableOn_burnolModelKernel_logPow
    (theta : burnolContinuousParameter) (n : ℕ) :
    LocallyIntegrableOn (fun t : ℝ =>
      (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) (Ioi 0) := by
  have hbase : LocallyIntegrableOn
      (fun t : ℝ => (burnolModelKernel theta t : ℂ)) (Ioi 0) := by
    exact locallyIntegrableOn_of_locallyIntegrable_restrict
      ((burnolModelKernel_memLp_two_positiveHalfLine theta).ofReal.locallyIntegrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hlog : ContinuousOn (fun t : ℝ => (Real.log t : ℂ) ^ n) (Ioi 0) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun _ ht => ne_of_gt ht)).pow n
  exact hbase.continuousOn_mul hlog isOpen_Ioi.isLocallyClosed

/-- The explicit model kernel has a fixed `t^(-1/4)` majorant at the origin. -/
theorem isBigO_burnolModelKernel_rpow_zero
    (theta : burnolContinuousParameter) :
    (fun t : ℝ => (burnolModelKernel theta t : ℂ)) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-1 / 4 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  let C : ℝ := 6 / (theta : ℝ) ^ (-1 / 4 : ℝ)
  refine ⟨C, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT theta.property.1] with t ht
  have ht0 : 0 < t := ht.1
  have hratio0 : 0 < t / (theta : ℝ) := div_pos ht0 theta.property.1
  have hratio1 : t / (theta : ℝ) ≤ 1 :=
    (div_le_one theta.property.1).2 ht.2.le
  have hA := abs_burnolA_le_six_mul_rpow hratio0 hratio1
  have hthetaPow : 0 < (theta : ℝ) ^ (-1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos theta.property.1 _
  rw [burnolModelKernel, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
  calc
    |burnolA (t / (theta : ℝ))| ≤
        6 * (t / (theta : ℝ)) ^ (-1 / 4 : ℝ) := hA
    _ = C * t ^ (-1 / 4 : ℝ) := by
      rw [Real.div_rpow ht0.le theta.property.1.le]
      dsimp only [C]
      field_simp

/-- Multiplying the model kernel by any fixed logarithmic power costs less than an additional
`t^(-1/8)` at the origin. -/
theorem isBigO_burnolModelKernel_logPow_rpow_zero
    (theta : burnolContinuousParameter) (n : ℕ) :
    (fun t : ℝ =>
      (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) =O[𝓝[>] 0]
        (fun t : ℝ => t ^ (-(3 / 8 : ℝ))) := by
  have hlogRaw :=
    (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n : ℝ)
      (show (-(1 / 8 : ℝ)) < 0 by norm_num)).isBigO
  have hlog : (fun t : ℝ => (Real.log t) ^ n) =O[𝓝[>] 0]
      (fun t : ℝ => t ^ (-(1 / 8 : ℝ))) := by
    rw [Asymptotics.isBigO_iff] at hlogRaw ⊢
    obtain ⟨C, hC⟩ := hlogRaw
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_mem_nhdsWithin] with t ht ht0
    rw [Real.norm_eq_abs, abs_pow, ← Real.rpow_natCast |Real.log t| n,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.out.le _)]
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (Real.log t)) _),
      abs_of_nonneg (Real.rpow_nonneg ht0.out.le _)] using ht
  have hproduct := hlog.smul (isBigO_burnolModelKernel_rpow_zero theta)
  refine hproduct.congr' ?_ ?_
  · exact Eventually.of_forall fun t => by
      simp only [Complex.real_smul, Complex.ofReal_pow]
  · filter_upwards [eventually_mem_nhdsWithin] with t ht
    simp only [smul_eq_mul]
    rw [← Real.rpow_add ht.out]
    norm_num

/-- Every logarithmic moment of the compactly supported model kernel is eventually zero. -/
theorem isBigO_burnolModelKernel_logPow_rpow_top
    (theta : burnolContinuousParameter) (n : ℕ) :
    (fun t : ℝ =>
      (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) =O[atTop]
        (fun t : ℝ => t ^ (-2 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (theta : ℝ)] with t ht
  have hratio : 1 < t / (theta : ℝ) := by
    rw [lt_div_iff₀ theta.property.1]
    simpa only [one_mul] using ht
  simp [burnolModelKernel, burnolA_eq_zero_of_one_lt hratio]
  positivity

/-- Differentiating the Mellin transform of a logarithmic moment produces the next moment
throughout a fixed strip containing Burnol's evaluation points. -/
theorem hasDerivAt_mellin_burnolModelKernel_logPow
    (theta : burnolContinuousParameter) (n : ℕ) {s : ℂ}
    (hs0 : (3 / 8 : ℝ) < s.re) (hs1 : s.re < 2) :
    HasDerivAt
      (mellin (fun t : ℝ =>
        (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)))
      (mellin (fun t : ℝ =>
        (Real.log t : ℂ) ^ (n + 1) * (burnolModelKernel theta t : ℂ)) s) s := by
  have hdiff := mellin_hasDerivAt_of_isBigO_rpow
    (locallyIntegrableOn_burnolModelKernel_logPow theta n)
    (isBigO_burnolModelKernel_logPow_rpow_top theta n) hs1
    (isBigO_burnolModelKernel_logPow_rpow_zero theta n) hs0
  have hvalue :
      mellin (fun t : ℝ => Real.log t •
          ((Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ))) s =
        mellin (fun t : ℝ =>
          (Real.log t : ℂ) ^ (n + 1) *
            (burnolModelKernel theta t : ℂ)) s := by
    congr 1
    funext t
    simp only [Complex.real_smul, pow_succ]
    ring
  rw [hvalue] at hdiff
  exact hdiff.2

/-- All iterated Mellin derivatives of the explicit model kernel are its logarithmic moments. -/
theorem iteratedDeriv_mellin_burnolModelKernel_eq_logPow
    (theta : burnolContinuousParameter) (n : ℕ) {s : ℂ}
    (hs0 : (3 / 8 : ℝ) < s.re) (hs1 : s.re < 2) :
    iteratedDeriv n
        (mellin (fun t : ℝ => (burnolModelKernel theta t : ℂ))) s =
      mellin (fun t : ℝ =>
        (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) s := by
  induction n generalizing s with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n hn =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n
          (mellin (fun t : ℝ => (burnolModelKernel theta t : ℂ))) =ᶠ[𝓝 s]
          mellin (fun t : ℝ =>
            (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) := by
        have hstrip : ∀ᶠ z : ℂ in 𝓝 s, (3 / 8 : ℝ) < z.re ∧ z.re < 2 := by
          exact ((Complex.continuous_re.tendsto s).eventually
            (Ioo_mem_nhds hs0 hs1))
        filter_upwards [hstrip] with z hz
        exact hn hz.1 hz.2
      rw [hfun.deriv_eq]
      exact (hasDerivAt_mellin_burnolModelKernel_logPow theta n hs0 hs1).deriv

/-- The logarithmic moments are the iterated derivatives of the explicit Burnol Mellin
transform throughout the source strip. -/
theorem iteratedDeriv_burnolModelKernelMellin_eq_logPow
    (theta : burnolContinuousParameter) (n : ℕ) {s : ℂ}
    (hs0 : (3 / 8 : ℝ) < s.re) (hs1 : s.re < 1) :
    iteratedDeriv n
        (fun z : ℂ => burnolDilationFactor theta z * burnolZ z) s =
      mellin (fun t : ℝ =>
        (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) s := by
  have heq : mellin (fun t : ℝ => (burnolModelKernel theta t : ℂ)) =ᶠ[𝓝 s]
      fun z : ℂ => burnolDilationFactor theta z * burnolZ z := by
    have hstrip : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re ∧ z.re < 1 := by
      exact ((Complex.continuous_re.tendsto s).eventually
        (Ioo_mem_nhds (by linarith) hs1))
    filter_upwards [hstrip] with z hz
    simpa only [burnolZ] using
      (hasMellin_burnolModelKernel theta z hz.1 hz.2).2
  calc
    iteratedDeriv n
        (fun z : ℂ => burnolDilationFactor theta z * burnolZ z) s =
      iteratedDeriv n
        (mellin (fun t : ℝ => (burnolModelKernel theta t : ℂ))) s :=
      (heq.iteratedDeriv_eq n).symm
    _ = mellin (fun t : ℝ =>
        (Real.log t : ℂ) ^ n * (burnolModelKernel theta t : ℂ)) s :=
      iteratedDeriv_mellin_burnolModelKernel_eq_logPow theta n hs0 (by linarith)

/-- The analytic function whose boundary derivatives occur in Burnol's pairing. -/
def burnolBoundaryPairingSource
    (theta : burnolContinuousParameter) (w : ℂ) : ℂ :=
  ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w) * burnolZ (1 - w)

/-- Burnol's direct source function `theta^(z - 1/2) Z(z)` for the boundary pairing. -/
def burnolDirectPairingSource
    (theta : burnolContinuousParameter) (z : ℂ) : ℂ :=
  ((theta : ℝ) : ℂ) ^ (z - (1 / 2 : ℂ)) * burnolZ z

theorem burnolBoundaryPairingSource_eq_normalized
    (theta : burnolContinuousParameter) (w : ℂ) :
    burnolBoundaryPairingSource theta w =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
        (burnolDilationFactor theta (1 - w) * burnolZ (1 - w)) := by
  rw [burnolBoundaryPairingSource, ← mul_assoc,
    burnol_normalizedDilationFactor_one_sub]

/-- The `k`-th derivative of Burnol's source pairing is the normalized `k`-th logarithmic
Mellin moment, including the sign from `s = 1 - w`. -/
theorem iteratedDeriv_burnolBoundaryPairingSource_eq_mellin_log
    (theta : burnolContinuousParameter) (w : ℂ) (k : ℕ)
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    iteratedDeriv k (burnolBoundaryPairingSource theta) w =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) * ((-1 : ℂ) ^ k *
        mellin (fun t : ℝ =>
          (Real.log t : ℂ) ^ k * (burnolModelKernel theta t : ℂ)) (1 - w)) := by
  let F : ℂ → ℂ := fun z => burnolDilationFactor theta z * burnolZ z
  have hsource : burnolBoundaryPairingSource theta =
      fun z : ℂ => ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) * F (1 - z) := by
    funext z
    exact burnolBoundaryPairingSource_eq_normalized theta z
  have hs0 : (3 / 8 : ℝ) < (1 - w).re := by
    change (3 / 8 : ℝ) < 1 - w.re
    linarith
  have hs1 : (1 - w).re < 1 := by
    change 1 - w.re < 1
    linarith
  rw [hsource]
  rw [iteratedDeriv_const_mul_field]
  have hcomp := congrFun (iteratedDeriv_comp_const_sub k F 1) w
  rw [hcomp]
  change ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
      (((-1 : ℂ) ^ k) * iteratedDeriv k F (1 - w)) = _
  rw [iteratedDeriv_burnolModelKernelMellin_eq_logPow theta k hs0 hs1]

theorem inner_normalizedModelKernel_burnolPreY_eq_mellin_log
    (lambda : ℝ) (theta : burnolContinuousParameter) (w : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) (hw : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w k) =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) * ((-1 : ℂ) ^ k *
        mellin (fun t : ℝ =>
          (Real.log t : ℂ) ^ k * (burnolModelKernel theta t : ℂ)) (1 - w)) := by
  rw [inner_normalizedModelKernel_burnolPreY
      lambda theta w k hlambdaTheta,
    inner_normalizedModelKernel_burnolPsiL2_eq_mellin_log theta w k hw]

/-- Exact all-order pre-boundary pairing in Burnol's source parameter. -/
theorem inner_normalizedModelKernel_burnolPreY_eq_iteratedDeriv
    (lambda : ℝ) (theta : burnolContinuousParameter) (w : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ))
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w k) =
      iteratedDeriv k (burnolBoundaryPairingSource theta) w := by
  rw [inner_normalizedModelKernel_burnolPreY_eq_mellin_log
      lambda theta w k hlambdaTheta hwHalf,
    iteratedDeriv_burnolBoundaryPairingSource_eq_mellin_log
      theta w k hw0 hwHalf]

theorem inner_normalizedModelKernel_burnolPsiL2_zero_eq_Z
    (theta : burnolContinuousParameter) (w : ℂ)
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPsiL2 w 0) =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
        (burnolDilationFactor theta (1 - w) * burnolZ (1 - w)) := by
  have hs0 : 0 < (1 - w).re := by
    change 0 < 1 - w.re
    linarith
  have hs1 : (1 - w).re < 1 := by
    change 1 - w.re < 1
    linarith
  rw [inner_normalizedModelKernel_burnolPsiL2_zero_eq_mellin theta w hwHalf,
    (hasMellin_burnolModelKernel theta (1 - w) hs0 hs1).2]
  rfl

theorem inner_normalizedModelKernel_burnolPreY_zero_eq_Z
    (lambda : ℝ) (theta : burnolContinuousParameter) (w : ℂ)
    (hlambdaTheta : lambda ≤ (theta : ℝ))
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w 0) =
      ((Real.sqrt (theta : ℝ))⁻¹ : ℂ) *
        (burnolDilationFactor theta (1 - w) * burnolZ (1 - w)) := by
  rw [inner_normalizedModelKernel_burnolPreY
      lambda theta w 0 hlambdaTheta,
    inner_normalizedModelKernel_burnolPsiL2_zero_eq_Z theta w hw0 hwHalf]

theorem inner_normalizedModelKernel_burnolPsiL2_zero_eq_source
    (theta : burnolContinuousParameter) (w : ℂ)
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPsiL2 w 0) =
      ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w) * burnolZ (1 - w) := by
  rw [inner_normalizedModelKernel_burnolPsiL2_zero_eq_Z theta w hw0 hwHalf,
    ← mul_assoc, burnol_normalizedDilationFactor_one_sub]

theorem inner_normalizedModelKernel_burnolPreY_zero_eq_source
    (lambda : ℝ) (theta : burnolContinuousParameter) (w : ℂ)
    (hlambdaTheta : lambda ≤ (theta : ℝ))
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w 0) =
      ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w) * burnolZ (1 - w) := by
  rw [inner_normalizedModelKernel_burnolPreY_zero_eq_Z
      lambda theta w hlambdaTheta hw0 hwHalf,
    ← mul_assoc, burnol_normalizedDilationFactor_one_sub]

/-! ## Burnol's oscillatory continuation -/

/-- The logarithmic-power weight in Burnol's original truncated definition of `phi`. -/
def burnolPhiSourceWeight (w : ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  (Real.log v⁻¹ : ℂ) ^ k * ((v : ℂ) ^ (-w))

/-- The sinc kernel differentiated in Burnol's original truncated definition. -/
def burnolPhiSourceSinc (t v : ℝ) : ℂ :=
  ((Real.sin (2 * Real.pi * t / v) / (Real.pi * t / v) : ℝ) : ℂ)

/-- Burnol's original `delta`-truncated oscillatory integral. -/
def burnolPhiTruncated (delta : ℝ) (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ∫ v in delta..1,
    burnolPhiSourceWeight w k v * deriv (burnolPhiSourceSinc t) v

theorem burnolPhiSourceWeight_zero (w : ℂ) (v : ℝ) :
    burnolPhiSourceWeight w 0 v = (v : ℂ) ^ (-w) := by
  simp [burnolPhiSourceWeight]

theorem differentiableAt_burnolPhiSourceSinc
    {t v : ℝ} (ht : t ≠ 0) (hv : v ≠ 0) :
    DifferentiableAt ℝ (burnolPhiSourceSinc t) v := by
  unfold burnolPhiSourceSinc
  have harg : DifferentiableAt ℝ (fun x : ℝ => 2 * Real.pi * t / x) v :=
    differentiableAt_const (c := 2 * Real.pi * t) |>.div differentiableAt_id hv
  have hden : DifferentiableAt ℝ (fun x : ℝ => Real.pi * t / x) v :=
    differentiableAt_const (c := Real.pi * t) |>.div differentiableAt_id hv
  have hquot : DifferentiableAt ℝ
      (fun x : ℝ => Real.sin (2 * Real.pi * t / x) / (Real.pi * t / x)) v :=
    harg.sin.div hden (div_ne_zero (mul_ne_zero Real.pi_ne_zero ht) hv)
  exact Complex.ofRealCLM.differentiableAt.comp v hquot

theorem hasDerivAt_burnolPhiSourceSinc
    {t v : ℝ} (ht : t ≠ 0) (hv : v ≠ 0) :
    HasDerivAt (burnolPhiSourceSinc t)
      (deriv (burnolPhiSourceSinc t) v) v :=
  (differentiableAt_burnolPhiSourceSinc ht hv).hasDerivAt

theorem contDiffOn_burnolPhiSourceSinc
    {t : ℝ} (ht : t ≠ 0) :
    ContDiffOn ℝ (⊤ : WithTop ℕ∞) (burnolPhiSourceSinc t) (Ioi 0) := by
  have harg : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun v : ℝ => 2 * Real.pi * t / v) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun v hv => ne_of_gt hv)
  have hden : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun v : ℝ => Real.pi * t / v) (Ioi 0) :=
    contDiffOn_const.div contDiffOn_id (fun v hv => ne_of_gt hv)
  have hquot : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      (fun v : ℝ => Real.sin (2 * Real.pi * t / v) / (Real.pi * t / v))
      (Ioi 0) :=
    (Real.contDiff_sin.comp_contDiffOn harg).div hden fun v hv =>
      div_ne_zero (mul_ne_zero Real.pi_ne_zero ht) (ne_of_gt hv)
  unfold burnolPhiSourceSinc
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn hquot

theorem continuousOn_deriv_burnolPhiSourceSinc
    {t : ℝ} (ht : t ≠ 0) :
    ContinuousOn (deriv (burnolPhiSourceSinc t)) (Ioi 0) :=
  (contDiffOn_burnolPhiSourceSinc ht).continuousOn_deriv_of_isOpen
    isOpen_Ioi (by norm_num)

/-- The polynomial-logarithmic factor produced by integration by parts in Burnol's `phi`
integral. The formula also covers `k=0`, since the first summand then vanishes. -/
def burnolPhiLogFactor (w : ℂ) (k : ℕ) (u : ℝ) : ℂ :=
  (k : ℂ) * (Real.log u : ℂ) ^ (k - 1) +
    w * (Real.log u : ℂ) ^ k

/-- The derivative of the source weight, written in the form used after integration by parts. -/
def burnolPhiSourceWeightDeriv (w : ℂ) (k : ℕ) (v : ℝ) : ℂ :=
  -burnolPhiLogFactor w k v⁻¹ * ((v : ℂ) ^ (-w - 1))

theorem hasDerivAt_burnolPhiSourceWeight
    (w : ℂ) (k : ℕ) {v : ℝ} (hw0 : 0 < w.re) (hv : v ≠ 0) :
    HasDerivAt (burnolPhiSourceWeight w k)
      (burnolPhiSourceWeightDeriv w k v) v := by
  have hw : w ≠ 0 := by
    intro hw
    rw [hw] at hw0
    norm_num at hw0
  have hlogReal : HasDerivAt (fun x : ℝ => -Real.log x) (-v⁻¹) v :=
    (Real.hasDerivAt_log hv).neg
  have hlogComplex : HasDerivAt
      (Complex.ofRealCLM ∘ fun x : ℝ => -Real.log x)
      ((-v⁻¹) • (1 : ℂ)) v :=
    Complex.ofRealCLM.hasDerivAt.scomp v hlogReal
  have hcpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-w))
      ((-w) * (v : ℂ) ^ (-w - 1)) v := by
    exact hasDerivAt_ofReal_cpow_const hv (neg_ne_zero.mpr hw)
  have hproduct := (hlogComplex.pow k).mul hcpow
  unfold burnolPhiSourceWeightDeriv
  convert hproduct using 1
  · rfl
  · funext x
    simp [burnolPhiSourceWeight, Function.comp_def, Real.log_inv]
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply, Pi.pow_apply,
      Complex.real_smul, mul_one]
    rw [burnolPhiLogFactor, Real.log_inv]
    rw [show ((v : ℂ) ^ (-w)) = (v : ℂ) * ((v : ℂ) ^ (-w - 1)) by
      calc
        ((v : ℂ) ^ (-w)) = (v : ℂ) ^ (1 + (-w - 1)) := by
          congr 1
          ring
        _ = (v : ℂ) ^ (1 : ℂ) * (v : ℂ) ^ (-w - 1) :=
          Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv)
        _ = (v : ℂ) * (v : ℂ) ^ (-w - 1) := by rw [Complex.cpow_one]]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hv]
    ring

theorem continuousOn_burnolPhiSourceWeight
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) :
    ContinuousOn (burnolPhiSourceWeight w k) (Ioi 0) := by
  intro v hv
  exact (hasDerivAt_burnolPhiSourceWeight w k hw0 (ne_of_gt hv)).continuousAt.continuousWithinAt

theorem continuousOn_burnolPhiSourceWeightDeriv
    (w : ℂ) (k : ℕ) :
    ContinuousOn (burnolPhiSourceWeightDeriv w k) (Ioi 0) := by
  intro v hv
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hinv : ContinuousAt (fun x : ℝ => x⁻¹) v := continuousAt_inv₀ hv0
  have hlogReal : ContinuousAt (fun x : ℝ => Real.log x⁻¹) v :=
    (Real.continuousAt_log (inv_ne_zero hv0)).comp hinv
  have hlogComplex : ContinuousAt (fun x : ℝ => (Real.log x⁻¹ : ℂ)) v :=
    Complex.ofRealCLM.continuous.continuousAt.comp hlogReal
  have hfactor : ContinuousAt (fun x : ℝ => burnolPhiLogFactor w k x⁻¹) v := by
    unfold burnolPhiLogFactor
    exact (continuousAt_const.mul (hlogComplex.pow (k - 1))).add
      (continuousAt_const.mul (hlogComplex.pow k))
  have hpower : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-w - 1)) v :=
    Complex.continuousAt_ofReal_cpow_const v (-w - 1) (Or.inr hv0)
  exact (hfactor.neg.mul hpower).continuousWithinAt

theorem burnolPhiTruncated_eq_integrationByParts
    {delta : ℝ} (w : ℂ) (k : ℕ) {t : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hw0 : 0 < w.re) (ht : t ≠ 0) :
    burnolPhiTruncated delta w k t =
      burnolPhiSourceWeight w k 1 * burnolPhiSourceSinc t 1 -
        burnolPhiSourceWeight w k delta * burnolPhiSourceSinc t delta -
          ∫ v in delta..1,
            burnolPhiSourceWeightDeriv w k v * burnolPhiSourceSinc t v := by
  have hsub : uIcc delta 1 ⊆ Ioi 0 := by
    rw [uIcc_of_le hdelta1]
    intro v hv
    exact hdelta0.trans_le hv.1
  have hu : ContinuousOn (burnolPhiSourceWeight w k) (uIcc delta 1) :=
    (continuousOn_burnolPhiSourceWeight w k hw0).mono hsub
  have hv : ContinuousOn (burnolPhiSourceSinc t) (uIcc delta 1) :=
    (contDiffOn_burnolPhiSourceSinc ht).continuousOn.mono hsub
  have hu' : IntervalIntegrable (burnolPhiSourceWeightDeriv w k) volume delta 1 :=
    ((continuousOn_burnolPhiSourceWeightDeriv w k).mono hsub).intervalIntegrable
  have hv' : IntervalIntegrable (deriv (burnolPhiSourceSinc t)) volume delta 1 :=
    ((continuousOn_deriv_burnolPhiSourceSinc ht).mono hsub).intervalIntegrable
  have hibp := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (𝕜 := ℂ) (E := ℂ) hu hv
    (fun v hv => hasDerivAt_burnolPhiSourceWeight w k hw0 <|
      ne_of_gt (hsub (Ioo_subset_Icc_self hv)))
    (fun v hv => hasDerivAt_burnolPhiSourceSinc ht <|
      ne_of_gt (hsub (Ioo_subset_Icc_self hv)))
    hu' hv'
  simpa [burnolPhiTruncated, smul_eq_mul] using hibp

/-- The boundary term left by integration by parts; it occurs only for `k=0`. -/
def burnolPhiBoundaryTerm (k : ℕ) (t : ℝ) : ℂ :=
  if k = 0 then (Real.sin (2 * Real.pi * t) : ℂ) / (Real.pi * t : ℝ)
  else 0

theorem burnolPhiSourceWeight_one_mul_sinc
    (w : ℂ) (k : ℕ) (t : ℝ) :
    burnolPhiSourceWeight w k 1 * burnolPhiSourceSinc t 1 =
      burnolPhiBoundaryTerm k t := by
  cases k with
  | zero =>
      simp [burnolPhiSourceWeight, burnolPhiSourceSinc,
        burnolPhiBoundaryTerm]
  | succ k =>
      simp [burnolPhiSourceWeight, burnolPhiBoundaryTerm]

/-- The source-side remainder before the substitution `u=1/v`. -/
def burnolPhiSourcePostIntegrand (w : ℂ) (k : ℕ) (t v : ℝ) : ℂ :=
  burnolPhiLogFactor w k v⁻¹ * ((v : ℂ) ^ (-w)) *
    (Real.sin (2 * Real.pi * t / v) : ℂ)

theorem neg_burnolPhiSourceWeightDeriv_mul_sinc
    (w : ℂ) (k : ℕ) {t v : ℝ} (ht : t ≠ 0) (hv : v ≠ 0) :
    -(burnolPhiSourceWeightDeriv w k v * burnolPhiSourceSinc t v) =
      (((Real.pi * t : ℝ) : ℂ)⁻¹) *
        burnolPhiSourcePostIntegrand w k t v := by
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv
  have htC : (((Real.pi * t : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero ht)
  have hcpow :
      (v : ℂ) * ((v : ℂ) ^ (-w - 1)) = (v : ℂ) ^ (-w) := by
    calc
      (v : ℂ) * ((v : ℂ) ^ (-w - 1)) =
          (v : ℂ) ^ (1 : ℂ) * (v : ℂ) ^ (-w - 1) := by rw [Complex.cpow_one]
      _ = (v : ℂ) ^ (1 + (-w - 1)) :=
        (Complex.cpow_add _ _ hvC).symm
      _ = (v : ℂ) ^ (-w) := by
        congr 1
        ring
  have hsinc : burnolPhiSourceSinc t v =
      (v : ℂ) * (Real.sin (2 * Real.pi * t / v) : ℂ) /
        ((Real.pi * t : ℝ) : ℂ) := by
    unfold burnolPhiSourceSinc
    push_cast
    field_simp [ht, hv]
  rw [burnolPhiSourceWeightDeriv, burnolPhiSourcePostIntegrand, hsinc]
  calc
    -(-burnolPhiLogFactor w k v⁻¹ * (v : ℂ) ^ (-w - 1) *
        ((v : ℂ) * (Real.sin (2 * Real.pi * t / v) : ℂ) /
          ((Real.pi * t : ℝ) : ℂ))) =
      burnolPhiLogFactor w k v⁻¹ *
        ((v : ℂ) * (v : ℂ) ^ (-w - 1)) *
          (Real.sin (2 * Real.pi * t / v) : ℂ) /
            ((Real.pi * t : ℝ) : ℂ) := by ring
    _ = burnolPhiLogFactor w k v⁻¹ * (v : ℂ) ^ (-w) *
          (Real.sin (2 * Real.pi * t / v) : ℂ) /
            ((Real.pi * t : ℝ) : ℂ) := by rw [hcpow]
    _ = (((Real.pi * t : ℝ) : ℂ)⁻¹) *
        (burnolPhiLogFactor w k v⁻¹ * (v : ℂ) ^ (-w) *
          (Real.sin (2 * Real.pi * t / v) : ℂ)) := by
      field_simp [htC]

theorem burnolPhiTruncated_eq_sourcePost
    {delta : ℝ} (w : ℂ) (k : ℕ) {t : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hw0 : 0 < w.re) (ht : t ≠ 0) :
    burnolPhiTruncated delta w k t =
      burnolPhiBoundaryTerm k t -
        burnolPhiSourceWeight w k delta * burnolPhiSourceSinc t delta +
          (((Real.pi * t : ℝ) : ℂ)⁻¹) *
            ∫ v in delta..1, burnolPhiSourcePostIntegrand w k t v := by
  rw [burnolPhiTruncated_eq_integrationByParts w k hdelta0 hdelta1 hw0 ht,
    burnolPhiSourceWeight_one_mul_sinc]
  rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvDelta : delta ≤ v := by
    rw [uIcc_of_le hdelta1] at hv
    exact hv.1
  exact neg_burnolPhiSourceWeightDeriv_mul_sinc w k ht <|
    ne_of_gt (hdelta0.trans_le hvDelta)

/-- The absolutely convergent tail integrand obtained from Burnol's defining oscillatory
integral after integration by parts and the substitution `u=1/v`. -/
def burnolPhiTailIntegrand (w : ℂ) (k : ℕ) (t u : ℝ) : ℂ :=
  burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
    (Real.sin (2 * Real.pi * t * u) : ℂ)

theorem inv_sq_smul_burnolPhiSourcePostIntegrand_inv
    (w : ℂ) (k : ℕ) (t : ℝ) {u : ℝ} (hu : 0 < u) :
    (u ^ 2)⁻¹ • burnolPhiSourcePostIntegrand w k t u⁻¹ =
      burnolPhiTailIntegrand w k t u := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0
  have harg : Complex.arg (u : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hu.le]
    exact Real.pi_ne_zero.symm
  have hinvCpow : (((u⁻¹ : ℝ) : ℂ) ^ (-w)) = (u : ℂ) ^ w := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]
    simp
  have hphase : 2 * Real.pi * t / u⁻¹ = 2 * Real.pi * t * u := by
    field_simp [hu0]
  have hpower : (((u ^ 2)⁻¹ : ℝ) : ℂ) * ((u : ℂ) ^ w) =
      (u : ℂ) ^ (w - 2) := by
    rw [Complex.cpow_sub _ _ huC, Complex.cpow_two]
    push_cast
    field_simp [huC]
  rw [burnolPhiSourcePostIntegrand, burnolPhiTailIntegrand, inv_inv,
    hinvCpow, hphase]
  rw [Complex.real_smul]
  calc
    (((u ^ 2)⁻¹ : ℝ) : ℂ) *
        (burnolPhiLogFactor w k u * (u : ℂ) ^ w *
          (Real.sin (2 * Real.pi * t * u) : ℂ)) =
      burnolPhiLogFactor w k u *
        ((((u ^ 2)⁻¹ : ℝ) : ℂ) * (u : ℂ) ^ w) *
          (Real.sin (2 * Real.pi * t * u) : ℂ) := by ring
    _ = burnolPhiLogFactor w k u * (u : ℂ) ^ (w - 2) *
        (Real.sin (2 * Real.pi * t * u) : ℂ) := by rw [hpower]

theorem intervalIntegral_burnolPhiSourcePost_eq_tail
    {delta : ℝ} (w : ℂ) (k : ℕ) (t : ℝ)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (∫ v in delta..1, burnolPhiSourcePostIntegrand w k t v) =
      ∫ u in 1..delta⁻¹, burnolPhiTailIntegrand w k t u := by
  have hdeltaInv : 1 ≤ delta⁻¹ := (one_le_inv₀ hdelta0).2 hdelta1
  have hsub : uIcc 1 delta⁻¹ ⊆ Ioi 0 := by
    rw [uIcc_of_le hdeltaInv]
    intro u hu
    exact zero_lt_one.trans_le hu.1
  have hf : ContinuousOn (fun u : ℝ => u⁻¹) (uIcc 1 delta⁻¹) := by
    intro u hu
    exact (continuousAt_inv₀ (ne_of_gt (hsub hu))).continuousWithinAt
  have hff : ∀ u ∈ Ioo (min 1 delta⁻¹) (max 1 delta⁻¹),
      HasDerivAt (fun x : ℝ => x⁻¹) (-(u ^ 2)⁻¹) u := by
    intro u hu
    exact hasDerivAt_inv <| ne_of_gt (hsub (Ioo_subset_Icc_self hu))
  have hf' : ∀ u ∈ Ioo (min 1 delta⁻¹) (max 1 delta⁻¹),
      -(u ^ 2)⁻¹ ≤ 0 := by
    intro u hu
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg u))
  have hsubst := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
    (E := ℂ) (a := 1) (b := delta⁻¹)
    (f := fun u : ℝ => u⁻¹) (f' := fun u : ℝ => -(u ^ 2)⁻¹)
    (g := burnolPhiSourcePostIntegrand w k t) hf hff hf'
  have hleft :
      (∫ u in 1..delta⁻¹,
        (-(u ^ 2)⁻¹) • burnolPhiSourcePostIntegrand w k t u⁻¹) =
        -∫ u in 1..delta⁻¹, burnolPhiTailIntegrand w k t u := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    calc
      (-(u ^ 2)⁻¹) • burnolPhiSourcePostIntegrand w k t u⁻¹ =
          -((u ^ 2)⁻¹ • burnolPhiSourcePostIntegrand w k t u⁻¹) := by
        exact neg_smul _ _
      _ = -burnolPhiTailIntegrand w k t u := by
        rw [inv_sq_smul_burnolPhiSourcePostIntegrand_inv w k t (hsub hu)]
  apply neg_inj.mp
  calc
    -(∫ v in delta..1, burnolPhiSourcePostIntegrand w k t v) =
        ∫ v in 1..delta, burnolPhiSourcePostIntegrand w k t v := by
      exact (intervalIntegral.integral_symm delta 1).symm
    _ = ∫ u in 1..delta⁻¹,
          (-(u ^ 2)⁻¹) • burnolPhiSourcePostIntegrand w k t u⁻¹ :=
      by simpa [Function.comp_def] using hsubst.symm
    _ = -∫ u in 1..delta⁻¹, burnolPhiTailIntegrand w k t u := hleft

theorem burnolPhiTruncated_eq_finiteTail
    {delta : ℝ} (w : ℂ) (k : ℕ) {t : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hw0 : 0 < w.re) (ht : t ≠ 0) :
    burnolPhiTruncated delta w k t =
      burnolPhiBoundaryTerm k t -
        burnolPhiSourceWeight w k delta * burnolPhiSourceSinc t delta +
          (((Real.pi * t : ℝ) : ℂ)⁻¹) *
            ∫ u in 1..delta⁻¹, burnolPhiTailIntegrand w k t u := by
  rw [burnolPhiTruncated_eq_sourcePost w k hdelta0 hdelta1 hw0 ht,
    intervalIntegral_burnolPhiSourcePost_eq_tail w k t hdelta0 hdelta1]

theorem tendsto_abs_log_rpow_mul_rpow_nhdsGT_zero
    (k : ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun x : ℝ => |Real.log x| ^ (k : ℝ) * x ^ alpha)
      (𝓝[>] 0) (𝓝 0) := by
  let s : ℝ := -alpha / 2
  have hs : s < 0 := by
    dsimp only [s]
    linarith
  have hsmall := isLittleO_abs_log_rpow_rpow_nhdsGT_zero (k : ℝ) hs
  have hprod := hsmall.mul_isBigO
    (Asymptotics.isBigO_refl (fun x : ℝ => x ^ alpha) (𝓝[>] 0))
  have hsexp : 0 < s + alpha := by
    dsimp only [s]
    linarith
  have hrpow : Tendsto (fun x : ℝ => x ^ (s + alpha)) (𝓝[>] 0) (𝓝 0) := by
    have hcont := (Real.continuous_rpow_const hsexp.le).tendsto 0
    have hle : (𝓝[>] (0 : ℝ)) ≤ 𝓝 0 := inf_le_left
    have hcontWithin := hcont.mono_left hle
    simpa [Real.zero_rpow hsexp.ne'] using hcontWithin
  have hcomparison : Tendsto (fun x : ℝ => x ^ s * x ^ alpha)
      (𝓝[>] 0) (𝓝 0) := by
    apply hrpow.congr'
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    exact Real.rpow_add hx.out s alpha
  exact hprod.trans_tendsto hcomparison

theorem norm_burnolPhiSourceSinc_le
    {t delta : ℝ} (ht : t ≠ 0) (hdelta : 0 < delta) :
    ‖burnolPhiSourceSinc t delta‖ ≤ delta / |Real.pi * t| := by
  have hden : 0 < |Real.pi * t| :=
    abs_pos.mpr (mul_ne_zero Real.pi_ne_zero ht)
  have hquotDen : 0 < |Real.pi * t| / delta := div_pos hden hdelta
  rw [burnolPhiSourceSinc, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_div, abs_of_pos hdelta]
  calc
    |Real.sin (2 * Real.pi * t / delta)| / (|Real.pi * t| / delta) ≤
        1 / (|Real.pi * t| / delta) :=
      (div_le_div_iff_of_pos_right hquotDen).2 (Real.abs_sin_le_one _)
    _ = delta / |Real.pi * t| := by field_simp

theorem norm_burnolPhiSourceWeight_of_pos
    (w : ℂ) (k : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ‖burnolPhiSourceWeight w k delta‖ =
      |Real.log delta| ^ k * delta ^ (-w.re) := by
  rw [burnolPhiSourceWeight, norm_mul, norm_pow, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos hdelta, Complex.neg_re,
    Real.norm_eq_abs, Real.log_inv, abs_neg]

theorem norm_burnolPhiLowerBoundary_le
    (w : ℂ) (k : ℕ) {t delta : ℝ} (ht : t ≠ 0) (hdelta : 0 < delta) :
    ‖burnolPhiSourceWeight w k delta * burnolPhiSourceSinc t delta‖ ≤
      |Real.pi * t|⁻¹ *
        (|Real.log delta| ^ (k : ℝ) * delta ^ (1 - w.re)) := by
  rw [norm_mul, norm_burnolPhiSourceWeight_of_pos w k hdelta]
  have hweight0 : 0 ≤ |Real.log delta| ^ k * delta ^ (-w.re) :=
    mul_nonneg (pow_nonneg (abs_nonneg _) k) (Real.rpow_nonneg hdelta.le _)
  have hpower : delta ^ (-w.re) * delta = delta ^ (1 - w.re) := by
    calc
      delta ^ (-w.re) * delta = delta ^ (-w.re) * delta ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = delta ^ (-w.re + 1) := (Real.rpow_add hdelta _ _).symm
      _ = delta ^ (1 - w.re) := by
        congr 1
        ring
  calc
    (|Real.log delta| ^ k * delta ^ (-w.re)) *
        ‖burnolPhiSourceSinc t delta‖ ≤
      (|Real.log delta| ^ k * delta ^ (-w.re)) *
        (delta / |Real.pi * t|) :=
      mul_le_mul_of_nonneg_left (norm_burnolPhiSourceSinc_le ht hdelta) hweight0
    _ = |Real.pi * t|⁻¹ *
        (|Real.log delta| ^ (k : ℝ) * delta ^ (1 - w.re)) := by
      rw [← Real.rpow_natCast]
      rw [div_eq_mul_inv]
      calc
        (|Real.log delta| ^ (k : ℝ) * delta ^ (-w.re)) *
            (delta * |Real.pi * t|⁻¹) =
          |Real.pi * t|⁻¹ * |Real.log delta| ^ (k : ℝ) *
            (delta ^ (-w.re) * delta) := by ring
        _ = |Real.pi * t|⁻¹ *
            (|Real.log delta| ^ (k : ℝ) * delta ^ (1 - w.re)) := by
          rw [hpower]
          ring

theorem tendsto_burnolPhiLowerBoundary_nhdsGT_zero
    (w : ℂ) (k : ℕ) {t : ℝ} (ht : t ≠ 0) (hw1 : w.re < 1) :
    Tendsto (fun delta : ℝ =>
      burnolPhiSourceWeight w k delta * burnolPhiSourceSinc t delta)
      (𝓝[>] 0) (𝓝 0) := by
  have halpha : 0 < 1 - w.re := sub_pos.mpr hw1
  have hmajor : Tendsto (fun delta : ℝ =>
      |Real.pi * t|⁻¹ *
        (|Real.log delta| ^ (k : ℝ) * delta ^ (1 - w.re)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using
      (tendsto_abs_log_rpow_mul_rpow_nhdsGT_zero k halpha).const_mul
        |Real.pi * t|⁻¹
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun delta => norm_nonneg _
  · filter_upwards [eventually_mem_nhdsWithin] with delta hdelta
    exact norm_burnolPhiLowerBoundary_le w k ht hdelta.out
  · exact hmajor

/-- A `t`-independent pointwise majorant for the oscillatory tail. -/
def burnolPhiTailMajor (w : ℂ) (k : ℕ) (u : ℝ) : ℝ :=
  ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2)

theorem burnolPhiLogFactor_zero (w : ℂ) (u : ℝ) :
    burnolPhiLogFactor w 0 u = w := by
  simp [burnolPhiLogFactor]

theorem measurable_burnolPhiTailIntegrand
    (w : ℂ) (k : ℕ) (t : ℝ) :
    Measurable (burnolPhiTailIntegrand w k t) := by
  unfold burnolPhiTailIntegrand burnolPhiLogFactor
  fun_prop

theorem measurable_burnolPhiTailMajor (w : ℂ) (k : ℕ) :
    Measurable (burnolPhiTailMajor w k) := by
  unfold burnolPhiTailMajor burnolPhiLogFactor
  fun_prop

theorem norm_burnolPhiTailPower_of_pos
    (w : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖((u : ℂ) ^ (w - 2))‖ = u ^ (w.re - 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  rfl

theorem norm_burnolPhiLogFactor_le
    (w : ℂ) (k : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    ‖burnolPhiLogFactor w k u‖ ≤
      (k : ℝ) * (Real.log u) ^ (k - 1) +
        ‖w‖ * (Real.log u) ^ k := by
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu
  rw [burnolPhiLogFactor]
  calc
    ‖(k : ℂ) * (Real.log u : ℂ) ^ (k - 1) +
        w * (Real.log u : ℂ) ^ k‖ ≤
      ‖(k : ℂ) * (Real.log u : ℂ) ^ (k - 1)‖ +
        ‖w * (Real.log u : ℂ) ^ k‖ := norm_add_le _ _
    _ = (k : ℝ) * (Real.log u) ^ (k - 1) +
        ‖w‖ * (Real.log u) ^ k := by
      simp only [norm_mul, norm_pow, norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hlog0]

theorem integrableOn_log_pow_mul_rpow_Ioi_one
    (j : ℕ) (a : ℝ) (ha : a < -1) :
    IntegrableOn (fun u : ℝ => (Real.log u) ^ j * u ^ a) (Ioi 1) := by
  let epsilon : ℝ := (-1 - a) / (2 * (j + 1))
  let p : ℝ := a + epsilon * j
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  have hp : p < -1 := by
    dsimp only [p, epsilon]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hj1 : (0 : ℝ) < j + 1 := by positivity
    field_simp
    nlinarith
  have hmajor : IntegrableOn
      (fun u : ℝ => (epsilon⁻¹ : ℝ) ^ j * u ^ p) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hp one_pos).const_mul ((epsilon⁻¹ : ℝ) ^ j)
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := one_pos.trans hu
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu.le
  have hlogBound : Real.log u ≤ u ^ epsilon / epsilon :=
    Real.log_le_rpow_div hu0.le hepsilon
  have hpowBound :
      (Real.log u) ^ j ≤ (u ^ epsilon / epsilon) ^ j :=
    pow_le_pow_left₀ hlog0 hlogBound j
  have htargetNonneg : 0 ≤ (Real.log u) ^ j * u ^ a :=
    mul_nonneg (pow_nonneg hlog0 j) (Real.rpow_nonneg hu0.le _)
  calc
    ‖(Real.log u) ^ j * u ^ a‖ = (Real.log u) ^ j * u ^ a := by
      rw [Real.norm_eq_abs, abs_of_nonneg htargetNonneg]
    _ ≤
        (u ^ epsilon / epsilon) ^ j * u ^ a :=
      mul_le_mul_of_nonneg_right hpowBound (Real.rpow_nonneg hu0.le _)
    _ = (epsilon⁻¹ : ℝ) ^ j * u ^ p := by
      rw [div_eq_mul_inv, mul_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul hu0.le, mul_comm (u ^ (epsilon * (j : ℝ))),
        mul_assoc, ← Real.rpow_add hu0]
      congr 2
      dsimp only [p]
      ring

theorem integrableOn_burnolPhiTailIntegrand
    (w : ℂ) (k : ℕ) (t : ℝ) (hw : w.re < 1) :
    IntegrableOn (burnolPhiTailIntegrand w k t) (Ioi 1) := by
  let a : ℝ := w.re - 2
  have ha : a < -1 := by
    dsimp only [a]
    linarith
  have hfirst : IntegrableOn (fun u : ℝ =>
      (k : ℝ) * ((Real.log u) ^ (k - 1) * u ^ a)) (Ioi 1) :=
    (integrableOn_log_pow_mul_rpow_Ioi_one (k - 1) a ha).const_mul (k : ℝ)
  have hsecond : IntegrableOn (fun u : ℝ =>
      ‖w‖ * ((Real.log u) ^ k * u ^ a)) (Ioi 1) :=
    (integrableOn_log_pow_mul_rpow_Ioi_one k a ha).const_mul ‖w‖
  have hmajor : IntegrableOn (fun u : ℝ =>
      (k : ℝ) * ((Real.log u) ^ (k - 1) * u ^ a) +
        ‖w‖ * ((Real.log u) ^ k * u ^ a)) (Ioi 1) :=
    hfirst.add hsecond
  refine hmajor.mono'
    (measurable_burnolPhiTailIntegrand w k t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := one_pos.trans hu
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu.le
  have hfactor :
      ‖burnolPhiLogFactor w k u‖ ≤
        (k : ℝ) * (Real.log u) ^ (k - 1) +
          ‖w‖ * (Real.log u) ^ k := by
    rw [burnolPhiLogFactor]
    calc
      ‖(k : ℂ) * (Real.log u : ℂ) ^ (k - 1) +
          w * (Real.log u : ℂ) ^ k‖ ≤
        ‖(k : ℂ) * (Real.log u : ℂ) ^ (k - 1)‖ +
          ‖w * (Real.log u : ℂ) ^ k‖ := norm_add_le _ _
      _ = (k : ℝ) * (Real.log u) ^ (k - 1) +
          ‖w‖ * (Real.log u) ^ k := by
        simp only [norm_mul, norm_pow, norm_natCast, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hlog0]
  have hpower0 : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le _
  have hsin : |Real.sin (2 * Real.pi * t * u)| ≤ 1 := Real.abs_sin_le_one _
  rw [burnolPhiTailIntegrand, norm_mul, norm_mul,
    norm_burnolPhiTailPower_of_pos w hu0, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖burnolPhiLogFactor w k u‖ * u ^ a *
        |Real.sin (2 * Real.pi * t * u)| ≤
      ‖burnolPhiLogFactor w k u‖ * u ^ a * 1 :=
        mul_le_mul_of_nonneg_left hsin (mul_nonneg (norm_nonneg _) hpower0)
    _ = ‖burnolPhiLogFactor w k u‖ * u ^ a := by ring
    _ ≤ ((k : ℝ) * (Real.log u) ^ (k - 1) +
        ‖w‖ * (Real.log u) ^ k) * u ^ a :=
      mul_le_mul_of_nonneg_right hfactor hpower0
    _ = (k : ℝ) * ((Real.log u) ^ (k - 1) * u ^ a) +
        ‖w‖ * ((Real.log u) ^ k * u ^ a) := by ring

theorem tendsto_intervalIntegral_burnolPhiTail_nhdsGT_zero
    (w : ℂ) (k : ℕ) (t : ℝ) (hw : w.re < 1) :
    Tendsto (fun delta : ℝ =>
      ∫ u in 1..delta⁻¹, burnolPhiTailIntegrand w k t u)
      (𝓝[>] 0)
      (𝓝 <| ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u) :=
  intervalIntegral_tendsto_integral_Ioi 1
    (integrableOn_burnolPhiTailIntegrand w k t hw)
    tendsto_inv_nhdsGT_zero

theorem integrableOn_burnolPhiTailMajor
    (w : ℂ) (k : ℕ) (hw : w.re < 1) :
    IntegrableOn (burnolPhiTailMajor w k) (Ioi 1) := by
  let a : ℝ := w.re - 2
  have ha : a < -1 := by
    dsimp only [a]
    linarith
  have hfirst : IntegrableOn (fun u : ℝ =>
      (k : ℝ) * ((Real.log u) ^ (k - 1) * u ^ a)) (Ioi 1) :=
    (integrableOn_log_pow_mul_rpow_Ioi_one (k - 1) a ha).const_mul (k : ℝ)
  have hsecond : IntegrableOn (fun u : ℝ =>
      ‖w‖ * ((Real.log u) ^ k * u ^ a)) (Ioi 1) :=
    (integrableOn_log_pow_mul_rpow_Ioi_one k a ha).const_mul ‖w‖
  have hmajor : IntegrableOn (fun u : ℝ =>
      (k : ℝ) * ((Real.log u) ^ (k - 1) * u ^ a) +
        ‖w‖ * ((Real.log u) ^ k * u ^ a)) (Ioi 1) :=
    hfirst.add hsecond
  refine hmajor.mono'
    (measurable_burnolPhiTailMajor w k).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := one_pos.trans hu
  have hfactor := norm_burnolPhiLogFactor_le w k hu.le
  have hpower0 : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le _
  have htarget0 : 0 ≤ burnolPhiTailMajor w k u :=
    mul_nonneg (norm_nonneg _) hpower0
  calc
    ‖burnolPhiTailMajor w k u‖ = burnolPhiTailMajor w k u := by
      rw [Real.norm_eq_abs, abs_of_nonneg htarget0]
    _ ≤ ((k : ℝ) * (Real.log u) ^ (k - 1) +
        ‖w‖ * (Real.log u) ^ k) * u ^ a :=
      mul_le_mul_of_nonneg_right hfactor hpower0
    _ = (k : ℝ) * ((Real.log u) ^ (k - 1) * u ^ a) +
        ‖w‖ * ((Real.log u) ^ k * u ^ a) := by
      ring

theorem norm_burnolPhiTailIntegrand_le_major
    (w : ℂ) (k : ℕ) (t : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖burnolPhiTailIntegrand w k t u‖ ≤ burnolPhiTailMajor w k u := by
  have hpower0 : 0 ≤ u ^ (w.re - 2) := Real.rpow_nonneg hu.le _
  have hsin : |Real.sin (2 * Real.pi * t * u)| ≤ 1 := Real.abs_sin_le_one _
  rw [burnolPhiTailIntegrand, burnolPhiTailMajor, norm_mul, norm_mul,
    norm_burnolPhiTailPower_of_pos w hu, Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) *
        |Real.sin (2 * Real.pi * t * u)| ≤
      ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) * 1 :=
        mul_le_mul_of_nonneg_left hsin (mul_nonneg (norm_nonneg _) hpower0)
    _ = ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) := by ring

theorem norm_integral_burnolPhiTailIntegrand_le_major
    (w : ℂ) (k : ℕ) (t : ℝ) (hw : w.re < 1) :
    ‖∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u‖ ≤
      ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u := by
  exact norm_integral_le_of_norm_le
    (integrableOn_burnolPhiTailMajor w k hw)
    (ae_restrict_mem measurableSet_Ioi |>.mono fun u hu =>
      norm_burnolPhiTailIntegrand_le_major w k t (one_pos.trans hu))

/-- Burnol's oscillatory continuation, expressed by its absolutely convergent post-integration-
by-parts integral on the source domain `Re(w)<1`. -/
def burnolPhi (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  burnolPhiBoundaryTerm k t +
    ((Real.pi * t : ℝ) : ℂ)⁻¹ *
      ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u

/-- The `j`-th term in Burnol's explicit small-`t` correction series. The `j=0` term
vanishes, so summing over all naturals is the same as the source sum over `j>=1`. -/
def burnolPhiSeriesCoreTerm (w : ℂ) (k : ℕ) (t : ℝ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j *
    (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j) /
      ((2 * j + 1).factorial : ℂ)) *
        (((2 * j : ℕ) : ℂ) / (w + (2 * j : ℕ)) ^ (k + 1))

/-- Burnol's explicit correction series after `k` parameter derivatives. -/
def burnolPhiSeriesRemainder (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  2 * (-1 : ℂ) ^ k * k.factorial *
    ∑' j : ℕ, burnolPhiSeriesCoreTerm w k t j

theorem measurable_burnolPhiSeriesCoreTerm
    (w : ℂ) (k j : ℕ) :
    Measurable (fun t : ℝ => burnolPhiSeriesCoreTerm w k t j) := by
  unfold burnolPhiSeriesCoreTerm
  fun_prop

theorem measurable_burnolPhiSeriesRemainder
    (w : ℂ) (k : ℕ) :
    Measurable (fun t : ℝ => burnolPhiSeriesRemainder w k t) := by
  unfold burnolPhiSeriesRemainder
  exact measurable_const.mul
    (Measurable.tsum fun j => measurable_burnolPhiSeriesCoreTerm w k j)

/-- The low-end correction left after replacing the tail integral by the corresponding
whole-line oscillatory integral. -/
def burnolPhiSmallCorrection (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  burnolPhiBoundaryTerm k t -
    ((Real.pi * t : ℝ) : ℂ)⁻¹ *
      ∫ u : ℝ in Ioc 0 1,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (2 * Real.pi * t * u) : ℂ)

/-- The `j`-th separated term of the sine series used in the low-end correction. -/
def burnolSineSeriesTerm (t : ℝ) (j : ℕ) (u : ℝ) : ℂ :=
  (-1 : ℂ) ^ j *
    (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℂ)) *
        ((u : ℂ) ^ (2 * j + 1))

theorem hasSum_burnolSineSeriesTerm (t u : ℝ) :
    HasSum (fun j : ℕ => burnolSineSeriesTerm t j u)
      (Real.sin (2 * Real.pi * t * u) : ℂ) := by
  have hsin := Complex.hasSum_sin (((2 * Real.pi * t * u : ℝ) : ℂ))
  convert hsin using 1
  · ext j
    rw [burnolSineSeriesTerm]
    push_cast
    rw [mul_pow]
    ring
  · simp

/-- A sine-series term after multiplication by the `k=0` correction weight. -/
def burnolPhiZeroCorrectionIntegrand
    (w : ℂ) (t : ℝ) (j : ℕ) (u : ℝ) : ℂ :=
  w * ((u : ℂ) ^ (w - 2)) * burnolSineSeriesTerm t j u

theorem hasSum_burnolPhiZeroCorrectionIntegrand
    (w : ℂ) (t u : ℝ) :
    HasSum (fun j : ℕ => burnolPhiZeroCorrectionIntegrand w t j u)
      (w * ((u : ℂ) ^ (w - 2)) *
        (Real.sin (2 * Real.pi * t * u) : ℂ)) := by
  exact (hasSum_burnolSineSeriesTerm t u).mul_left
    (w * ((u : ℂ) ^ (w - 2)))

/-- The elementary complex power integral used termwise in the correction series. -/
theorem integral_Ioc_cpow_sub_one {q : ℂ} (hq : 0 < q.re) :
    (∫ u : ℝ in Ioc 0 1, (u : ℂ) ^ (q - 1)) = q⁻¹ := by
  have hexp : -1 < (q - 1).re := by
    change -1 < q.re - 1
    linarith
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hq
    exact lt_irrefl 0 hq
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl hexp), sub_add_cancel, Complex.ofReal_one,
    Complex.one_cpow, Complex.ofReal_zero, Complex.zero_cpow hq0,
    sub_zero, div_eq_mul_inv, one_mul]

/-- The logarithmic moments of the unit-interval indicator used to differentiate the elementary
Mellin integral. -/
def burnolUnitLogMoment (n : ℕ) (u : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => (Real.log x : ℂ) ^ n) u

theorem locallyIntegrableOn_burnolUnitLogMoment (n : ℕ) :
    LocallyIntegrableOn (burnolUnitLogMoment n) (Ioi 0) := by
  let f : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hfInt : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hM := (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num)).1
    rw [MellinConvergent] at hM
    simpa [f] using hM
  have hlog : ContinuousOn (fun u : ℝ => (Real.log u : ℂ) ^ n) (Ioi 0) := by
    exact (Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun _ hu => ne_of_gt hu)).pow n
  have hproduct := hfInt.locallyIntegrableOn.mul_continuousOn
    hlog isOpen_Ioi.isLocallyClosed
  refine hproduct.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  by_cases hu1 : u ≤ 1
  · have huIoc : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hu1⟩
    simp [f, burnolUnitLogMoment, huIoc]
  · have huNot : u ∉ Ioc (0 : ℝ) 1 := fun h => hu1 h.2
    simp [f, burnolUnitLogMoment, huNot]

theorem isBigO_burnolUnitLogMoment_rpow_zero
    (n : ℕ) {b : ℝ} (hb : 0 < b) :
    burnolUnitLogMoment n =O[𝓝[>] 0] (fun u : ℝ => u ^ (-b)) := by
  have hraw :=
    (isLittleO_abs_log_rpow_rpow_nhdsGT_zero (n : ℝ) (neg_neg_of_pos hb)).isBigO
  rw [Asymptotics.isBigO_iff] at hraw ⊢
  obtain ⟨C, hC⟩ := hraw
  refine ⟨C, ?_⟩
  filter_upwards [hC, Ioc_mem_nhdsGT zero_lt_one] with u hbound hu
  rw [burnolUnitLogMoment, Set.indicator_of_mem hu, norm_pow,
    Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _)]
  calc
    |Real.log u| ^ n = |Real.log u| ^ (n : ℝ) :=
      (Real.rpow_natCast |Real.log u| n).symm
    _ = ‖|Real.log u| ^ (n : ℝ)‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    _ ≤ C * ‖u ^ (-b)‖ := hbound
    _ = C * u ^ (-b) := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _)]

theorem isBigO_burnolUnitLogMoment_rpow_top (n : ℕ) (a : ℝ) :
    burnolUnitLogMoment n =O[atTop] (fun u : ℝ => u ^ (-a)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have huNot : u ∉ Ioc (0 : ℝ) 1 := fun h => (not_le_of_gt hu) h.2
  simp [burnolUnitLogMoment, huNot]

theorem hasDerivAt_mellin_burnolUnitLogMoment
    (n : ℕ) {q : ℂ} (hq : 0 < q.re) :
    HasDerivAt (mellin (burnolUnitLogMoment n))
      (mellin (burnolUnitLogMoment (n + 1)) q) q := by
  let b : ℝ := q.re / 2
  have hb0 : 0 < b := by dsimp only [b]; linarith
  have hbq : b < q.re := by dsimp only [b]; linarith
  have hdiff := mellin_hasDerivAt_of_isBigO_rpow
    (locallyIntegrableOn_burnolUnitLogMoment n)
    (isBigO_burnolUnitLogMoment_rpow_top n (q.re + 1)) (lt_add_one q.re)
    (isBigO_burnolUnitLogMoment_rpow_zero n hb0) hbq
  have hfun : (fun u : ℝ => Real.log u • burnolUnitLogMoment n u) =
      burnolUnitLogMoment (n + 1) := by
    funext u
    by_cases hu : u ∈ Ioc (0 : ℝ) 1
    · rw [burnolUnitLogMoment, burnolUnitLogMoment,
        Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      simp only [Complex.real_smul, pow_succ]
      ring
    · simp [burnolUnitLogMoment, hu]
  rw [hfun] at hdiff
  exact hdiff.2

theorem mellinConvergent_burnolUnitLogMoment
    (n : ℕ) {q : ℂ} (hq : 0 < q.re) :
    MellinConvergent (burnolUnitLogMoment n) q := by
  cases n with
  | zero =>
      have hfun : burnolUnitLogMoment 0 =
          (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
        funext u
        simp [burnolUnitLogMoment]
      rw [hfun]
      exact (hasMellin_one_Ioc hq).1
  | succ n =>
      let b : ℝ := q.re / 2
      have hb0 : 0 < b := by dsimp only [b]; linarith
      have hbq : b < q.re := by dsimp only [b]; linarith
      have hdiff := mellin_hasDerivAt_of_isBigO_rpow
        (locallyIntegrableOn_burnolUnitLogMoment n)
        (isBigO_burnolUnitLogMoment_rpow_top n (q.re + 1)) (lt_add_one q.re)
        (isBigO_burnolUnitLogMoment_rpow_zero n hb0) hbq
      have hfun : (fun u : ℝ => Real.log u • burnolUnitLogMoment n u) =
          burnolUnitLogMoment (n + 1) := by
        funext u
        by_cases hu : u ∈ Ioc (0 : ℝ) 1
        · rw [burnolUnitLogMoment, burnolUnitLogMoment,
            Set.indicator_of_mem hu, Set.indicator_of_mem hu]
          simp only [Complex.real_smul, pow_succ]
          ring
        · simp [burnolUnitLogMoment, hu]
      rw [hfun] at hdiff
      exact hdiff.1

theorem integrableOn_abs_log_pow_mul_rpow_Ioc
    (n : ℕ) {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun u : ℝ => |Real.log u| ^ n * u ^ a) (Ioc 0 1) := by
  let q : ℂ := (a + 1 : ℝ)
  have hq : 0 < q.re := by
    dsimp only [q]
    norm_num
    linarith
  have hconv := mellinConvergent_burnolUnitLogMoment n hq
  rw [MellinConvergent] at hconv
  have hnorm : IntegrableOn
      (fun u : ℝ => ‖((u : ℂ) ^ (q - 1)) • burnolUnitLogMoment n u‖)
      (Ioi 0) := hconv.norm
  have hrestricted : IntegrableOn
      (fun u : ℝ => ‖((u : ℂ) ^ (q - 1)) • burnolUnitLogMoment n u‖)
      (Ioc 0 1) :=
    IntegrableOn.mono_set hnorm Ioc_subset_Ioi_self
  refine hrestricted.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  rw [burnolUnitLogMoment, Set.indicator_of_mem hu, norm_smul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs]
  have hqexp : q - 1 = (a : ℂ) := by
    dsimp only [q]
    push_cast
    ring
  rw [hqexp, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  norm_num
  ring

theorem integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    (n : ℕ) {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun u : ℝ => (1 + |Real.log u|) ^ n * u ^ a) (Ioc 0 1) := by
  have hzero : IntegrableOn (fun u : ℝ => u ^ a) (Ioc 0 1) := by
    simpa only [pow_zero, one_mul] using
      (integrableOn_abs_log_pow_mul_rpow_Ioc 0 ha)
  have hn := integrableOn_abs_log_pow_mul_rpow_Ioc n ha
  have hmajor : IntegrableOn
      (fun u : ℝ => (2 : ℝ) ^ (n - 1) *
        (u ^ a + |Real.log u| ^ n * u ^ a)) (Ioc 0 1) :=
    (hzero.add hn).const_mul ((2 : ℝ) ^ (n - 1))
  apply Integrable.mono' hmajor
  · fun_prop
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  have hrpow : 0 ≤ u ^ a := Real.rpow_nonneg hu0.le _
  have hpow := add_pow_le (a := (1 : ℝ)) (b := |Real.log u|)
    (by norm_num) (abs_nonneg _) n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (by positivity) _) hrpow)]
  calc
    (1 + |Real.log u|) ^ n * u ^ a ≤
        ((2 : ℝ) ^ (n - 1) *
          ((1 : ℝ) ^ n + |Real.log u| ^ n)) * u ^ a :=
      mul_le_mul_of_nonneg_right hpow hrpow
    _ = (2 : ℝ) ^ (n - 1) *
        (u ^ a + |Real.log u| ^ n * u ^ a) := by ring

theorem iteratedDeriv_mellin_burnolUnitLogMoment_zero
    (n : ℕ) {q : ℂ} (hq : 0 < q.re) :
    iteratedDeriv n (mellin (burnolUnitLogMoment 0)) q =
      mellin (burnolUnitLogMoment n) q := by
  induction n generalizing q with
  | zero => simp only [iteratedDeriv_zero]
  | succ n hn =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (mellin (burnolUnitLogMoment 0)) =ᶠ[𝓝 q]
          mellin (burnolUnitLogMoment n) := by
        have hhalf : ∀ᶠ z : ℂ in 𝓝 q, 0 < z.re :=
          (Complex.continuous_re.tendsto q).eventually (Ioi_mem_nhds hq)
        filter_upwards [hhalf] with z hz
        exact hn hz
      rw [hfun.deriv_eq]
      exact (hasDerivAt_mellin_burnolUnitLogMoment n hq).deriv

theorem mellin_burnolUnitLogMoment_zero_eq_inv {q : ℂ} (hq : 0 < q.re) :
    mellin (burnolUnitLogMoment 0) q = q⁻¹ := by
  have hfun : burnolUnitLogMoment 0 =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
    funext u
    simp [burnolUnitLogMoment]
  rw [hfun]
  simpa only [one_div] using (hasMellin_one_Ioc (s := q) hq).2

theorem integral_Ioc_log_pow_mul_cpow_sub_one
    (n : ℕ) {q : ℂ} (hq : 0 < q.re) :
    (∫ u : ℝ in Ioc 0 1,
      (Real.log u : ℂ) ^ n * ((u : ℂ) ^ (q - 1))) =
        (-1 : ℂ) ^ n * n.factorial / q ^ (n + 1) := by
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hq
    exact lt_irrefl 0 hq
  have heq : mellin (burnolUnitLogMoment 0) =ᶠ[𝓝 q] Inv.inv := by
    have hhalf : ∀ᶠ z : ℂ in 𝓝 q, 0 < z.re :=
      (Complex.continuous_re.tendsto q).eventually (Ioi_mem_nhds hq)
    filter_upwards [hhalf] with z hz
    exact mellin_burnolUnitLogMoment_zero_eq_inv hz
  have hmoment : mellin (burnolUnitLogMoment n) q =
      (-1 : ℂ) ^ n * n.factorial / q ^ (n + 1) := by
    rw [← iteratedDeriv_mellin_burnolUnitLogMoment_zero n hq,
      heq.iteratedDeriv_eq n, iteratedDeriv_eq_iterate, iter_deriv_inv]
    rw [show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg_coe_of_pos q (by omega)]
    rw [div_eq_mul_inv]
  rw [← hmoment]
  rw [mellin]
  simp_rw [burnolUnitLogMoment, ← Set.indicator_smul, smul_eq_mul]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  apply integral_congr_ae
  filter_upwards with u
  ring

theorem burnolPhiZeroCorrectionIntegrand_eq_cpow
    (w : ℂ) (t : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    burnolPhiZeroCorrectionIntegrand w t j u =
      (w * (-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ))) *
        ((u : ℂ) ^ (w + (2 * j : ℕ) - 1)) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hpow :
      ((u : ℂ) ^ (w - 2)) * ((u : ℂ) ^ (2 * j + 1)) =
        (u : ℂ) ^ (w + (2 * j : ℕ) - 1) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ huC]
    congr 1
    push_cast
    ring
  rw [burnolPhiZeroCorrectionIntegrand, burnolSineSeriesTerm]
  calc
    w * ((u : ℂ) ^ (w - 2)) *
        ((-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ)) * ((u : ℂ) ^ (2 * j + 1))) =
      (w * (-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ))) *
        (((u : ℂ) ^ (w - 2)) * ((u : ℂ) ^ (2 * j + 1))) := by ring
    _ = _ := by rw [hpow]

theorem integral_burnolPhiZeroCorrectionIntegrand
    (w : ℂ) (t : ℝ) (j : ℕ) (hw0 : 0 < w.re) :
    (∫ u : ℝ in Ioc 0 1, burnolPhiZeroCorrectionIntegrand w t j u) =
      (w * (-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ))) *
        (w + (2 * j : ℕ))⁻¹ := by
  let c : ℂ := w * (-1 : ℂ) ^ j *
    (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℂ))
  have hq : 0 < (w + (2 * j : ℕ)).re := by
    rw [Complex.add_re]
    norm_num
    positivity
  calc
    (∫ u : ℝ in Ioc 0 1, burnolPhiZeroCorrectionIntegrand w t j u) =
        ∫ u : ℝ in Ioc 0 1,
          c * ((u : ℂ) ^ ((w + (2 * j : ℕ)) - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      exact burnolPhiZeroCorrectionIntegrand_eq_cpow w t j hu.1
    _ = c * ∫ u : ℝ in Ioc 0 1,
          ((u : ℂ) ^ ((w + (2 * j : ℕ)) - 1)) :=
      by rw [integral_const_mul]
    _ = c * (w + (2 * j : ℕ))⁻¹ := by
      rw [integral_Ioc_cpow_sub_one hq]
    _ = _ := rfl

/-- The scalar majorant for the odd sine-series coefficients. -/
def burnolSineSeriesNormCoeff (t : ℝ) (j : ℕ) : ℝ :=
  |2 * Real.pi * t| ^ (2 * j + 1) / (2 * j + 1).factorial

theorem burnolSineSeriesNormCoeff_nonneg (t : ℝ) (j : ℕ) :
    0 ≤ burnolSineSeriesNormCoeff t j := by
  exact div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _)

theorem summable_burnolSineSeriesNormCoeff (t : ℝ) :
    Summable (burnolSineSeriesNormCoeff t) := by
  have hexp := Real.summable_pow_div_factorial |2 * Real.pi * t|
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro i j hij
    exact Nat.mul_left_cancel (by norm_num : 0 < 2) (Nat.add_right_cancel hij)
  change Summable (fun j : ℕ =>
    |2 * Real.pi * t| ^ (2 * j + 1) / (2 * j + 1).factorial)
  exact hexp.comp_injective hinj

/-- The product majorant used to justify termwise integration of the low-end sine series. -/
def burnolPhiZeroCorrectionMajor
    (w : ℂ) (t : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  burnolSineSeriesNormCoeff t j * (‖w‖ * u ^ (w.re - 1))

theorem norm_burnolPhiZeroCorrectionIntegrand_le_major
    (w : ℂ) (t : ℝ) (j : ℕ) {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖burnolPhiZeroCorrectionIntegrand w t j u‖ ≤
      burnolPhiZeroCorrectionMajor w t j u := by
  have hpow0 : 0 ≤ u ^ (w.re - 1) := Real.rpow_nonneg hu0.le _
  have hexponents : w.re - 1 ≤ w.re + (2 * j : ℝ) - 1 := by
    have hj : (0 : ℝ) ≤ (2 * j : ℕ) := Nat.cast_nonneg _
    linarith
  have hpowLe : u ^ (w.re + (2 * j : ℝ) - 1) ≤ u ^ (w.re - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hexponents
  have hcombine :
      u ^ (w.re - 2) * u ^ (2 * j + 1 : ℕ) =
        u ^ (w.re + (2 * j : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
    congr 1
    push_cast
    ring
  simp only [burnolPhiZeroCorrectionIntegrand, burnolSineSeriesTerm,
    burnolPhiZeroCorrectionMajor, norm_mul, norm_div, norm_pow, norm_neg,
    norm_one, one_pow, norm_natCast, burnolSineSeriesNormCoeff]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
    Real.norm_eq_abs]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
  have hcoeff0 : 0 ≤
      burnolSineSeriesNormCoeff t j :=
    burnolSineSeriesNormCoeff_nonneg t j
  norm_num only [Complex.sub_re, one_mul]
  change ‖w‖ * u ^ (w.re - 2) *
      (burnolSineSeriesNormCoeff t j * u ^ (2 * j + 1)) ≤
    burnolSineSeriesNormCoeff t j * (‖w‖ * u ^ (w.re - 1))
  calc
    ‖w‖ * u ^ (w.re - 2) *
        (burnolSineSeriesNormCoeff t j * u ^ (2 * j + 1)) =
      (burnolSineSeriesNormCoeff t j * ‖w‖) *
        (u ^ (w.re - 2) * u ^ (2 * j + 1)) := by ring
    _ = (burnolSineSeriesNormCoeff t j * ‖w‖) *
        u ^ (w.re + (2 * j : ℝ) - 1) := by rw [hcombine]
    _ ≤ (burnolSineSeriesNormCoeff t j * ‖w‖) *
        u ^ (w.re - 1) :=
      mul_le_mul_of_nonneg_left hpowLe (mul_nonneg hcoeff0 (norm_nonneg w))
    _ = burnolSineSeriesNormCoeff t j *
        (‖w‖ * u ^ (w.re - 1)) := by ring

theorem integrableOn_burnolPhiZeroCorrectionMajor_tsum
    (w : ℂ) (t : ℝ) (hw0 : 0 < w.re) :
    IntegrableOn (fun u : ℝ =>
      ∑' j : ℕ, burnolPhiZeroCorrectionMajor w t j u) (Ioc 0 1) := by
  have hrpow : IntegrableOn (fun u : ℝ => u ^ (w.re - 1)) (Ioc 0 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  have hfun : (fun u : ℝ =>
      ∑' j : ℕ, burnolPhiZeroCorrectionMajor w t j u) =
      fun u : ℝ =>
        (∑' j : ℕ, burnolSineSeriesNormCoeff t j) *
          (‖w‖ * u ^ (w.re - 1)) := by
    funext u
    exact tsum_mul_right
  rw [hfun]
  have hconst := hrpow.const_mul
    ((∑' j : ℕ, burnolSineSeriesNormCoeff t j) * ‖w‖)
  exact hconst.congr <| ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by ring

theorem hasSum_integral_burnolPhiZeroCorrectionIntegrand
    (w : ℂ) (t : ℝ) (hw0 : 0 < w.re) :
    HasSum
      (fun j : ℕ =>
        ∫ u : ℝ in Ioc 0 1, burnolPhiZeroCorrectionIntegrand w t j u)
      (∫ u : ℝ in Ioc 0 1,
        w * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (2 * Real.pi * t * u) : ℂ)) := by
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (burnolPhiZeroCorrectionMajor w t)
  · intro j
    have hmeas : Measurable (burnolPhiZeroCorrectionIntegrand w t j) := by
      unfold burnolPhiZeroCorrectionIntegrand burnolSineSeriesTerm
      fun_prop
    exact hmeas.aestronglyMeasurable
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact norm_burnolPhiZeroCorrectionIntegrand_le_major w t j hu.1 hu.2
  · filter_upwards with u
    exact (summable_burnolSineSeriesNormCoeff t).mul_right
      (‖w‖ * u ^ (w.re - 1))
  · exact integrableOn_burnolPhiZeroCorrectionMajor_tsum w t hw0
  · filter_upwards with u
    exact hasSum_burnolPhiZeroCorrectionIntegrand w t u

/-- A general correction integrand, before summing the sine series. -/
def burnolPhiCorrectionIntegrand
    (w : ℂ) (k : ℕ) (t : ℝ) (j : ℕ) (u : ℝ) : ℂ :=
  burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
    burnolSineSeriesTerm t j u

theorem hasSum_burnolPhiCorrectionIntegrand
    (w : ℂ) (k : ℕ) (t u : ℝ) :
    HasSum (fun j : ℕ => burnolPhiCorrectionIntegrand w k t j u)
      (burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
        (Real.sin (2 * Real.pi * t * u) : ℂ)) := by
  exact (hasSum_burnolSineSeriesTerm t u).mul_left
    (burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)))

theorem norm_burnolPhiLogFactor_le_abs
    (w : ℂ) (k : ℕ) (u : ℝ) :
    ‖burnolPhiLogFactor w k u‖ ≤
      (k : ℝ) * |Real.log u| ^ (k - 1) +
        ‖w‖ * |Real.log u| ^ k := by
  rw [burnolPhiLogFactor]
  calc
    ‖(k : ℂ) * (Real.log u : ℂ) ^ (k - 1) +
        w * (Real.log u : ℂ) ^ k‖ ≤
      ‖(k : ℂ) * (Real.log u : ℂ) ^ (k - 1)‖ +
        ‖w * (Real.log u : ℂ) ^ k‖ := norm_add_le _ _
    _ = (k : ℝ) * |Real.log u| ^ (k - 1) +
        ‖w‖ * |Real.log u| ^ k := by
      simp only [norm_mul, norm_pow, norm_natCast, Complex.norm_real,
        Real.norm_eq_abs]

/-- The common majorant for the general correction series. -/
def burnolPhiCorrectionMajor
    (w : ℂ) (k : ℕ) (t : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  burnolSineSeriesNormCoeff t j *
    (((k : ℝ) * |Real.log u| ^ (k - 1) +
      ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1))

theorem norm_burnolPhiCorrectionIntegrand_le_major
    (w : ℂ) (k : ℕ) (t : ℝ) (j : ℕ) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖burnolPhiCorrectionIntegrand w k t j u‖ ≤
      burnolPhiCorrectionMajor w k t j u := by
  have hfactor := norm_burnolPhiLogFactor_le_abs w k u
  have hfactor0 : 0 ≤
      (k : ℝ) * |Real.log u| ^ (k - 1) +
        ‖w‖ * |Real.log u| ^ k := by positivity
  have hexponents : w.re - 1 ≤ w.re + (2 * j : ℝ) - 1 := by
    have hj : (0 : ℝ) ≤ (2 * j : ℕ) := Nat.cast_nonneg _
    linarith
  have hpowLe : u ^ (w.re + (2 * j : ℝ) - 1) ≤ u ^ (w.re - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hexponents
  have hcombine :
      u ^ (w.re - 2) * u ^ (2 * j + 1 : ℕ) =
        u ^ (w.re + (2 * j : ℝ) - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hu0]
    congr 1
    push_cast
    ring
  have hproduct :
      ‖burnolPhiLogFactor w k u‖ *
          u ^ (w.re + (2 * j : ℝ) - 1) ≤
        ((k : ℝ) * |Real.log u| ^ (k - 1) +
          ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1) := by
    exact mul_le_mul hfactor hpowLe
      (Real.rpow_nonneg hu0.le _) hfactor0
  have hcoeff0 := burnolSineSeriesNormCoeff_nonneg t j
  simp only [burnolPhiCorrectionIntegrand, burnolSineSeriesTerm,
    burnolPhiCorrectionMajor, norm_mul, norm_div, norm_pow, norm_neg,
    norm_one, one_pow, norm_natCast, burnolSineSeriesNormCoeff]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.norm_real,
    Real.norm_eq_abs]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
  norm_num only [Complex.sub_re, one_mul]
  change ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) *
      (burnolSineSeriesNormCoeff t j * u ^ (2 * j + 1)) ≤
    burnolSineSeriesNormCoeff t j *
      (((k : ℝ) * |Real.log u| ^ (k - 1) +
        ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1))
  calc
    ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) *
        (burnolSineSeriesNormCoeff t j * u ^ (2 * j + 1)) =
      burnolSineSeriesNormCoeff t j *
        (‖burnolPhiLogFactor w k u‖ *
          (u ^ (w.re - 2) * u ^ (2 * j + 1))) := by ring
    _ = burnolSineSeriesNormCoeff t j *
        (‖burnolPhiLogFactor w k u‖ *
          u ^ (w.re + (2 * j : ℝ) - 1)) := by rw [hcombine]
    _ ≤ burnolSineSeriesNormCoeff t j *
        (((k : ℝ) * |Real.log u| ^ (k - 1) +
          ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1)) :=
      mul_le_mul_of_nonneg_left hproduct hcoeff0

theorem integrableOn_burnolPhiCorrectionMajor_tsum
    (w : ℂ) (k : ℕ) (t : ℝ) (hw0 : 0 < w.re) :
    IntegrableOn (fun u : ℝ =>
      ∑' j : ℕ, burnolPhiCorrectionMajor w k t j u) (Ioc 0 1) := by
  have ha : -1 < w.re - 1 := by linarith
  have hfirst : IntegrableOn (fun u : ℝ =>
      (k : ℝ) * (|Real.log u| ^ (k - 1) * u ^ (w.re - 1))) (Ioc 0 1) :=
    (integrableOn_abs_log_pow_mul_rpow_Ioc (k - 1) ha).const_mul (k : ℝ)
  have hsecond : IntegrableOn (fun u : ℝ =>
      ‖w‖ * (|Real.log u| ^ k * u ^ (w.re - 1))) (Ioc 0 1) :=
    (integrableOn_abs_log_pow_mul_rpow_Ioc k ha).const_mul ‖w‖
  have hbase : IntegrableOn (fun u : ℝ =>
      ((k : ℝ) * |Real.log u| ^ (k - 1) +
        ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1)) (Ioc 0 1) := by
    exact (hfirst.add hsecond).congr <|
      ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => by
        simp only [Pi.add_apply]
        ring
  have hfun : (fun u : ℝ =>
      ∑' j : ℕ, burnolPhiCorrectionMajor w k t j u) =
      fun u : ℝ =>
        (∑' j : ℕ, burnolSineSeriesNormCoeff t j) *
          (((k : ℝ) * |Real.log u| ^ (k - 1) +
            ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1)) := by
    funext u
    exact tsum_mul_right
  rw [hfun]
  exact hbase.const_mul (∑' j : ℕ, burnolSineSeriesNormCoeff t j)

theorem hasSum_integral_burnolPhiCorrectionIntegrand
    (w : ℂ) (k : ℕ) (t : ℝ) (hw0 : 0 < w.re) :
    HasSum
      (fun j : ℕ =>
        ∫ u : ℝ in Ioc 0 1, burnolPhiCorrectionIntegrand w k t j u)
      (∫ u : ℝ in Ioc 0 1,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (2 * Real.pi * t * u) : ℂ)) := by
  apply MeasureTheory.hasSum_integral_of_dominated_convergence
    (burnolPhiCorrectionMajor w k t)
  · intro j
    have hmeas : Measurable (burnolPhiCorrectionIntegrand w k t j) := by
      unfold burnolPhiCorrectionIntegrand burnolPhiLogFactor burnolSineSeriesTerm
      fun_prop
    exact hmeas.aestronglyMeasurable
  · intro j
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact norm_burnolPhiCorrectionIntegrand_le_major w k t j hu.1 hu.2
  · filter_upwards with u
    exact (summable_burnolSineSeriesNormCoeff t).mul_right
      (((k : ℝ) * |Real.log u| ^ (k - 1) +
        ‖w‖ * |Real.log u| ^ k) * u ^ (w.re - 1))
  · exact integrableOn_burnolPhiCorrectionMajor_tsum w k t hw0
  · filter_upwards with u
    exact hasSum_burnolPhiCorrectionIntegrand w k t u

theorem integrableOn_log_pow_mul_cpow_sub_one
    (n : ℕ) {q : ℂ} (hq : 0 < q.re) :
    IntegrableOn (fun u : ℝ =>
      (Real.log u : ℂ) ^ n * ((u : ℂ) ^ (q - 1))) (Ioc 0 1) := by
  have hmajor := integrableOn_abs_log_pow_mul_rpow_Ioc n
    (show -1 < q.re - 1 by linarith)
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu.1]
  norm_num

theorem integral_Ioc_burnolPhiLogFactor_mul_cpow
    (w : ℂ) {k j : ℕ} (hw0 : 0 < w.re) (hk : 1 ≤ k) :
    (∫ u : ℝ in Ioc 0 1,
      burnolPhiLogFactor w k u *
        ((u : ℂ) ^ ((w + (2 * j : ℕ)) - 1))) =
      -((-1 : ℂ) ^ k * k.factorial *
        (((2 * j : ℕ) : ℂ) / (w + (2 * j : ℕ)) ^ (k + 1))) := by
  let q : ℂ := w + (2 * j : ℕ)
  have hq : 0 < q.re := by
    dsimp only [q]
    rw [Complex.add_re]
    norm_num
    positivity
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hq
    exact lt_irrefl 0 hq
  have hkm1 := integrableOn_log_pow_mul_cpow_sub_one (k - 1) hq
  have hkInt := integrableOn_log_pow_mul_cpow_sub_one k hq
  calc
    (∫ u : ℝ in Ioc 0 1,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (q - 1))) =
      ∫ u : ℝ in Ioc 0 1,
        (k : ℂ) * ((Real.log u : ℂ) ^ (k - 1) * ((u : ℂ) ^ (q - 1))) +
          w * ((Real.log u : ℂ) ^ k * ((u : ℂ) ^ (q - 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      unfold burnolPhiLogFactor
      ring
    _ = (k : ℂ) * (∫ u : ℝ in Ioc 0 1,
          (Real.log u : ℂ) ^ (k - 1) * ((u : ℂ) ^ (q - 1))) +
        w * (∫ u : ℝ in Ioc 0 1,
          (Real.log u : ℂ) ^ k * ((u : ℂ) ^ (q - 1))) := by
      rw [integral_add (hkm1.const_mul (k : ℂ)) (hkInt.const_mul w),
        integral_const_mul, integral_const_mul]
    _ = (k : ℂ) *
          (((-1 : ℂ) ^ (k - 1) * (k - 1).factorial) / q ^ k) +
        w * (((-1 : ℂ) ^ k * k.factorial) / q ^ (k + 1)) := by
      rw [integral_Ioc_log_pow_mul_cpow_sub_one (k - 1) hq,
        integral_Ioc_log_pow_mul_cpow_sub_one k hq]
      rw [Nat.sub_add_cancel hk]
    _ = -((-1 : ℂ) ^ k * k.factorial *
        (((2 * j : ℕ) : ℂ) / q ^ (k + 1))) := by
      cases k with
      | zero => omega
      | succ n =>
          simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul,
            Nat.cast_add, Nat.cast_one, pow_succ]
          field_simp [hq0]
          dsimp only [q]
          push_cast
          ring

theorem burnolPhiCorrectionIntegrand_eq_cpow
    (w : ℂ) (k : ℕ) (t : ℝ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    burnolPhiCorrectionIntegrand w k t j u =
      ((-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ))) *
        (burnolPhiLogFactor w k u *
          ((u : ℂ) ^ ((w + (2 * j : ℕ)) - 1))) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hpow :
      ((u : ℂ) ^ (w - 2)) * ((u : ℂ) ^ (2 * j + 1)) =
        (u : ℂ) ^ (w + (2 * j : ℕ) - 1) := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ huC]
    congr 1
    push_cast
    ring
  rw [burnolPhiCorrectionIntegrand, burnolSineSeriesTerm]
  calc
    burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
        ((-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ)) * ((u : ℂ) ^ (2 * j + 1))) =
      ((-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ))) *
        (burnolPhiLogFactor w k u *
          (((u : ℂ) ^ (w - 2)) * ((u : ℂ) ^ (2 * j + 1)))) := by ring
    _ = _ := by rw [hpow]

theorem integral_burnolPhiCorrectionIntegrand
    (w : ℂ) (t : ℝ) {k : ℕ} (j : ℕ)
    (hw0 : 0 < w.re) (hk : 1 ≤ k) :
    (∫ u : ℝ in Ioc 0 1, burnolPhiCorrectionIntegrand w k t j u) =
      -(((-1 : ℂ) ^ j *
          (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
            ((2 * j + 1).factorial : ℂ))) *
        ((-1 : ℂ) ^ k * k.factorial *
          (((2 * j : ℕ) : ℂ) /
            (w + (2 * j : ℕ)) ^ (k + 1)))) := by
  let c : ℂ := (-1 : ℂ) ^ j *
    (((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j + 1) /
      ((2 * j + 1).factorial : ℂ))
  calc
    (∫ u : ℝ in Ioc 0 1, burnolPhiCorrectionIntegrand w k t j u) =
      ∫ u : ℝ in Ioc 0 1,
        c * (burnolPhiLogFactor w k u *
          ((u : ℂ) ^ ((w + (2 * j : ℕ)) - 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      exact burnolPhiCorrectionIntegrand_eq_cpow w k t j hu.1
    _ = c * (∫ u : ℝ in Ioc 0 1,
        burnolPhiLogFactor w k u *
          ((u : ℂ) ^ ((w + (2 * j : ℕ)) - 1))) := by
      rw [integral_const_mul]
    _ = c * -((-1 : ℂ) ^ k * k.factorial *
        (((2 * j : ℕ) : ℂ) /
          (w + (2 * j : ℕ)) ^ (k + 1))) := by
      rw [integral_Ioc_burnolPhiLogFactor_mul_cpow w hw0 hk]
    _ = _ := by ring

theorem burnolPhiCorrection_series_term
    (w : ℂ) {k : ℕ} {t : ℝ} (j : ℕ)
    (hw0 : 0 < w.re) (hk : 1 ≤ k) (ht : t ≠ 0) :
    -((Real.pi * t : ℝ) : ℂ)⁻¹ *
        (∫ u : ℝ in Ioc 0 1,
          burnolPhiCorrectionIntegrand w k t j u) =
      2 * (-1 : ℂ) ^ k * k.factorial *
        burnolPhiSeriesCoreTerm w k t j := by
  rw [integral_burnolPhiCorrectionIntegrand w t j hw0 hk]
  rw [burnolPhiSeriesCoreTerm]
  rw [pow_succ]
  field_simp [Real.pi_ne_zero, ht]
  push_cast
  ring_nf

theorem burnolPhiZeroCorrection_series_term
    (w : ℂ) {t : ℝ} (j : ℕ) (hw0 : 0 < w.re) (ht : t ≠ 0) :
    ((Real.pi * t : ℝ) : ℂ)⁻¹ * burnolSineSeriesTerm t j 1 -
        ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          (∫ u : ℝ in Ioc 0 1,
            burnolPhiZeroCorrectionIntegrand w t j u) =
      2 * burnolPhiSeriesCoreTerm w 0 t j := by
  have hden : w + (2 * j : ℕ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    rw [Complex.add_re, Complex.zero_re] at hre
    norm_num at hre
    have hj : (0 : ℝ) ≤ (2 * j : ℕ) := Nat.cast_nonneg _
    linarith
  have hfact : (((2 * j + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * j + 1)
  have hdenFact :
      w * ((2 * j + 1).factorial : ℂ) +
          ((2 * j : ℕ) : ℂ) * ((2 * j + 1).factorial : ℂ) ≠ 0 := by
    rw [← add_mul]
    exact mul_ne_zero hden hfact
  rw [integral_burnolPhiZeroCorrectionIntegrand w t j hw0]
  simp only [burnolSineSeriesTerm, burnolPhiSeriesCoreTerm]
  rw [pow_succ]
  rw [inv_eq_one_div]
  field_simp [Real.pi_ne_zero, ht, hden, hfact, hdenFact]
  simp only [zero_add, pow_one]
  field_simp [hden, hfact, hdenFact]
  norm_num
  ring

/-- The complete `k=0` low-end correction is exactly Burnol's convergent correction series. -/
theorem burnolPhiSmallCorrection_zero_eq_seriesRemainder
    (w : ℂ) {t : ℝ} (hw0 : 0 < w.re) (ht : t ≠ 0) :
    burnolPhiSmallCorrection w 0 t = burnolPhiSeriesRemainder w 0 t := by
  let c : ℂ := ((Real.pi * t : ℝ) : ℂ)⁻¹
  have hsine : HasSum
      (fun j : ℕ => c * burnolSineSeriesTerm t j 1)
      (c * (Real.sin (2 * Real.pi * t) : ℂ)) := by
    simpa only [mul_one] using
      (hasSum_burnolSineSeriesTerm t 1).mul_left c
  have hintegral : HasSum
      (fun j : ℕ => c *
        (∫ u : ℝ in Ioc 0 1,
          burnolPhiZeroCorrectionIntegrand w t j u))
      (c * ∫ u : ℝ in Ioc 0 1,
        w * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (2 * Real.pi * t * u) : ℂ)) :=
    (hasSum_integral_burnolPhiZeroCorrectionIntegrand w t hw0).mul_left c
  have hcorrection := hsine.sub hintegral
  have hseries : HasSum
      (fun j : ℕ => 2 * burnolPhiSeriesCoreTerm w 0 t j)
      (burnolPhiSmallCorrection w 0 t) := by
    have hvalue :
        c * (Real.sin (2 * Real.pi * t) : ℂ) -
            c * ∫ u : ℝ in Ioc 0 1,
              w * ((u : ℂ) ^ (w - 2)) *
                (Real.sin (2 * Real.pi * t * u) : ℂ) =
          burnolPhiSmallCorrection w 0 t := by
      simp [burnolPhiSmallCorrection, burnolPhiBoundaryTerm,
        burnolPhiLogFactor_zero, c]
      ring
    rw [hvalue] at hcorrection
    exact hcorrection.congr_fun fun j =>
      (burnolPhiZeroCorrection_series_term w j hw0 ht).symm
  rw [← hseries.tsum_eq]
  simp only [burnolPhiSeriesRemainder, pow_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one]
  exact tsum_mul_left

/-- For every derivative order, the low-end correction is Burnol's explicit convergent series. -/
theorem burnolPhiSmallCorrection_eq_seriesRemainder
    (w : ℂ) (k : ℕ) {t : ℝ} (hw0 : 0 < w.re) (ht : t ≠ 0) :
    burnolPhiSmallCorrection w k t = burnolPhiSeriesRemainder w k t := by
  by_cases hk0 : k = 0
  · subst k
    exact burnolPhiSmallCorrection_zero_eq_seriesRemainder w hw0 ht
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  let c : ℂ := -((Real.pi * t : ℝ) : ℂ)⁻¹
  have hintegral : HasSum
      (fun j : ℕ => c *
        (∫ u : ℝ in Ioc 0 1,
          burnolPhiCorrectionIntegrand w k t j u))
      (c * ∫ u : ℝ in Ioc 0 1,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (2 * Real.pi * t * u) : ℂ)) :=
    (hasSum_integral_burnolPhiCorrectionIntegrand w k t hw0).mul_left c
  have hvalue :
      c * ∫ u : ℝ in Ioc 0 1,
          burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
            (Real.sin (2 * Real.pi * t * u) : ℂ) =
        burnolPhiSmallCorrection w k t := by
    simp [burnolPhiSmallCorrection, burnolPhiBoundaryTerm, hk0, c]
  rw [hvalue] at hintegral
  have hseries : HasSum
      (fun j : ℕ =>
        2 * (-1 : ℂ) ^ k * k.factorial *
          burnolPhiSeriesCoreTerm w k t j)
      (burnolPhiSmallCorrection w k t) := by
    exact hintegral.congr_fun fun j =>
      (burnolPhiCorrection_series_term w j hw0 hk ht).symm
  rw [← hseries.tsum_eq]
  rw [burnolPhiSeriesRemainder]
  exact tsum_mul_left

theorem two_mul_nat_le_norm_add_of_re_nonneg
    (w : ℂ) {j : ℕ} (hw0 : 0 ≤ w.re) :
    (2 * j : ℝ) ≤ ‖w + (2 * j : ℕ)‖ := by
  calc
    (2 * j : ℝ) ≤ (w + (2 * j : ℕ)).re := by
      have hcast : (((2 * j : ℕ) : ℂ)).re = (2 * j : ℝ) := by norm_num
      rw [Complex.add_re, hcast]
      linarith
    _ ≤ ‖w + (2 * j : ℕ)‖ := Complex.re_le_norm _

theorem norm_burnolPhiSeriesRationalFactor_le_one
    (w : ℂ) {k j : ℕ} (hw0 : 0 ≤ w.re) (hj : 1 ≤ j) :
    ‖((2 * j : ℕ) : ℂ) / (w + (2 * j : ℕ)) ^ (k + 1)‖ ≤ 1 := by
  have hjReal : (1 : ℝ) ≤ 2 * j := by
    exact_mod_cast (show 1 ≤ 2 * j by omega)
  have hnumDen : (2 * j : ℝ) ≤ ‖w + (2 * j : ℕ)‖ :=
    two_mul_nat_le_norm_add_of_re_nonneg w hw0
  have hdenOne : (1 : ℝ) ≤ ‖w + (2 * j : ℕ)‖ := hjReal.trans hnumDen
  have hdenPow : ‖w + (2 * j : ℕ)‖ ≤ ‖w + (2 * j : ℕ)‖ ^ (k + 1) :=
    le_self_pow₀ hdenOne (by omega)
  have hdenPos : 0 < ‖w + (2 * j : ℕ)‖ ^ (k + 1) := by positivity
  rw [norm_div, norm_pow, norm_natCast]
  exact (div_le_one hdenPos).2 <| by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnumDen.trans hdenPow

/-- A `w`-independent majorant for Burnol's correction-series core. -/
def burnolPhiSeriesMajor (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ (2 * j) / (2 * j + 1).factorial

theorem burnolPhiSeriesMajor_nonneg (j : ℕ) :
    0 ≤ burnolPhiSeriesMajor j := by
  exact div_nonneg (pow_nonneg (by positivity) _) (Nat.cast_nonneg _)

theorem norm_burnolPhiSeriesCoreTerm_le_major
    (w : ℂ) {k : ℕ} {t : ℝ} (hw0 : 0 ≤ w.re)
    (ht : |t| ≤ 1) (j : ℕ) :
    ‖burnolPhiSeriesCoreTerm w k t j‖ ≤ burnolPhiSeriesMajor j := by
  by_cases hj : j = 0
  · subst j
    simp [burnolPhiSeriesCoreTerm, burnolPhiSeriesMajor]
  have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
  have hbase : |2 * Real.pi * t| ≤ 2 * Real.pi := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hpow : |2 * Real.pi * t| ^ (2 * j) ≤ (2 * Real.pi) ^ (2 * j) :=
    pow_le_pow_left₀ (abs_nonneg _) hbase (2 * j)
  have hfactorial : (0 : ℝ) < (2 * j + 1).factorial := by positivity
  have hosc :
      ‖(((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j) /
        ((2 * j + 1).factorial : ℂ))‖ ≤ burnolPhiSeriesMajor j := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_natCast,
      burnolPhiSeriesMajor]
    exact (div_le_div_iff_of_pos_right hfactorial).2 hpow
  have hrat := norm_burnolPhiSeriesRationalFactor_le_one w (k := k) hw0 hj1
  rw [burnolPhiSeriesCoreTerm, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul]
  calc
    ‖(((2 * Real.pi * t : ℝ) : ℂ) ^ (2 * j) /
        ((2 * j + 1).factorial : ℂ))‖ *
        ‖((2 * j : ℕ) : ℂ) / (w + (2 * j : ℕ)) ^ (k + 1)‖ ≤
      burnolPhiSeriesMajor j * 1 :=
        mul_le_mul hosc hrat (norm_nonneg _) (burnolPhiSeriesMajor_nonneg j)
    _ = burnolPhiSeriesMajor j := mul_one _

theorem burnolPhiSeriesMajor_le_expMajor (j : ℕ) :
    burnolPhiSeriesMajor j ≤
      ((2 * Real.pi) ^ 2) ^ j / j.factorial := by
  have hnum : 0 ≤ (2 * Real.pi) ^ (2 * j) := pow_nonneg (by positivity) _
  have hfactPos : (0 : ℝ) < j.factorial := by positivity
  have hfact : (j.factorial : ℝ) ≤ (2 * j + 1).factorial := by
    exact_mod_cast Nat.factorial_le (by omega : j ≤ 2 * j + 1)
  rw [burnolPhiSeriesMajor]
  calc
    (2 * Real.pi) ^ (2 * j) / (2 * j + 1).factorial ≤
        (2 * Real.pi) ^ (2 * j) / j.factorial :=
      div_le_div_of_nonneg_left hnum hfactPos hfact
    _ = ((2 * Real.pi) ^ 2) ^ j / j.factorial := by
      rw [pow_mul]

theorem summable_burnolPhiSeriesMajor :
    Summable burnolPhiSeriesMajor := by
  have hexp := Real.summable_pow_div_factorial ((2 * Real.pi) ^ 2)
  exact hexp.of_nonneg_of_le burnolPhiSeriesMajor_nonneg
    burnolPhiSeriesMajor_le_expMajor

theorem summable_burnolPhiSeriesCoreTerm
    (w : ℂ) {k : ℕ} {t : ℝ} (hw0 : 0 ≤ w.re)
    (ht : |t| ≤ 1) :
    Summable (burnolPhiSeriesCoreTerm w k t) := by
  apply Summable.of_norm
  exact summable_burnolPhiSeriesMajor.of_nonneg_of_le
    (fun j => norm_nonneg _) (norm_burnolPhiSeriesCoreTerm_le_major w hw0 ht)

/-- A uniform small-`t` bound for Burnol's correction series. -/
def burnolPhiSeriesBound (k : ℕ) : ℝ :=
  2 * k.factorial * ∑' j : ℕ, burnolPhiSeriesMajor j

theorem burnolPhiSeriesBound_nonneg (k : ℕ) :
    0 ≤ burnolPhiSeriesBound k := by
  unfold burnolPhiSeriesBound
  exact mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _))
    (tsum_nonneg burnolPhiSeriesMajor_nonneg)

theorem norm_tsum_burnolPhiSeriesCoreTerm_le_major
    (w : ℂ) {k : ℕ} {t : ℝ} (hw0 : 0 ≤ w.re)
    (ht : |t| ≤ 1) :
    ‖∑' j : ℕ, burnolPhiSeriesCoreTerm w k t j‖ ≤
      ∑' j : ℕ, burnolPhiSeriesMajor j := by
  have hnorm : Summable (fun j : ℕ => ‖burnolPhiSeriesCoreTerm w k t j‖) :=
    (summable_burnolPhiSeriesCoreTerm w hw0 ht).norm
  calc
    ‖∑' j : ℕ, burnolPhiSeriesCoreTerm w k t j‖ ≤
        ∑' j : ℕ, ‖burnolPhiSeriesCoreTerm w k t j‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' j : ℕ, burnolPhiSeriesMajor j :=
      hnorm.tsum_le_tsum
        (norm_burnolPhiSeriesCoreTerm_le_major w hw0 ht)
        summable_burnolPhiSeriesMajor

theorem norm_burnolPhiSeriesRemainder_le
    (w : ℂ) {k : ℕ} {t : ℝ} (hw0 : 0 ≤ w.re)
    (ht : |t| ≤ 1) :
    ‖burnolPhiSeriesRemainder w k t‖ ≤ burnolPhiSeriesBound k := by
  have hcore := norm_tsum_burnolPhiSeriesCoreTerm_le_major w (k := k) hw0 ht
  rw [burnolPhiSeriesRemainder, burnolPhiSeriesBound]
  change ‖(2 : ℂ) * (-1 : ℂ) ^ k * (k.factorial : ℂ) *
      (∑' j : ℕ, burnolPhiSeriesCoreTerm w k t j)‖ ≤
    2 * (k.factorial : ℝ) * ∑' j : ℕ, burnolPhiSeriesMajor j
  rw [norm_mul]
  have hscalar :
      ‖(2 : ℂ) * (-1 : ℂ) ^ k * (k.factorial : ℂ)‖ =
        2 * (k.factorial : ℝ) := by
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow,
      norm_natCast, mul_one]
    norm_num
  rw [hscalar]
  exact mul_le_mul_of_nonneg_left hcore (by positivity)

theorem tendsto_burnolPhiTruncated_nhdsGT_zero
    (w : ℂ) (k : ℕ) {t : ℝ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) (ht : t ≠ 0) :
    Tendsto (fun delta : ℝ => burnolPhiTruncated delta w k t)
      (𝓝[>] 0) (𝓝 (burnolPhi w k t)) := by
  have hlower := tendsto_burnolPhiLowerBoundary_nhdsGT_zero w k ht hw1
  have htail := tendsto_intervalIntegral_burnolPhiTail_nhdsGT_zero w k t hw1
  have hconst : Tendsto (fun _ : ℝ => burnolPhiBoundaryTerm k t)
      (𝓝[>] 0) (𝓝 (burnolPhiBoundaryTerm k t)) := tendsto_const_nhds
  have hscaled := htail.const_mul (((Real.pi * t : ℝ) : ℂ)⁻¹)
  have hsum := (hconst.sub hlower).add hscaled
  have hsum' : Tendsto (fun delta : ℝ =>
      burnolPhiBoundaryTerm k t -
        burnolPhiSourceWeight w k delta * burnolPhiSourceSinc t delta +
          (((Real.pi * t : ℝ) : ℂ)⁻¹) *
            ∫ u in 1..delta⁻¹, burnolPhiTailIntegrand w k t u)
      (𝓝[>] 0) (𝓝 (burnolPhi w k t)) := by
    simpa [burnolPhi] using hsum
  apply hsum'.congr'
  filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with delta hdelta
  exact (burnolPhiTruncated_eq_finiteTail w k hdelta.1 hdelta.2 hw0 ht).symm

theorem burnolPhiBoundaryTerm_zero (t : ℝ) :
    burnolPhiBoundaryTerm 0 t =
      (Real.sin (2 * Real.pi * t) : ℂ) / (Real.pi * t : ℝ) := by
  simp [burnolPhiBoundaryTerm]

theorem burnolPhiBoundaryTerm_eq_zero_of_pos
    {k : ℕ} (hk : 0 < k) (t : ℝ) :
    burnolPhiBoundaryTerm k t = 0 := by
  rw [burnolPhiBoundaryTerm, if_neg hk.ne']

theorem burnolPhi_zero (w : ℂ) (t : ℝ) :
    burnolPhi w 0 t =
      (Real.sin (2 * Real.pi * t) : ℂ) / (Real.pi * t : ℝ) +
        ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ∫ u : ℝ in Ioi 1,
            w * ((u : ℂ) ^ (w - 2)) *
              (Real.sin (2 * Real.pi * t * u) : ℂ) := by
  rw [burnolPhi, burnolPhiBoundaryTerm_zero]
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ fun u => by
    rw [burnolPhiTailIntegrand, burnolPhiLogFactor_zero]

theorem integral_burnolPhiTailMajor_nonneg
    (w : ℂ) (k : ℕ) :
    0 ≤ ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (one_pos.trans hu).le _)

theorem norm_burnolPhiBoundaryTerm_le
    (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖burnolPhiBoundaryTerm k t‖ ≤ (Real.pi * t)⁻¹ := by
  have hden : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  by_cases hk : k = 0
  · subst k
    rw [burnolPhiBoundaryTerm_zero, norm_div, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hden, inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hden).2 (Real.abs_sin_le_one _)
  · rw [burnolPhiBoundaryTerm, if_neg hk, norm_zero]
    exact inv_nonneg.mpr hden.le

theorem norm_burnolPhiTailTerm_le
    (w : ℂ) (k : ℕ) {t : ℝ} (hw : w.re < 1) (ht : 0 < t) :
    ‖((Real.pi * t : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u‖ ≤
      (Real.pi * t)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u := by
  have hden : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_burnolPhiTailIntegrand_le_major w k t hw)
    (inv_nonneg.mpr hden.le)

theorem norm_burnolPhi_le
    (w : ℂ) (k : ℕ) {t : ℝ} (hw : w.re < 1) (ht : 0 < t) :
    ‖burnolPhi w k t‖ ≤
      (1 + ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u) /
        (Real.pi * t) := by
  rw [burnolPhi]
  calc
    ‖burnolPhiBoundaryTerm k t +
        ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u‖ ≤
      ‖burnolPhiBoundaryTerm k t‖ +
        ‖((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u‖ :=
      norm_add_le _ _
    _ ≤ (Real.pi * t)⁻¹ + (Real.pi * t)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u :=
      add_le_add (norm_burnolPhiBoundaryTerm_le k ht)
        (norm_burnolPhiTailTerm_le w k hw ht)
    _ = (1 + ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u) /
        (Real.pi * t) := by
      rw [div_eq_mul_inv]
      ring

/-! ### The absolutely convergent sine--Mellin main term -/

theorem integral_Ioi_exp_neg_mul_cos
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (∫ u : ℝ in Ioi 0, Real.exp (-x * u) * Real.cos (y * u)) =
      x / (x ^ 2 + y ^ 2) := by
  let a : ℂ := (-x : ℂ) + Complex.I * y
  have ha : a.re < 0 := by
    simp [a, hx]
  have ha0 : a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [a] at hre
    linarith
  have hpoint : ∀ u : ℝ,
      (Complex.exp (a * u)).re =
        Real.exp (-x * u) * Real.cos (y * u) := by
    intro u
    rw [Complex.exp_re]
    simp [a]
  have hint := integral_exp_mul_complex_Ioi ha 0
  have hintable := integrableOn_exp_mul_complex_Ioi ha 0
  calc
    (∫ u : ℝ in Ioi 0, Real.exp (-x * u) * Real.cos (y * u)) =
        ∫ u : ℝ in Ioi 0, (Complex.exp (a * u)).re := by
          apply integral_congr_ae
          exact ae_of_all _ fun u => (hpoint u).symm
    _ = (∫ u : ℝ in Ioi 0, Complex.exp (a * u)).re := integral_re hintable
    _ = (-Complex.exp (a * (0 : ℝ)) / a).re := by rw [hint]
    _ = x / (x ^ 2 + y ^ 2) := by
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div]
      simp [a, Complex.normSq_apply]
      field_simp

theorem integrable_expNegCos_prod
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Integrable
      (fun z : ℝ × ℝ => Real.exp (-x * z.2) * Real.cos (z.1 * z.2))
      ((volume.restrict (uIoc 0 y)).prod (volume.restrict (Ioi 0))) := by
  have hv : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (uIoc 0 y)) := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc 0 y)
    exact (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 y).def'
  have hu : Integrable (fun u : ℝ => Real.exp (-x * u))
      (volume.restrict (Ioi 0)) := by
    change IntegrableOn (fun u : ℝ => Real.exp (-x * u)) (Ioi 0)
    exact integrableOn_exp_mul_Ioi (a := -x) (by linarith) 0
  have hmajor := hv.mul_prod hu
  refine hmajor.mono (by fun_prop) ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (z.1 * z.2))
    (Real.exp_pos _).le

theorem intervalIntegral_cos_mul_eq_sin_div
    {u : ℝ} (hu : u ≠ 0) (y : ℝ) :
    (∫ v : ℝ in 0..y, Real.cos (v * u)) = Real.sin (y * u) / u := by
  apply (eq_div_iff hu).2
  rw [mul_comm]
  rw [intervalIntegral.mul_integral_comp_mul_right]
  simp

theorem integral_Ioi_exp_neg_mul_sin_div
    {x : ℝ} (hx : 0 < x) (y : ℝ) :
    (∫ u : ℝ in Ioi 0,
        Real.exp (-x * u) * (Real.sin (y * u) / u)) =
      Real.arctan (y / x) := by
  have hprod := integrable_expNegCos_prod hx y
  calc
    (∫ u : ℝ in Ioi 0,
        Real.exp (-x * u) * (Real.sin (y * u) / u)) =
        ∫ u : ℝ in Ioi 0,
          (∫ v : ℝ in 0..y,
            Real.exp (-x * u) * Real.cos (v * u)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu0
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_cos_mul_eq_sin_div hu0.ne' y]
    _ = ∫ v : ℝ in 0..y,
        (∫ u : ℝ in Ioi 0,
          Real.exp (-x * u) * Real.cos (v * u)) := by
      exact (intervalIntegral_integral_swap hprod).symm
    _ = ∫ v : ℝ in 0..y, x / (x ^ 2 + v ^ 2) := by
      apply intervalIntegral.integral_congr
      intro v _
      exact integral_Ioi_exp_neg_mul_cos hx v
    _ = Real.arctan (y / x) := by
      rw [integral_div_sq_add_sq]
      simp

theorem integrableOn_rpow_mul_abs_sin_Ioi
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (b : ℝ) :
    IntegrableOn
      (fun u : ℝ => u ^ (sigma - 2) * |Real.sin (b * u)|)
      (Ioi 0) := by
  have hnearMajor : IntegrableOn
      (fun u : ℝ => |b| * u ^ (sigma - 1)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)).const_mul _
  have hnear : IntegrableOn
      (fun u : ℝ => u ^ (sigma - 2) * |Real.sin (b * u)|)
      (Ioo 0 1) := by
    refine hnearMajor.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      exact (continuousOn_id.rpow_const fun u hu => Or.inl hu.1.ne').mul
        (show Continuous (fun u : ℝ => |Real.sin (b * u)|) by fun_prop).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg hu.1.le _) (abs_nonneg _))]
      calc
        u ^ (sigma - 2) * |Real.sin (b * u)| ≤
            u ^ (sigma - 2) * |b * u| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs
            (Real.rpow_nonneg hu.1.le _)
        _ = |b| * u ^ (sigma - 1) := by
          rw [abs_mul, abs_of_pos hu.1]
          rw [show sigma - 1 = (sigma - 2) + 1 by ring,
            Real.rpow_add_one hu.1.ne']
          ring
  have htailMajor : IntegrableOn
      (fun u : ℝ => u ^ (sigma - 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have htailIoi : IntegrableOn
      (fun u : ℝ => u ^ (sigma - 2) * |Real.sin (b * u)|)
      (Ioi 1) := by
    refine htailMajor.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact (continuousOn_id.rpow_const fun u hu =>
        Or.inl (zero_lt_one.trans hu).ne').mul
          (show Continuous (fun u : ℝ => |Real.sin (b * u)|) by fun_prop).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Real.rpow_nonneg (zero_le_one.trans hu.le) _) (abs_nonneg _))]
      simpa using mul_le_of_le_one_right
        (Real.rpow_nonneg (zero_le_one.trans hu.le) _)
        (Real.abs_sin_le_one (b * u))
  have htail : IntegrableOn
      (fun u : ℝ => u ^ (sigma - 2) * |Real.sin (b * u)|)
      (Ici 1) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi htailIoi
  rw [show Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 by ext u; simp]
  exact hnear.union htail

theorem integral_Ioi_cpow_neg_mul_exp_neg_mul
    {w : ℂ} (hw1 : w.re < 1) {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Complex.exp (-((u : ℂ) * x))) =
      Complex.Gamma (1 - w) * (u : ℂ) ^ (w - 1) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi
    (a := 1 - w) (r := u) (by simp; linarith) hu
  rw [show -w = (1 - w) - 1 by ring, h, one_div,
    Complex.inv_cpow _ _
      (Complex.arg_ofReal_of_nonneg hu.le ▸ Real.pi_pos.ne),
    ← Complex.cpow_neg]
  rw [show -(1 - w) = w - 1 by ring]
  ring

/-- The positive-real Laplace kernel used to evaluate the sine--Mellin integral. -/
def sineMellinLaplaceKernel (w : ℂ) (b : ℝ) (z : ℝ × ℝ) : ℂ :=
  (z.1 : ℂ) ^ (-w) * Complex.exp (-((z.2 : ℂ) * z.1)) *
    (Real.sin (b * z.2) / z.2 : ℝ)

theorem norm_sineMellinLaplaceKernel
    (w : ℂ) (b : ℝ) {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    ‖sineMellinLaplaceKernel w b (x, u)‖ =
      x ^ (-w.re) * Real.exp (-u * x) * (|Real.sin (b * u)| / u) := by
  rw [sineMellinLaplaceKernel, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos hu]
  simp

theorem integrableOn_rpow_mul_exp_neg_mul_Ioi
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn
      (fun x : ℝ => x ^ (a - 1) * Real.exp (-(r * x)))
      (Ioi 0) := by
  simpa [Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := a - 1) (b := r) (by linarith) le_rfl hr)

theorem integral_Ioi_norm_sineMellinLaplaceKernel
    {w : ℂ} (hw1 : w.re < 1) (b : ℝ) {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ in Ioi 0, ‖sineMellinLaplaceKernel w b (x, u)‖) =
      Real.Gamma (1 - w.re) *
        (u ^ (w.re - 2) * |Real.sin (b * u)|) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx =>
    norm_sineMellinLaplaceKernel w b hx hu)]
  rw [integral_mul_const]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1 - w.re) (r := u) (by linarith) hu
  have h' :
      (∫ x : ℝ in Ioi 0,
        x ^ ((1 - w.re) - 1) * Real.exp (-u * x)) =
        (1 / u) ^ (1 - w.re) * Real.Gamma (1 - w.re) := by
    simpa only [neg_mul] using h
  rw [show -w.re = (1 - w.re) - 1 by ring, h', one_div,
    Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
  rw [show -(1 - w.re) = w.re - 1 by ring]
  have hrpow : u ^ (w.re - 2) = u ^ (w.re - 1) / u := by
    convert Real.rpow_sub_one hu.ne' (w.re - 1) using 1
    ring
  rw [hrpow]
  ring

theorem integrableOn_cpow_neg_mul_exp_neg_mul_Ioi
    {w : ℂ} (hw1 : w.re < 1) {u : ℝ} (hu : 0 < u) :
    IntegrableOn
      (fun x : ℝ =>
        (x : ℂ) ^ (-w) * Complex.exp (-((u : ℂ) * x)))
      (Ioi 0) := by
  have hmajor : IntegrableOn
      (fun x : ℝ => x ^ (-w.re) * Real.exp (-(u * x)))
      (Ioi 0) := by
    convert integrableOn_rpow_mul_exp_neg_mul_Ioi
      (a := 1 - w.re) (r := u) (by linarith) hu using 1
    ext x
    congr 2
    ring
  refine hmajor.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const x (-w)
      (Or.inr hx.ne')).mul
        (show ContinuousAt
          (fun x : ℝ => Complex.exp (-((u : ℂ) * x))) x by fun_prop) |>.continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_exp]
    simp

theorem integrable_sineMellinLaplaceKernel_prod
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) (b : ℝ) :
    Integrable (sineMellinLaplaceKernel w b)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hcont : ContinuousOn (sineMellinLaplaceKernel w b)
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    intro z hz
    have hpow : ContinuousAt
        (fun z : ℝ × ℝ => (z.1 : ℂ) ^ (-w)) z :=
      (Complex.continuousAt_ofReal_cpow_const z.1 (-w)
        (Or.inr hz.1.ne')).fst''
    have hexp : ContinuousAt
        (fun z : ℝ × ℝ => Complex.exp (-((z.2 : ℂ) * z.1))) z := by
      fun_prop
    have hsinReal : ContinuousAt
        (fun z : ℝ × ℝ => Real.sin (b * z.2) / z.2) z := by
      exact (Real.continuous_sin.continuousAt.comp
        (continuousAt_const.mul continuousAt_snd)).div
          continuousAt_snd hz.2.ne'
    have hsin : ContinuousAt
        (fun z : ℝ × ℝ => ((Real.sin (b * z.2) / z.2 : ℝ) : ℂ)) z :=
      Complex.ofRealCLM.continuous.continuousAt.comp hsinReal
    exact (hpow.mul hexp).mul hsin |>.continuousWithinAt
  have hmeas : AEStronglyMeasurable (sineMellinLaplaceKernel w b)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    rw [Measure.prod_restrict]
    exact hcont.aestronglyMeasurable
      (measurableSet_Ioi.prod measurableSet_Ioi)
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hbase := integrableOn_cpow_neg_mul_exp_neg_mul_Ioi hw1 hu
    have hscaled := hbase.mul_const
      (Real.sin (b * u) / u : ℝ)
    simpa [sineMellinLaplaceKernel, mul_assoc] using hscaled
  · have houter : IntegrableOn
        (fun u : ℝ => Real.Gamma (1 - w.re) *
          (u ^ (w.re - 2) * |Real.sin (b * u)|))
        (Ioi 0) :=
      (integrableOn_rpow_mul_abs_sin_Ioi hw0 hw1 b).const_mul _
    apply houter.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (integral_Ioi_norm_sineMellinLaplaceKernel hw1 b hu).symm

theorem integral_Ioi_sineMellinLaplaceKernel_right
    (w : ℂ) (b : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Ioi 0, sineMellinLaplaceKernel w b (x, u)) =
      (x : ℂ) ^ (-w) * Real.arctan (b / x) := by
  have hpoint : ∀ u : ℝ,
      sineMellinLaplaceKernel w b (x, u) =
        (x : ℂ) ^ (-w) *
          (Real.exp (-x * u) * (Real.sin (b * u) / u) : ℝ) := by
    intro u
    rw [sineMellinLaplaceKernel]
    have hexp : Complex.exp (-((u : ℂ) * x)) =
        (Real.exp (-x * u) : ℂ) := by
      rw [show -((u : ℂ) * x) = ((-x * u : ℝ) : ℂ) by
        push_cast
        ring]
      exact (Complex.ofReal_exp (-x * u)).symm
    rw [hexp]
    push_cast
    ring
  calc
    (∫ u : ℝ in Ioi 0, sineMellinLaplaceKernel w b (x, u)) =
        ∫ u : ℝ in Ioi 0,
          (x : ℂ) ^ (-w) *
            (Real.exp (-x * u) * (Real.sin (b * u) / u) : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      exact hpoint u
    _ = (x : ℂ) ^ (-w) *
        (∫ u : ℝ in Ioi 0,
          Real.exp (-x * u) * (Real.sin (b * u) / u) : ℝ) := by
      rw [integral_const_mul]
      congr 1
      exact integral_ofReal
    _ = (x : ℂ) ^ (-w) * Real.arctan (b / x) := by
      rw [integral_Ioi_exp_neg_mul_sin_div hx b]

theorem integral_Ioi_sineMellinLaplaceKernel_left
    {w : ℂ} (hw1 : w.re < 1) (b : ℝ) {u : ℝ} (hu : 0 < u) :
    (∫ x : ℝ in Ioi 0, sineMellinLaplaceKernel w b (x, u)) =
      Complex.Gamma (1 - w) * (u : ℂ) ^ (w - 1) *
        (Real.sin (b * u) / u : ℝ) := by
  rw [show (fun x : ℝ => sineMellinLaplaceKernel w b (x, u)) =
      fun x : ℝ =>
        ((x : ℂ) ^ (-w) * Complex.exp (-((u : ℂ) * x))) *
          (Real.sin (b * u) / u : ℝ) by
    funext x
    rfl]
  rw [integral_mul_const,
    integral_Ioi_cpow_neg_mul_exp_neg_mul hw1 hu]

theorem gamma_mul_sineMellinIntegral_eq_arctanIntegral
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) (b : ℝ) :
    Complex.Gamma (1 - w) *
        (∫ u : ℝ in Ioi 0,
          (u : ℂ) ^ (w - 2) * Real.sin (b * u)) =
      ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Real.arctan (b / x) := by
  have hprod := integrable_sineMellinLaplaceKernel_prod hw0 hw1 b
  have hprod' : Integrable
      (Function.uncurry fun x u : ℝ =>
        sineMellinLaplaceKernel w b (x, u))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    apply hprod.congr
    exact ae_of_all _ fun z => by
      rcases z with ⟨x, u⟩
      rfl
  have hswap :
      (∫ x : ℝ in Ioi 0,
        ∫ u : ℝ in Ioi 0, sineMellinLaplaceKernel w b (x, u)) =
      ∫ u : ℝ in Ioi 0,
        ∫ x : ℝ in Ioi 0, sineMellinLaplaceKernel w b (x, u) :=
    integral_integral_swap hprod'
  have hleft : ∀ u ∈ Ioi (0 : ℝ),
      Complex.Gamma (1 - w) * (u : ℂ) ^ (w - 1) *
          (Real.sin (b * u) / u : ℝ) =
        Complex.Gamma (1 - w) *
          ((u : ℂ) ^ (w - 2) * Real.sin (b * u)) := by
    intro u hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hpow : (u : ℂ) ^ (w - 1) * (u : ℂ)⁻¹ =
        (u : ℂ) ^ (w - 2) := by
      rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hu0]
      congr 1
      ring
    have hcast : ((Real.sin (b * u) / u : ℝ) : ℂ) =
        (Real.sin (b * u) : ℂ) * (u : ℂ)⁻¹ := by
      push_cast
      rfl
    rw [hcast]
    calc
      Complex.Gamma (1 - w) * (u : ℂ) ^ (w - 1) *
          ((Real.sin (b * u) : ℂ) * (u : ℂ)⁻¹) =
          Complex.Gamma (1 - w) *
            ((u : ℂ) ^ (w - 1) * (u : ℂ)⁻¹) *
              Real.sin (b * u) := by ring
      _ = Complex.Gamma (1 - w) *
          ((u : ℂ) ^ (w - 2) * Real.sin (b * u)) := by
        rw [hpow]
        ring
  calc
    Complex.Gamma (1 - w) *
        (∫ u : ℝ in Ioi 0,
          (u : ℂ) ^ (w - 2) * Real.sin (b * u)) =
        ∫ u : ℝ in Ioi 0,
          Complex.Gamma (1 - w) *
            ((u : ℂ) ^ (w - 2) * Real.sin (b * u)) := by
      rw [integral_const_mul]
    _ = ∫ u : ℝ in Ioi 0,
        (∫ x : ℝ in Ioi 0,
          sineMellinLaplaceKernel w b (x, u)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change Complex.Gamma (1 - w) *
          ((u : ℂ) ^ (w - 2) * Real.sin (b * u)) =
        ∫ x : ℝ in Ioi 0, sineMellinLaplaceKernel w b (x, u)
      rw [integral_Ioi_sineMellinLaplaceKernel_left hw1 b hu]
      exact (hleft u hu).symm
    _ = ∫ x : ℝ in Ioi 0,
        (∫ u : ℝ in Ioi 0,
          sineMellinLaplaceKernel w b (x, u)) := hswap.symm
    _ = ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Real.arctan (b / x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact integral_Ioi_sineMellinLaplaceKernel_right w b hx

/-- The standard Möbius map from the unit interval to the positive half-line. -/
def unitToIoi (t : ℝ) : ℝ :=
  t / (1 - t)

theorem hasDerivAt_unitToIoi {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt unitToIoi (1 / (1 - t) ^ 2) t := by
  have h := (hasDerivAt_id t).div
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
      (sub_ne_zero.mpr ht.symm)
  convert h using 1 <;> try rfl
  field_simp [sub_ne_zero.mpr ht.symm]
  simp only [Pi.sub_apply, id_eq]
  ring

theorem unitToIoi_injOn :
    Set.InjOn unitToIoi (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  simp only [unitToIoi] at hxy
  have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
  have hy1 : 1 - y ≠ 0 := by linarith [hy.2]
  field_simp [hx1, hy1] at hxy
  linarith

theorem unitToIoi_image :
    unitToIoi '' Ioo (0 : ℝ) 1 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [mem_Ioi, unitToIoi]
    exact div_pos ht.1 (sub_pos.mpr ht.2)
  · intro hy
    have hy0 : 0 < y := mem_Ioi.mp hy
    let t := y / (1 + y)
    have hden : 0 < 1 + y := by linarith
    have ht0 : 0 < t := div_pos hy0 hden
    have ht1 : t < 1 := (div_lt_one hden).2 (by linarith)
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    rw [unitToIoi]
    dsimp [t]
    field_simp
    ring

theorem ofReal_div_cpow
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (r : ℂ) :
    ((a / b : ℝ) : ℂ) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ (-r) := by
  rw [Complex.ofReal_div, div_eq_mul_inv, ← Complex.ofReal_inv,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hb.le),
    Complex.ofReal_inv,
    Complex.inv_cpow _ _
      (Complex.arg_ofReal_of_nonneg hb.le ▸ Real.pi_pos.ne),
    ← Complex.cpow_neg]

theorem unitToIoi_betaIntegrand
    (s : ℂ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |1 / (1 - t) ^ 2| •
        ((unitToIoi t : ℂ) ^ (s - 1) / (1 + unitToIoi t)) =
      (t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ ((1 - s) - 1) := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have ht1ne : (1 - (t : ℂ)) ≠ 0 := by
    norm_cast
    exact ht1.ne'
  have habs : |1 / (1 - t) ^ 2| = 1 / (1 - t) ^ 2 := by
    rw [abs_of_pos]
    positivity
  have hden : (1 + (unitToIoi t : ℂ)) =
      ((1 / (1 - t) : ℝ) : ℂ) := by
    rw [unitToIoi]
    push_cast
    field_simp
    ring
  have hratio :
      (1 / (1 - (t : ℂ)) ^ 2) / (1 / (1 - (t : ℂ))) =
        1 / (1 - (t : ℂ)) := by
    field_simp [ht1ne]
  have hinv : (1 / (1 - (t : ℂ))) =
      (1 - (t : ℂ)) ^ (-1 : ℂ) := by
    rw [Complex.cpow_neg_one]
    rw [one_div]
  rw [habs, hden, unitToIoi, ofReal_div_cpow ht0 ht1]
  rw [Complex.real_smul]
  push_cast
  change (1 / (1 - (t : ℂ)) ^ 2) *
      (((t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ (-(s - 1))) /
        (1 / (1 - (t : ℂ)))) = _
  calc
    (1 / (1 - (t : ℂ)) ^ 2) *
        (((t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ (-(s - 1))) /
          (1 / (1 - (t : ℂ)))) =
        (t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ (-(s - 1)) *
          ((1 / (1 - (t : ℂ)) ^ 2) /
            (1 / (1 - (t : ℂ)))) := by ring
    _ = (t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ (-(s - 1)) *
        (1 / (1 - (t : ℂ))) := by rw [hratio]
    _ = (t : ℂ) ^ (s - 1) *
        ((1 - (t : ℂ)) ^ (-(s - 1)) *
          (1 - (t : ℂ)) ^ (-1 : ℂ)) := by rw [hinv]; ring
    _ = (t : ℂ) ^ (s - 1) *
        (1 - (t : ℂ)) ^ (-(s - 1) + (-1 : ℂ)) := by
      rw [Complex.cpow_add _ _ ht1ne]
    _ = (t : ℂ) ^ (s - 1) *
        (1 - (t : ℂ)) ^ ((1 - s) - 1) := by
      congr 2
      ring

theorem integral_Ioi_cpow_div_one_add_eq_betaIntegral (s : ℂ) :
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (s - 1) / (1 + y)) =
      Complex.betaIntegral s (1 - s) := by
  let g : ℝ → ℂ := fun y => (y : ℂ) ^ (s - 1) / (1 + y)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo
    (fun t ht => (hasDerivAt_unitToIoi ht.2.ne).hasDerivWithinAt)
    unitToIoi_injOn g
  rw [unitToIoi_image] at hchange
  calc
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (s - 1) / (1 + y)) =
        ∫ t : ℝ in Ioo 0 1,
          |1 / (1 - t) ^ 2| •
            ((unitToIoi t : ℂ) ^ (s - 1) / (1 + unitToIoi t)) := hchange
    _ = ∫ t : ℝ in Ioo 0 1,
        (t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ ((1 - s) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact unitToIoi_betaIntegrand s ht
    _ = ∫ t : ℝ in 0..1,
        (t : ℂ) ^ (s - 1) * (1 - (t : ℂ)) ^ ((1 - s) - 1) := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo]
    _ = Complex.betaIntegral s (1 - s) := rfl

theorem ofReal_sq_cpow_neg_half
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    ((x ^ 2 : ℝ) : ℂ) ^ (-w / 2) = (x : ℂ) ^ (-w) := by
  have h := Complex.cpow_ofNat_mul' (x := (x : ℂ)) (n := 2)
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; simp [Real.pi_pos])
    (by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      simpa using Real.pi_pos.le)
    (-w / 2)
  rw [show (2 : ℂ) * (-w / 2) = -w by ring] at h
  rw [Complex.ofReal_pow]
  exact h.symm

theorem integral_Ioi_cpow_one_sub_div_one_add_sq_eq_betaIntegral
    (w : ℂ) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (1 - w) / (1 + x ^ 2)) =
      (1 / 2 : ℂ) * Complex.betaIntegral (1 - w / 2) (w / 2) := by
  let g : ℝ → ℂ := fun y =>
    (1 / 2 : ℂ) * ((y : ℂ) ^ (-w / 2) / (1 + y))
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := g) (p := (2 : ℝ)) (by norm_num)
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)) =
        (x : ℂ) ^ (1 - w) / (1 + x ^ 2) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hpow : (x : ℂ) * (x : ℂ) ^ (-w) =
        (x : ℂ) ^ (1 - w) := by
      calc
        (x : ℂ) * (x : ℂ) ^ (-w) =
            (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-w) := by
          rw [Complex.cpow_one]
        _ = (x : ℂ) ^ ((1 : ℂ) + (-w)) :=
          (Complex.cpow_add _ _ hx0).symm
        _ = (x : ℂ) ^ (1 - w) := by congr 1
    dsimp [g]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      show x ^ (2 : ℝ) = x ^ 2 by rw [Real.rpow_two],
      ofReal_sq_cpow_neg_half w hx]
    push_cast
    calc
      (2 : ℂ) * (x : ℂ) *
          ((1 / 2 : ℂ) *
            ((x : ℂ) ^ (-w) / (1 + (x : ℂ) ^ 2))) =
          ((x : ℂ) * (x : ℂ) ^ (-w)) /
            (1 + (x : ℂ) ^ 2) := by ring
      _ = (x : ℂ) ^ (1 - w) / (1 + (x : ℂ) ^ 2) := by rw [hpow]
  calc
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (1 - w) / (1 + x ^ 2)) =
        ∫ x : ℝ in Ioi 0,
          ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) • g (x ^ (2 : ℝ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (hpoint x hx).symm
    _ = ∫ y : ℝ in Ioi 0, g y := hsub
    _ = (1 / 2 : ℂ) *
        ∫ y : ℝ in Ioi 0,
          (y : ℂ) ^ (-w / 2) / (1 + y) := by
      rw [integral_const_mul]
    _ = (1 / 2 : ℂ) *
        Complex.betaIntegral (1 - w / 2) (w / 2) := by
      rw [show -w / 2 = (1 - w / 2) - 1 by ring,
        integral_Ioi_cpow_div_one_add_eq_betaIntegral]
      congr 2
      ring

theorem integral_Ioi_cpow_one_sub_div_one_add_sq
    {w : ℂ} (hw0 : 0 < w.re) (hw2 : w.re < 2) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (1 - w) / (1 + x ^ 2)) =
      (Real.pi : ℂ) / (2 * Complex.sin (Real.pi * w / 2)) := by
  rw [integral_Ioi_cpow_one_sub_div_one_add_sq_eq_betaIntegral]
  rw [Complex.betaIntegral_eq_Gamma_mul_div]
  · rw [show 1 - w / 2 + w / 2 = 1 by ring, Complex.Gamma_one, div_one]
    have href := Complex.Gamma_mul_Gamma_one_sub (w / 2)
    rw [show 1 - w / 2 = 1 - (w / 2) by ring]
    have harg : (Real.pi : ℂ) * (w / 2) = Real.pi * w / 2 := by ring
    rw [harg] at href
    have href' : Complex.Gamma (1 - w / 2) * Complex.Gamma (w / 2) =
        (Real.pi : ℂ) / Complex.sin (Real.pi * w / 2) := by
      calc
        Complex.Gamma (1 - w / 2) * Complex.Gamma (w / 2) =
            Complex.Gamma (w / 2) * Complex.Gamma (1 - w / 2) := mul_comm _ _
        _ = (Real.pi : ℂ) / Complex.sin (Real.pi * w / 2) := href
    rw [href']
    ring
  · simp
    linarith
  · simp
    linarith

theorem integrableOn_cpow_one_sub_div_one_add_sq
    {w : ℂ} (hw0 : 0 < w.re) (hw2 : w.re < 2) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (1 - w) / (1 + x ^ 2))
      (Ioi 0) := by
  have hnearMajor : IntegrableOn
      (fun x : ℝ => x ^ (1 - w.re)) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  have hnear : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (1 - w) / (1 + x ^ 2))
      (Ioo 0 1) := by
    refine hnearMajor.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      intro x hx
      have hden : (1 + (x : ℂ) ^ 2) ≠ 0 := by
        rw [show 1 + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) by norm_cast]
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      exact ((Complex.continuousAt_ofReal_cpow_const x (1 - w)
        (Or.inr hx.1.ne')).div
          (show ContinuousAt (fun x : ℝ => (1 + x ^ 2 : ℂ)) x by fun_prop)
          hden).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx.1,
        show 1 + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) by norm_cast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
      exact div_le_self (Real.rpow_nonneg hx.1.le _)
        (by nlinarith [sq_nonneg x])
  have htailMajor : IntegrableOn
      (fun x : ℝ => x ^ (-1 - w.re)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have htailIoi : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (1 - w) / (1 + x ^ 2))
      (Ioi 1) := by
    refine htailMajor.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro x hx
      have hden : (1 + (x : ℂ) ^ 2) ≠ 0 := by
        rw [show 1 + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) by norm_cast]
        exact Complex.ofReal_ne_zero.mpr (by positivity)
      exact ((Complex.continuousAt_ofReal_cpow_const x (1 - w)
        (Or.inr (zero_lt_one.trans hx).ne')).div
          (show ContinuousAt (fun x : ℝ => (1 + x ^ 2 : ℂ)) x by fun_prop)
          hden).continuousWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := zero_lt_one.trans hx
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        show 1 + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) by norm_cast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
      calc
        x ^ (1 - w.re) / (1 + x ^ 2) ≤ x ^ (1 - w.re) / x ^ 2 := by
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _)
            (sq_pos_of_pos hx0) (by linarith [sq_nonneg x])
        _ = x ^ (-1 - w.re) := by
          rw [← Real.rpow_sub_natCast hx0.ne' (1 - w.re) 2]
          congr 1
          ring
  have htail : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (1 - w) / (1 + x ^ 2))
      (Ici 1) := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi htailIoi
  rw [show Ioi (0 : ℝ) = Ioo 0 1 ∪ Ici 1 by ext x; simp]
  exact hnear.union htail

theorem integrableOn_cpow_neg_mul_arctan_div_Ioi
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) (b : ℝ) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-w) * Real.arctan (b / x))
      (Ioi 0) := by
  have hprod := integrable_sineMellinLaplaceKernel_prod hw0 hw1 b
  have hsections := hprod.integral_prod_left
  apply hsections.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact integral_Ioi_sineMellinLaplaceKernel_right w b hx

theorem hasDerivAt_arctan_one_div {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.arctan (1 / y))
      (-1 / (1 + x ^ 2)) x := by
  have hinv : HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have h := (Real.hasDerivAt_arctan (1 / x)).comp x hinv
  convert h using 1 <;> try rfl
  field_simp
  ring

theorem arctan_le_self_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    Real.arctan y ≤ y := by
  simpa using Real.le_tan (Real.arctan_nonneg.mpr hy)
    (Real.arctan_lt_pi_div_two y)

theorem tendsto_cpow_div_mul_arctan_one_div_nhdsGT_zero
    {w : ℂ} (hw1 : w.re < 1) :
    Tendsto
      (fun x : ℝ =>
        ((x : ℂ) ^ (1 - w) / (1 - w)) * Real.arctan (1 / x))
      (𝓝[>] 0) (𝓝 0) := by
  have hexp : (1 - w) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hpow : Tendsto (fun x : ℝ => (x : ℂ) ^ (1 - w))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont := Complex.continuousAt_ofReal_cpow_const 0 (1 - w)
      (Or.inl (by simp; linarith))
    have ht : Tendsto (fun x : ℝ => (x : ℂ) ^ (1 - w))
        (𝓝[>] 0) (𝓝 ((0 : ℂ) ^ (1 - w))) :=
      hcont.tendsto.mono_left inf_le_left
    simpa [Complex.zero_cpow hexp] using ht
  have hU : Tendsto (fun x : ℝ => (x : ℂ) ^ (1 - w) / (1 - w))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hpow.div_const (1 - w)
  have hVReal : Tendsto (fun x : ℝ => Real.arctan (1 / x))
      (𝓝[>] 0) (𝓝 (Real.pi / 2)) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        tendsto_inv_nhdsGT_zero
  have hV : Tendsto (fun x : ℝ => (Real.arctan (1 / x) : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.pi / 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hVReal
  simpa using hU.mul hV

theorem tendsto_cpow_div_mul_arctan_one_div_atTop
    {w : ℂ} (hw0 : 0 < w.re) :
    Tendsto
      (fun x : ℝ =>
        ((x : ℂ) ^ (1 - w) / (1 - w)) * Real.arctan (1 / x))
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun x : ℝ => ‖(1 - w)⁻¹‖ * x ^ (-w.re))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hw0).const_mul ‖(1 - w)⁻¹‖
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖((x : ℂ) ^ (1 - w) / (1 - w)) * Real.arctan (1 / x)‖ ≤
        ‖(1 - w)⁻¹‖ * x ^ (-w.re) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have harctan0 : 0 ≤ Real.arctan (1 / x) :=
      Real.arctan_nonneg.mpr (one_div_nonneg.mpr hx.le)
    have harctanLe : Real.arctan (1 / x) ≤ 1 / x :=
      arctan_le_self_of_nonneg (one_div_nonneg.mpr hx.le)
    have hrpow : x ^ (1 - w.re) / x = x ^ (-w.re) := by
      rw [← Real.rpow_sub_one hx.ne' (1 - w.re)]
      congr 1
      ring
    rw [norm_mul, norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg harctan0,
      norm_inv]
    calc
      x ^ (1 - w.re) / ‖1 - w‖ * Real.arctan (1 / x) ≤
          x ^ (1 - w.re) / ‖1 - w‖ * (1 / x) :=
        mul_le_mul_of_nonneg_left harctanLe
          (div_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _))
      _ = ‖1 - w‖⁻¹ * x ^ (-w.re) := by rw [← hrpow]; ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hbound hmajor

theorem integral_Ioi_cpow_neg_mul_arctan_one_div
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Real.arctan (1 / x)) =
      (1 - w)⁻¹ *
        ∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (1 - w) / (1 + x ^ 2) := by
  have hwne : (1 - w) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hU : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt
        (fun y : ℝ => (y : ℂ) ^ (1 - w) / (1 - w))
        ((x : ℂ) ^ (-w)) x := by
    intro x hx
    have h := hasDerivAt_ofReal_cpow_const'
      hx.ne' (r := -w) (by
        intro hr
        have hre := congrArg Complex.re hr
        simp at hre
        linarith)
    simpa [sub_eq_add_neg, div_eq_mul_inv, add_comm, mul_comm] using h
  have hV : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt
        (fun y : ℝ => (Real.arctan (1 / y) : ℂ))
        ((-1 / (1 + x ^ 2) : ℝ) : ℂ) x := by
    intro x hx
    exact (hasDerivAt_arctan_one_div hx.ne').ofReal_comp
  have hUV' : IntegrableOn
      (fun x : ℝ =>
        ((x : ℂ) ^ (1 - w) / (1 - w)) *
          ((-1 / (1 + x ^ 2) : ℝ) : ℂ))
      (Ioi 0) := by
    have hrat := integrableOn_cpow_one_sub_div_one_add_sq hw0 (by linarith)
    have hscaled : IntegrableOn
        (fun x : ℝ => -(1 - w)⁻¹ *
          ((x : ℂ) ^ (1 - w) / (1 + x ^ 2)))
        (Ioi 0) :=
      hrat.const_mul (-(1 - w)⁻¹)
    apply hscaled.congr_fun
    · intro x _
      push_cast
      ring
    · exact measurableSet_Ioi
  have hU'V := integrableOn_cpow_neg_mul_arctan_div_Ioi hw0 hw1 1
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (a' := (0 : ℂ)) (b' := (0 : ℂ))
    hU hV hUV' hU'V
    (tendsto_cpow_div_mul_arctan_one_div_nhdsGT_zero hw1)
    (tendsto_cpow_div_mul_arctan_one_div_atTop hw0)
  have hleft :
      (∫ x : ℝ in Ioi 0,
        ((x : ℂ) ^ (1 - w) / (1 - w)) *
          ((-1 / (1 + x ^ 2) : ℝ) : ℂ)) =
        -(1 - w)⁻¹ *
          ∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (1 - w) / (1 + x ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    push_cast
    ring
  rw [hleft] at hibp
  simp only [zero_sub] at hibp
  have hCA :
      (1 - w)⁻¹ *
          (∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (1 - w) / (1 + x ^ 2)) =
        ∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (-w) * Real.arctan (1 / x) := by
    apply neg_injective
    simpa only [neg_mul, neg_zero, zero_sub] using hibp
  exact hCA.symm

theorem integral_Ioi_cpow_neg_mul_arctan_one_div_eq
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Real.arctan (1 / x)) =
      (Real.pi : ℂ) /
        ((1 - w) * (2 * Complex.sin (Real.pi * w / 2))) := by
  rw [integral_Ioi_cpow_neg_mul_arctan_one_div hw0 hw1,
    integral_Ioi_cpow_one_sub_div_one_add_sq hw0 (by linarith)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem integral_Ioi_cpow_neg_mul_arctan_div_scale
    (w : ℂ) {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Real.arctan (b / x)) =
      (b : ℂ) ^ (1 - w) *
        ∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (-w) * Real.arctan (1 / x) := by
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (-w) * Real.arctan (b / x)
  have hsub := integral_comp_mul_left_Ioi g 0 hb
  simp only [mul_zero] at hsub
  have hcomp :
      (∫ x : ℝ in Ioi 0, g (b * x)) =
        (b : ℂ) ^ (-w) *
          ∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (-w) * Real.arctan (1 / x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hdiv : b / (b * x) = 1 / x := by
      field_simp [hb.ne', hxpos.ne']
    dsimp [g]
    rw [Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hb.le hx.le, hdiv]
    ring
  have hsub' :
      (b : ℂ) ^ (-w) *
          (∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (-w) * Real.arctan (1 / x)) =
        (b : ℂ)⁻¹ *
          ∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (-w) * Real.arctan (b / x) := by
    rw [← hcomp]
    simpa only [Complex.real_smul, Complex.ofReal_inv] using hsub
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hpow :
      (b : ℂ) ^ (1 - w) = (b : ℂ) * (b : ℂ) ^ (-w) := by
    calc
      (b : ℂ) ^ (1 - w) = (b : ℂ) ^ ((1 : ℂ) + (-w)) := by
        congr 1
      _ = (b : ℂ) ^ (1 : ℂ) * (b : ℂ) ^ (-w) :=
        Complex.cpow_add _ _ hbC
      _ = (b : ℂ) * (b : ℂ) ^ (-w) := by rw [Complex.cpow_one]
  calc
    (∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (-w) * Real.arctan (b / x)) =
        (b : ℂ) *
          ((b : ℂ)⁻¹ *
            ∫ x : ℝ in Ioi 0,
              (x : ℂ) ^ (-w) * Real.arctan (b / x)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hbC, one_mul]
    _ = (b : ℂ) *
        ((b : ℂ) ^ (-w) *
          ∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (-w) * Real.arctan (1 / x)) := by
      rw [← hsub']
    _ = (b : ℂ) ^ (1 - w) *
        ∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (-w) * Real.arctan (1 / x) := by
      rw [hpow, mul_assoc]

theorem integral_Ioi_cpow_mul_sin_eq_gamma
    {w : ℂ} {b : ℝ} (hb : 0 < b)
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ u : ℝ in Ioi 0,
        (u : ℂ) ^ (w - 2) * Real.sin (b * u)) =
      (1 - w)⁻¹ * (b : ℂ) ^ (1 - w) *
        Complex.cos (Real.pi * w / 2) * Complex.Gamma w := by
  have hGamma : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hw0
  have hGammaOne : Complex.Gamma (1 - w) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    linarith
  have href := Complex.Gamma_mul_Gamma_one_sub w
  have hsinFull : Complex.sin (Real.pi * w) ≠ 0 := by
    intro hsin
    have href0 := href
    rw [hsin, div_zero] at href0
    exact (mul_ne_zero hGamma hGammaOne) href0
  have hsinDouble :
      Complex.sin (Real.pi * w) =
        2 * Complex.sin (Real.pi * w / 2) *
          Complex.cos (Real.pi * w / 2) := by
    calc
      Complex.sin (Real.pi * w) =
          Complex.sin (2 * (Real.pi * w / 2)) := by
        congr 1
        ring
      _ = 2 * Complex.sin (Real.pi * w / 2) *
          Complex.cos (Real.pi * w / 2) :=
        Complex.sin_two_mul (Real.pi * w / 2)
  have hsinHalf : Complex.sin (Real.pi * w / 2) ≠ 0 := by
    intro hsin
    apply hsinFull
    rw [hsinDouble, hsin]
    ring
  have hrefMul :
      Complex.Gamma w * Complex.Gamma (1 - w) *
          Complex.sin (Real.pi * w) = Real.pi :=
    (eq_div_iff hsinFull).mp href
  have href' :
      Complex.Gamma w * Complex.Gamma (1 - w) *
          (2 * Complex.sin (Real.pi * w / 2) *
            Complex.cos (Real.pi * w / 2)) = Real.pi := by
    rw [← hsinDouble]
    exact hrefMul
  have hratio :
      (Real.pi : ℂ) / (2 * Complex.sin (Real.pi * w / 2)) =
        Complex.cos (Real.pi * w / 2) *
          Complex.Gamma w * Complex.Gamma (1 - w) := by
    apply (div_eq_iff (mul_ne_zero two_ne_zero hsinHalf)).2
    calc
      (Real.pi : ℂ) =
          Complex.Gamma w * Complex.Gamma (1 - w) *
            (2 * Complex.sin (Real.pi * w / 2) *
              Complex.cos (Real.pi * w / 2)) := href'.symm
      _ = (Complex.cos (Real.pi * w / 2) *
          Complex.Gamma w * Complex.Gamma (1 - w)) *
            (2 * Complex.sin (Real.pi * w / 2)) := by ring
  have hFubini :=
    gamma_mul_sineMellinIntegral_eq_arctanIntegral hw0 hw1 b
  rw [integral_Ioi_cpow_neg_mul_arctan_div_scale w hb,
    integral_Ioi_cpow_neg_mul_arctan_one_div_eq hw0 hw1] at hFubini
  have hfrac :
      (Real.pi : ℂ) /
          ((1 - w) * (2 * Complex.sin (Real.pi * w / 2))) =
        (1 - w)⁻¹ *
          ((Real.pi : ℂ) /
            (2 * Complex.sin (Real.pi * w / 2))) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  apply mul_left_cancel₀ hGammaOne
  rw [hFubini, hfrac, hratio]
  ring

/-! ### Parameter derivatives of the sine--Mellin main term -/

def burnolSineMellinBase (b u : ℝ) : ℂ :=
  (Real.sin (b * u) / u : ℝ)

def burnolSineMellinLogMoment (b : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  (Real.log u : ℂ) ^ n * burnolSineMellinBase b u

theorem locallyIntegrableOn_burnolSineMellinLogMoment
    (b : ℝ) (n : ℕ) :
    LocallyIntegrableOn (burnolSineMellinLogMoment b n) (Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  unfold burnolSineMellinLogMoment burnolSineMellinBase
  fun_prop (disch := aesop)

theorem isBigO_burnolSineMellinBase_rpow_top (b : ℝ) :
    burnolSineMellinBase b =O[atTop]
      (fun u : ℝ => u ^ (-1 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [burnolSineMellinBase, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos hu0, one_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _), Real.rpow_neg_one]
  simpa only [one_div] using
    (div_le_div_of_nonneg_right (Real.abs_sin_le_one (b * u)) hu0.le)

theorem isBigO_burnolSineMellinBase_rpow_zero
    {b : ℝ} (hb : 0 < b) :
    burnolSineMellinBase b =O[𝓝[>] 0]
      (fun u : ℝ => u ^ (-(0 : ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨b, ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with u hu
  have hu0 : 0 < u := hu.out
  rw [burnolSineMellinBase, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos hu0, neg_zero, Real.rpow_zero,
    norm_one, mul_one]
  calc
    |Real.sin (b * u)| / u ≤ |b * u| / u :=
      div_le_div_of_nonneg_right Real.abs_sin_le_abs hu0.le
    _ = b := by rw [abs_mul, abs_of_pos hb, abs_of_pos hu0]; field_simp

theorem isBigO_burnolSineMellinLogMoment_rpow_top
    (b : ℝ) (n : ℕ) {a : ℝ} (ha : a < 1) :
    burnolSineMellinLogMoment b n =O[atTop]
      (fun u : ℝ => u ^ (-a)) := by
  induction n generalizing a with
  | zero =>
      have hmono : (fun u : ℝ => u ^ (-1 : ℝ)) =O[atTop]
          (fun u : ℝ => u ^ (-a)) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨1, ?_⟩
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
        rw [one_mul,
          Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
          Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
        exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
      refine ((isBigO_burnolSineMellinBase_rpow_top b).trans hmono).congr'
        (Eventually.of_forall fun u => ?_) (Eventually.of_forall fun _ => rfl)
      simp [burnolSineMellinLogMoment]
  | succ n hn =>
      let c : ℝ := (a + 1) / 2
      have hac : a < c := by dsimp [c]; linarith
      have hc1 : c < 1 := by dsimp [c]; linarith
      have hprev := hn hc1
      have hlog := isBigO_rpow_top_log_smul hac hprev
      refine hlog.congr' (Eventually.of_forall fun u => ?_)
        (Eventually.of_forall fun _ => rfl)
      simp only [burnolSineMellinLogMoment, Complex.real_smul, pow_succ]
      ring

theorem isBigO_burnolSineMellinLogMoment_rpow_zero
    {b : ℝ} (hb : 0 < b) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    burnolSineMellinLogMoment b n =O[𝓝[>] 0]
      (fun u : ℝ => u ^ (-a)) := by
  induction n generalizing a with
  | zero =>
      have hbase := isBigO_burnolSineMellinBase_rpow_zero hb
      have hmono : (fun u : ℝ => u ^ (-(0 : ℝ))) =O[𝓝[>] 0]
          (fun u : ℝ => u ^ (-a)) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨1, ?_⟩
        filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with u hu
        rw [one_mul,
          Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _),
          Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _)]
        exact Real.rpow_le_rpow_of_exponent_ge hu.1 hu.2 (by linarith)
      refine (hbase.trans hmono).congr' (Eventually.of_forall fun u => ?_)
        (Eventually.of_forall fun _ => rfl)
      simp [burnolSineMellinLogMoment]
  | succ n hn =>
      let c : ℝ := a / 2
      have hc0 : 0 < c := by dsimp [c]; linarith
      have hca : c < a := by dsimp [c]; linarith
      have hprev := hn hc0
      have hlog := isBigO_rpow_zero_log_smul hca hprev
      refine hlog.congr' (Eventually.of_forall fun u => ?_)
        (Eventually.of_forall fun _ => rfl)
      simp only [burnolSineMellinLogMoment, Complex.real_smul, pow_succ]
      ring

theorem hasDerivAt_mellin_burnolSineMellinLogMoment
    {b : ℝ} (hb : 0 < b) (n : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    HasDerivAt (mellin (burnolSineMellinLogMoment b n))
      (mellin (burnolSineMellinLogMoment b (n + 1)) w) w := by
  let a : ℝ := (w.re + 1) / 2
  let c : ℝ := w.re / 2
  have hwa : w.re < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hcw : c < w.re := by dsimp [c]; linarith
  have hdiff := mellin_hasDerivAt_of_isBigO_rpow
    (locallyIntegrableOn_burnolSineMellinLogMoment b n)
    (isBigO_burnolSineMellinLogMoment_rpow_top b n ha1) hwa
    (isBigO_burnolSineMellinLogMoment_rpow_zero hb n hc0) hcw
  have hvalue :
      mellin (fun u : ℝ =>
          Real.log u • burnolSineMellinLogMoment b n u) w =
        mellin (burnolSineMellinLogMoment b (n + 1)) w := by
    congr 1
    funext u
    simp only [burnolSineMellinLogMoment, Complex.real_smul, pow_succ]
    ring
  rw [hvalue] at hdiff
  exact hdiff.2

theorem iteratedDeriv_mellin_burnolSineMellinBase_eq_logMoment
    {b : ℝ} (hb : 0 < b) (n : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    iteratedDeriv n (mellin (burnolSineMellinBase b)) w =
      mellin (burnolSineMellinLogMoment b n) w := by
  induction n generalizing w with
  | zero =>
      simp only [iteratedDeriv_zero]
      congr 1
      funext u
      simp [burnolSineMellinLogMoment]
  | succ n hn =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv n (mellin (burnolSineMellinBase b)) =ᶠ[𝓝 w]
          mellin (burnolSineMellinLogMoment b n) := by
        have hstrip : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re ∧ z.re < 1 :=
          (Complex.continuous_re.tendsto w).eventually
            (Ioo_mem_nhds hw0 hw1)
        filter_upwards [hstrip] with z hz
        exact hn hz.1 hz.2
      rw [hfun.deriv_eq]
      exact (hasDerivAt_mellin_burnolSineMellinLogMoment hb n hw0 hw1).deriv

theorem mellin_burnolSineMellinLogMoment_eq_integral
    (b : ℝ) (n : ℕ) (w : ℂ) :
    mellin (burnolSineMellinLogMoment b n) w =
      ∫ u : ℝ in Ioi 0,
        (Real.log u : ℂ) ^ n * ((u : ℂ) ^ (w - 2) * Real.sin (b * u)) := by
  rw [mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hpow : (u : ℂ) ^ (w - 1) * (u : ℂ)⁻¹ =
      (u : ℂ) ^ (w - 2) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hu0]
    congr 1
    ring
  simp only [burnolSineMellinLogMoment, burnolSineMellinBase,
    smul_eq_mul]
  push_cast
  rw [div_eq_mul_inv, ← hpow]
  ring

def burnolSineMellinWeighted (b : ℝ) (w : ℂ) : ℂ :=
  w * mellin (burnolSineMellinBase b) w

theorem iteratedDeriv_burnolSineMellinWeighted_eq_logMoments
    {b : ℝ} (hb : 0 < b) (k : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    iteratedDeriv k (burnolSineMellinWeighted b) w =
      (k : ℂ) * mellin (burnolSineMellinLogMoment b (k - 1)) w +
        w * mellin (burnolSineMellinLogMoment b k) w := by
  induction k generalizing w with
  | zero =>
      simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, zero_add]
      rw [burnolSineMellinWeighted]
      congr 1
      congr 1
      funext u
      simp [burnolSineMellinLogMoment]
  | succ k hk =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv k (burnolSineMellinWeighted b) =ᶠ[𝓝 w]
          fun z : ℂ =>
            (k : ℂ) * mellin (burnolSineMellinLogMoment b (k - 1)) z +
              z * mellin (burnolSineMellinLogMoment b k) z := by
        have hstrip : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re ∧ z.re < 1 :=
          (Complex.continuous_re.tendsto w).eventually
            (Ioo_mem_nhds hw0 hw1)
        filter_upwards [hstrip] with z hz
        exact hk hz.1 hz.2
      rw [hfun.deriv_eq]
      have hfirst :=
        (hasDerivAt_mellin_burnolSineMellinLogMoment hb (k - 1) hw0 hw1).const_mul
          (k : ℂ)
      have hsecond := (hasDerivAt_id w).mul
        (hasDerivAt_mellin_burnolSineMellinLogMoment hb k hw0 hw1)
      have hsum := hfirst.add hsecond
      have heq :
          (fun z : ℂ =>
            (k : ℂ) * mellin (burnolSineMellinLogMoment b (k - 1)) z +
              z * mellin (burnolSineMellinLogMoment b k) z) =
            ((fun z : ℂ =>
              (k : ℂ) * mellin (burnolSineMellinLogMoment b (k - 1)) z) +
                id * mellin (burnolSineMellinLogMoment b k)) := by
        funext z
        rfl
      rw [heq, hsum.deriv]
      by_cases hk0 : k = 0
      · subst k
        simp
      · have hidx : k - 1 + 1 = k := by omega
        rw [hidx]
        simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, one_mul, id_eq]
        ring

theorem mellinConvergent_burnolSineMellinLogMoment
    {b : ℝ} (hb : 0 < b) (n : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    MellinConvergent (burnolSineMellinLogMoment b n) w := by
  let a : ℝ := (w.re + 1) / 2
  let c : ℝ := w.re / 2
  apply mellinConvergent_of_isBigO_rpow
    (locallyIntegrableOn_burnolSineMellinLogMoment b n)
    (isBigO_burnolSineMellinLogMoment_rpow_top b n (a := a) (by
      dsimp [a]
      linarith))
    (by dsimp [a]; linarith)
    (isBigO_burnolSineMellinLogMoment_rpow_zero hb n (a := c) (by
      dsimp [c]
      linarith))
    (by dsimp [c]; linarith)

theorem integrableOn_burnolSineMellinLogMoment_integrand
    {b : ℝ} (hb : 0 < b) (n : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn
      (fun u : ℝ =>
        (Real.log u : ℂ) ^ n *
          ((u : ℂ) ^ (w - 2) * Real.sin (b * u)))
      (Ioi 0) := by
  have hM := mellinConvergent_burnolSineMellinLogMoment hb n hw0 hw1
  rw [MellinConvergent] at hM
  apply hM.congr_fun
  · intro u hu
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hpow : (u : ℂ) ^ (w - 1) * (u : ℂ)⁻¹ =
        (u : ℂ) ^ (w - 2) := by
      rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hu0]
      congr 1
      ring
    simp only [burnolSineMellinLogMoment, burnolSineMellinBase,
      smul_eq_mul]
    push_cast
    rw [div_eq_mul_inv, ← hpow]
    ring
  · exact measurableSet_Ioi

theorem iteratedDeriv_burnolSineMellinWeighted_eq_integral
    {b : ℝ} (hb : 0 < b) (k : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    iteratedDeriv k (burnolSineMellinWeighted b) w =
      ∫ u : ℝ in Ioi 0,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (b * u) : ℂ) := by
  rw [iteratedDeriv_burnolSineMellinWeighted_eq_logMoments hb k hw0 hw1,
    mellin_burnolSineMellinLogMoment_eq_integral,
    mellin_burnolSineMellinLogMoment_eq_integral]
  have hprev := integrableOn_burnolSineMellinLogMoment_integrand
    hb (k - 1) hw0 hw1
  have hcurrent := integrableOn_burnolSineMellinLogMoment_integrand
    hb k hw0 hw1
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hprev.const_mul (k : ℂ)) (hcurrent.const_mul w)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [burnolPhiLogFactor]
  ring

def burnolSineMellinGammaMain (b : ℝ) (w : ℂ) : ℂ :=
  w * ((1 - w)⁻¹ * (b : ℂ) ^ (1 - w) *
    Complex.cos (Real.pi * w / 2) * Complex.Gamma w)

theorem burnolSineMellinWeighted_eq_gammaMain
    {b : ℝ} (hb : 0 < b) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolSineMellinWeighted b w = burnolSineMellinGammaMain b w := by
  have hzero :
      mellin (burnolSineMellinBase b) w =
        mellin (burnolSineMellinLogMoment b 0) w := by
    congr 1
    funext u
    simp [burnolSineMellinLogMoment]
  rw [burnolSineMellinWeighted, hzero,
    mellin_burnolSineMellinLogMoment_eq_integral]
  simp only [pow_zero, one_mul]
  rw [integral_Ioi_cpow_mul_sin_eq_gamma hb hw0 hw1]
  rfl

theorem iteratedDeriv_burnolSineMellinWeighted_eq_gammaMain
    {b : ℝ} (hb : 0 < b) (k : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    iteratedDeriv k (burnolSineMellinWeighted b) w =
      iteratedDeriv k (burnolSineMellinGammaMain b) w := by
  have heq : burnolSineMellinWeighted b =ᶠ[𝓝 w]
      burnolSineMellinGammaMain b := by
    have hstrip : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re ∧ z.re < 1 :=
      (Complex.continuous_re.tendsto w).eventually
        (Ioo_mem_nhds hw0 hw1)
    filter_upwards [hstrip] with z hz
    exact burnolSineMellinWeighted_eq_gammaMain hb hz.1 hz.2
  exact heq.iteratedDeriv_eq k

theorem integral_Ioi_burnolPhiLogFactor_eq_iteratedDeriv_gammaMain
    {b : ℝ} (hb : 0 < b) (k : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    (∫ u : ℝ in Ioi 0,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (b * u) : ℂ)) =
      iteratedDeriv k (burnolSineMellinGammaMain b) w := by
  calc
    (∫ u : ℝ in Ioi 0,
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (b * u) : ℂ)) =
        iteratedDeriv k (burnolSineMellinWeighted b) w :=
      (iteratedDeriv_burnolSineMellinWeighted_eq_integral
        hb k hw0 hw1).symm
    _ = iteratedDeriv k (burnolSineMellinGammaMain b) w :=
      iteratedDeriv_burnolSineMellinWeighted_eq_gammaMain hb k hw0 hw1

theorem integrableOn_burnolPhiLogFactor_mul_cpow_mul_sin_Ioi
    {b : ℝ} (hb : 0 < b) (k : ℕ) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn
      (fun u : ℝ =>
        burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
          (Real.sin (b * u) : ℂ))
      (Ioi 0) := by
  have hprev := integrableOn_burnolSineMellinLogMoment_integrand
    hb (k - 1) hw0 hw1
  have hcurrent := integrableOn_burnolSineMellinLogMoment_integrand
    hb k hw0 hw1
  have hsum : IntegrableOn
      (fun u : ℝ =>
        (k : ℂ) *
            ((Real.log u : ℂ) ^ (k - 1) *
              ((u : ℂ) ^ (w - 2) * Real.sin (b * u))) +
          w *
            ((Real.log u : ℂ) ^ k *
              ((u : ℂ) ^ (w - 2) * Real.sin (b * u))))
      (Ioi 0) :=
    (hprev.const_mul (k : ℂ)).add (hcurrent.const_mul w)
  apply hsum.congr_fun
  · intro u _
    simp only [burnolPhiLogFactor]
    ring
  · exact measurableSet_Ioi

theorem burnolPhi_eq_mainIntegral_add_seriesRemainder
    (w : ℂ) (k : ℕ) {t : ℝ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) (ht : 0 < t) :
    burnolPhi w k t =
      ((Real.pi * t : ℝ) : ℂ)⁻¹ *
        (∫ u : ℝ in Ioi 0,
          burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
            (Real.sin (2 * Real.pi * t * u) : ℂ)) +
        burnolPhiSeriesRemainder w k t := by
  let f : ℝ → ℂ := fun u =>
    burnolPhiLogFactor w k u * ((u : ℂ) ^ (w - 2)) *
      (Real.sin (2 * Real.pi * t * u) : ℂ)
  have hb : 0 < 2 * Real.pi * t := by positivity
  have hfull : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      (integrableOn_burnolPhiLogFactor_mul_cpow_mul_sin_Ioi
        hb k hw0 hw1)
  have hlow : IntegrableOn f (Ioc 0 1) :=
    hfull.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn f (Ioi 1) :=
    hfull.mono_set (Ioi_subset_Ioi zero_le_one)
  have hwhole :
      (∫ u : ℝ in Ioi 0, f u) =
        (∫ u : ℝ in Ioc 0 1, f u) +
          ∫ u : ℝ in Ioi 1, f u := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hlow htail
  have hcorrection :=
    burnolPhiSmallCorrection_eq_seriesRemainder w k hw0 ht.ne'
  rw [burnolPhiSmallCorrection] at hcorrection
  rw [burnolPhi]
  change burnolPhiBoundaryTerm k t +
      ((Real.pi * t : ℝ) : ℂ)⁻¹ * (∫ u : ℝ in Ioi 1, f u) =
    ((Real.pi * t : ℝ) : ℂ)⁻¹ * (∫ u : ℝ in Ioi 0, f u) +
      burnolPhiSeriesRemainder w k t
  rw [hwhole]
  calc
    burnolPhiBoundaryTerm k t +
        ((Real.pi * t : ℝ) : ℂ)⁻¹ * (∫ u : ℝ in Ioi 1, f u) =
      ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ((∫ u : ℝ in Ioc 0 1, f u) + ∫ u : ℝ in Ioi 1, f u) +
        (burnolPhiBoundaryTerm k t -
          ((Real.pi * t : ℝ) : ℂ)⁻¹ * ∫ u : ℝ in Ioc 0 1, f u) := by ring
    _ = ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ((∫ u : ℝ in Ioc 0 1, f u) + ∫ u : ℝ in Ioi 1, f u) +
        burnolPhiSeriesRemainder w k t := by rw [hcorrection]

def burnolPhiGammaMain (t : ℝ) (w : ℂ) : ℂ :=
  ((Real.pi * t : ℝ) : ℂ)⁻¹ *
    burnolSineMellinGammaMain (2 * Real.pi * t) w

theorem burnolPhi_eq_iteratedDeriv_gammaMain_add_seriesRemainder
    (w : ℂ) (k : ℕ) {t : ℝ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) (ht : 0 < t) :
    burnolPhi w k t =
      iteratedDeriv k (burnolPhiGammaMain t) w +
        burnolPhiSeriesRemainder w k t := by
  rw [burnolPhi_eq_mainIntegral_add_seriesRemainder w k hw0 hw1 ht,
    integral_Ioi_burnolPhiLogFactor_eq_iteratedDeriv_gammaMain
      (show 0 < 2 * Real.pi * t by positivity) k hw0 hw1]
  change ((Real.pi * t : ℝ) : ℂ)⁻¹ *
        iteratedDeriv k (burnolSineMellinGammaMain (2 * Real.pi * t)) w +
      burnolPhiSeriesRemainder w k t =
    iteratedDeriv k
        (fun z : ℂ => ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          burnolSineMellinGammaMain (2 * Real.pi * t) z) w +
      burnolPhiSeriesRemainder w k t
  rw [iteratedDeriv_const_mul_field]

theorem burnolPhiGammaMain_eq_explicit
    (w : ℂ) {t : ℝ} (ht : 0 < t) :
    burnolPhiGammaMain t w =
      2 * (((2 * Real.pi * t : ℝ) : ℂ) ^ (-w)) *
        (w / (1 - w)) * Complex.cos (Real.pi * w / 2) *
          Complex.Gamma w := by
  have hb : 0 < 2 * Real.pi * t := by positivity
  have hbC : (((2 * Real.pi * t : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hb.ne'
  have hpow :
      (((2 * Real.pi * t : ℝ) : ℂ)) ^ (1 - w) =
        (((2 * Real.pi * t : ℝ) : ℂ)) *
          (((2 * Real.pi * t : ℝ) : ℂ)) ^ (-w) := by
    calc
      (((2 * Real.pi * t : ℝ) : ℂ)) ^ (1 - w) =
          (((2 * Real.pi * t : ℝ) : ℂ)) ^ ((1 : ℂ) + (-w)) := by
        congr 1
      _ = (((2 * Real.pi * t : ℝ) : ℂ)) ^ (1 : ℂ) *
          (((2 * Real.pi * t : ℝ) : ℂ)) ^ (-w) :=
        Complex.cpow_add _ _ hbC
      _ = (((2 * Real.pi * t : ℝ) : ℂ)) *
          (((2 * Real.pi * t : ℝ) : ℂ)) ^ (-w) := by
        rw [Complex.cpow_one]
  have hpt : Real.pi * t ≠ 0 := mul_ne_zero Real.pi_ne_zero ht.ne'
  have hscaleReal :
      (Real.pi * t)⁻¹ * (2 * Real.pi * t) = 2 := by
    field_simp
  have hscale :
      (((Real.pi * t : ℝ) : ℂ))⁻¹ *
          (((2 * Real.pi * t : ℝ) : ℂ)) = 2 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    exact_mod_cast hscaleReal
  rw [burnolPhiGammaMain, burnolSineMellinGammaMain, hpow, div_eq_mul_inv]
  calc
    (((Real.pi * t : ℝ) : ℂ))⁻¹ *
        (w * ((1 - w)⁻¹ *
          ((((2 * Real.pi * t : ℝ) : ℂ)) *
            (((2 * Real.pi * t : ℝ) : ℂ)) ^ (-w)) *
          Complex.cos (Real.pi * w / 2) * Complex.Gamma w)) =
      ((((Real.pi * t : ℝ) : ℂ))⁻¹ *
          (((2 * Real.pi * t : ℝ) : ℂ))) *
        (((2 * Real.pi * t : ℝ) : ℂ)) ^ (-w) *
          (w * (1 - w)⁻¹) * Complex.cos (Real.pi * w / 2) *
            Complex.Gamma w := by ring
    _ = 2 * (((2 * Real.pi * t : ℝ) : ℂ) ^ (-w)) *
        (w * (1 - w)⁻¹) * Complex.cos (Real.pi * w / 2) *
          Complex.Gamma w := by rw [hscale]

theorem norm_burnolPhi_sub_iteratedDeriv_gammaMain_le
    (w : ℂ) {k : ℕ} {t : ℝ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (ht0 : 0 < t) (ht1 : |t| ≤ 1) :
    ‖burnolPhi w k t - iteratedDeriv k (burnolPhiGammaMain t) w‖ ≤
      burnolPhiSeriesBound k := by
  rw [burnolPhi_eq_iteratedDeriv_gammaMain_add_seriesRemainder
    w k hw0 hw1 ht0, add_sub_cancel_left]
  exact norm_burnolPhiSeriesRemainder_le w hw0.le ht1

def burnolUSpectral (w : ℂ) : ℂ :=
  2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-w)) *
    (w / (1 - w)) * Complex.cos (Real.pi * w / 2) *
      Complex.Gamma w

theorem burnolPhiGammaMain_eq_U_mul_cpow
    (w : ℂ) {t : ℝ} (ht : 0 < t) :
    burnolPhiGammaMain t w =
      burnolUSpectral w * (t : ℂ) ^ (-w) := by
  rw [burnolPhiGammaMain_eq_explicit w ht]
  rw [show (((2 * Real.pi * t : ℝ) : ℂ)) =
      (((2 * Real.pi : ℝ) : ℂ)) * (t : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg (by positivity) ht.le]
  rw [burnolUSpectral]
  ring

def burnolOpenCriticalStrip : Set ℂ :=
  {w | 0 < w.re ∧ w.re < 1}

theorem isOpen_burnolOpenCriticalStrip : IsOpen burnolOpenCriticalStrip := by
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem differentiableOn_burnolUSpectral :
    DifferentiableOn ℂ burnolUSpectral burnolOpenCriticalStrip := by
  intro w hw
  have hbase : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hcpow : DifferentiableAt ℂ
      (fun z : ℂ => (((2 * Real.pi : ℝ) : ℂ)) ^ (-z)) w :=
    differentiableAt_id.neg.const_cpow (Or.inl hbase)
  have hden : (1 - w) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hw.2]
  have hratio : DifferentiableAt ℂ (fun z : ℂ => z / (1 - z)) w :=
    differentiableAt_id.div
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id) hden
  have hcos : DifferentiableAt ℂ
      (fun z : ℂ => Complex.cos (Real.pi * z / 2)) w := by
    fun_prop
  have hgamma : DifferentiableAt ℂ Complex.Gamma w := by
    apply Complex.differentiableAt_Gamma w
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith [hw.1]
  unfold burnolUSpectral
  exact (((((differentiableAt_const (c := (2 : ℂ))).mul hcpow).mul hratio).mul hcos).mul
    hgamma).differentiableWithinAt

theorem contDiffOn_burnolUSpectral {n : WithTop ℕ∞} :
    ContDiffOn ℂ n burnolUSpectral burnolOpenCriticalStrip :=
  differentiableOn_burnolUSpectral.contDiffOn isOpen_burnolOpenCriticalStrip

theorem iteratedDeriv_ofReal_cpow_neg
    (n : ℕ) {t : ℝ} (ht : 0 < t) (w : ℂ) :
    iteratedDeriv n (fun z : ℂ => (t : ℂ) ^ (-z)) w =
      (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-w) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hfun : (fun z : ℂ => (t : ℂ) ^ (-z)) =
      fun z : ℂ => Complex.exp (-(Real.log t : ℂ) * z) := by
    funext z
    rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le]
    congr 1
    ring
  rw [hfun]
  rw [congrFun (iteratedDeriv_cexp_const_mul n (-(Real.log t : ℂ))) w]
  rw [← congrFun hfun w]

theorem iteratedDeriv_burnolPhiGammaMain_eq_sum
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (burnolPhiGammaMain t) w =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * iteratedDeriv i burnolUSpectral w *
          ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w)) := by
  have hmain : burnolPhiGammaMain t =
      fun z : ℂ => burnolUSpectral z * (t : ℂ) ^ (-z) := by
    funext z
    exact burnolPhiGammaMain_eq_U_mul_cpow z ht
  rw [hmain]
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hcpow : ContDiffAt ℂ k (fun z : ℂ => (t : ℂ) ^ (-z)) w := by
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    rw [show (fun z : ℂ => (t : ℂ) ^ (-z)) =
        fun z : ℂ => Complex.exp (-(Real.log t : ℂ) * z) by
      funext z
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le]
      congr 1
      ring]
    fun_prop
  change iteratedDeriv k
      (burnolUSpectral * fun z : ℂ => (t : ℂ) ^ (-z)) w = _
  rw [iteratedDeriv_mul hU hcpow]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_ofReal_cpow_neg (k - i) ht w]

def burnolGammaMainDerivCoeffBound (w : ℂ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * ‖iteratedDeriv i burnolUSpectral w‖

theorem burnolGammaMainDerivCoeffBound_nonneg (w : ℂ) (k : ℕ) :
    0 ≤ burnolGammaMainDerivCoeffBound w k := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

theorem norm_iteratedDeriv_burnolPhiGammaMain_le
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) :
    ‖iteratedDeriv k (burnolPhiGammaMain t) w‖ ≤
      burnolGammaMainDerivCoeffBound w k *
        (1 + |Real.log t|) ^ k * t ^ (-w.re) := by
  rw [iteratedDeriv_burnolPhiGammaMain_eq_sum k hw0 hw1 ht0]
  calc
    ‖∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * iteratedDeriv i burnolUSpectral w *
          ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w))‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℂ) * iteratedDeriv i burnolUSpectral w *
          ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        ((k.choose i : ℝ) * ‖iteratedDeriv i burnolUSpectral w‖) *
          ((1 + |Real.log t|) ^ k * t ^ (-w.re)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
      have hlogBase : |Real.log t| ≤ 1 + |Real.log t| := by linarith [abs_nonneg (Real.log t)]
      have hlogPow : |Real.log t| ^ (k - i) ≤
          (1 + |Real.log t|) ^ k := by
        calc
          |Real.log t| ^ (k - i) ≤ (1 + |Real.log t|) ^ (k - i) :=
            pow_le_pow_left₀ (abs_nonneg _) hlogBase (k - i)
          _ ≤ (1 + |Real.log t|) ^ k :=
            pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log t)])
              (Nat.sub_le k i)
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
        Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [norm_natCast, Complex.neg_re]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlogPow (Real.rpow_nonneg ht0.le _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ = burnolGammaMainDerivCoeffBound w k *
        (1 + |Real.log t|) ^ k * t ^ (-w.re) := by
      rw [burnolGammaMainDerivCoeffBound, mul_assoc, Finset.sum_mul]

theorem norm_burnolPhi_le_small
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolPhi w k t‖ ≤
      (burnolGammaMainDerivCoeffBound w k + burnolPhiSeriesBound k) *
        (1 + |Real.log t|) ^ k * t ^ (-w.re) := by
  have hweight :
      1 ≤ (1 + |Real.log t|) ^ k * t ^ (-w.re) := by
    have hlog : 1 ≤ (1 + |Real.log t|) ^ k :=
      one_le_pow₀ (by linarith [abs_nonneg (Real.log t)])
    have hrpow : 1 ≤ t ^ (-w.re) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ (1 + |Real.log t|) ^ k * t ^ (-w.re) :=
        mul_le_mul hlog hrpow (by norm_num) (by positivity)
  have hmain := norm_iteratedDeriv_burnolPhiGammaMain_le k hw0 hw1 ht0
  have hremainder :
      ‖burnolPhiSeriesRemainder w k t‖ ≤ burnolPhiSeriesBound k := by
    exact norm_burnolPhiSeriesRemainder_le w hw0.le (by simpa [abs_of_pos ht0])
  rw [burnolPhi_eq_iteratedDeriv_gammaMain_add_seriesRemainder
    w k hw0 hw1 ht0]
  calc
    ‖iteratedDeriv k (burnolPhiGammaMain t) w +
        burnolPhiSeriesRemainder w k t‖ ≤
      ‖iteratedDeriv k (burnolPhiGammaMain t) w‖ +
        ‖burnolPhiSeriesRemainder w k t‖ := norm_add_le _ _
    _ ≤ burnolGammaMainDerivCoeffBound w k *
          ((1 + |Real.log t|) ^ k * t ^ (-w.re)) +
        burnolPhiSeriesBound k :=
      add_le_add (by simpa only [mul_assoc] using hmain) hremainder
    _ ≤ burnolGammaMainDerivCoeffBound w k *
          ((1 + |Real.log t|) ^ k * t ^ (-w.re)) +
        burnolPhiSeriesBound k *
          ((1 + |Real.log t|) ^ k * t ^ (-w.re)) := by
      apply add_le_add (le_refl _)
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hweight (burnolPhiSeriesBound_nonneg k))
    _ = (burnolGammaMainDerivCoeffBound w k + burnolPhiSeriesBound k) *
        (1 + |Real.log t|) ^ k * t ^ (-w.re) := by ring

theorem aestronglyMeasurable_burnolPhi_restrict
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {s : Set ℝ} (hs : MeasurableSet s) (hs0 : s ⊆ Ioi 0) :
    AEStronglyMeasurable (burnolPhi w k)
      (volume.restrict s) := by
  let mainSum : ℝ → ℂ := fun t =>
    ∑ i ∈ Finset.range (k + 1),
      (k.choose i : ℂ) * iteratedDeriv i burnolUSpectral w *
        ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w))
  have hmainMeasurable : Measurable mainSum := by
    dsimp only [mainSum]
    fun_prop
  have hrepresentative : AEStronglyMeasurable
      (fun t => mainSum t + burnolPhiSeriesRemainder w k t)
      (volume.restrict s) :=
    (hmainMeasurable.add
      (measurable_burnolPhiSeriesRemainder w k)).aestronglyMeasurable
  apply hrepresentative.congr
  filter_upwards [ae_restrict_mem hs] with t ht
  have ht0 : 0 < t := hs0 ht
  rw [burnolPhi_eq_iteratedDeriv_gammaMain_add_seriesRemainder
    w k hw0 hw1 ht0,
    iteratedDeriv_burnolPhiGammaMain_eq_sum k hw0 hw1 ht0]

theorem aestronglyMeasurable_burnolPhi_Ioc
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    AEStronglyMeasurable (burnolPhi w k)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
  aestronglyMeasurable_burnolPhi_restrict w k hw0 hw1
    measurableSet_Ioc Ioc_subset_Ioi_self

theorem integrableOn_burnolPhi_Ioc
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (burnolPhi w k) (Ioc (0 : ℝ) 1) := by
  have hweight := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    k (a := -w.re) (by linarith)
  have hmajor := hweight.const_mul
    (burnolGammaMainDerivCoeffBound w k + burnolPhiSeriesBound k)
  apply Integrable.mono' hmajor
    (aestronglyMeasurable_burnolPhi_Ioc w k hw0 hw1)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simpa only [mul_assoc] using
    (norm_burnolPhi_le_small w k hw0 hw1 ht.1 ht.2)

theorem integrableOn_burnolPhi_Ioc_zero
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (T : ℝ) :
    IntegrableOn (burnolPhi w k) (Ioc (0 : ℝ) T) := by
  have hsmall := integrableOn_burnolPhi_Ioc w k hw0 hw1
  by_cases hT : T ≤ 1
  · exact hsmall.mono_set fun t ht => ⟨ht.1, ht.2.trans hT⟩
  have h1T : 1 ≤ T := le_of_lt (lt_of_not_ge hT)
  let C : ℝ :=
    (1 + ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u) / Real.pi
  have hnum :
      0 ≤ 1 + ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u := by
    linarith [integral_burnolPhiTailMajor_nonneg w k]
  have hlargeMeasurable : AEStronglyMeasurable (burnolPhi w k)
      (volume.restrict (Ioc (1 : ℝ) T)) :=
    aestronglyMeasurable_burnolPhi_restrict w k hw0 hw1
      measurableSet_Ioc fun t ht => zero_lt_one.trans ht.1
  have hconstant : IntegrableOn (fun _ : ℝ => C) (Ioc (1 : ℝ) T) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hlarge : IntegrableOn (burnolPhi w k) (Ioc (1 : ℝ) T) := by
    apply Integrable.mono' hconstant hlargeMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hden : Real.pi ≤ Real.pi * t := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left ht.1.le Real.pi_pos.le)
    calc
      ‖burnolPhi w k t‖ ≤
          (1 + ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u) /
            (Real.pi * t) := norm_burnolPhi_le w k hw1 (zero_lt_one.trans ht.1)
      _ ≤ C := by
        exact div_le_div_of_nonneg_left hnum Real.pi_pos hden
  rw [← Ioc_union_Ioc_eq_Ioc zero_le_one h1T]
  exact hsmall.union hlarge

/-! ### Pointwise Hardy averaging -/

/-- Burnol's pointwise Hardy averaging operator on the positive half-line. -/
def burnolHardyAverage (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)⁻¹ * ∫ u : ℝ in Ioc 0 t, f u

theorem norm_burnolHardyAverage_le_of_norm_le
    {f : ℝ → ℂ} {B t : ℝ} (ht : 0 < t)
    (hbound : ∀ u ∈ Ioc (0 : ℝ) t, ‖f u‖ ≤ B) :
    ‖burnolHardyAverage f t‖ ≤ B := by
  have hintegral :
      ‖∫ u : ℝ in Ioc 0 t, f u‖ ≤ B * t := by
    have h := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Ioc (0 : ℝ) t) measure_Ioc_lt_top hbound
    simpa only [Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal ht.le] using h
  rw [burnolHardyAverage, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht]
  calc
    t⁻¹ * ‖∫ u : ℝ in Ioc 0 t, f u‖ ≤ t⁻¹ * (B * t) :=
      mul_le_mul_of_nonneg_left hintegral (inv_nonneg.mpr ht.le)
    _ = B := by field_simp

theorem integral_Ioc_ofReal_cpow_neg
    {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioc 0 t, (u : ℂ) ^ (-w)) =
      (t : ℂ) ^ (1 - w) / (1 - w) := by
  have hexp : -1 < (-w).re := by simp only [Complex.neg_re]; linarith
  have hne : -w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  rw [← intervalIntegral.integral_of_le ht.le,
    integral_cpow (Or.inl hexp), Complex.ofReal_zero,
    Complex.zero_cpow hne, sub_zero]
  congr 1 <;> ring

theorem integrableOn_neg_log_pow_mul_cpow_neg_Ioc
    (n : ℕ) {w : ℂ} (hw1 : w.re < 1) :
    IntegrableOn
      (fun u : ℝ => (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w))
      (Ioc (0 : ℝ) 1) := by
  have hmajor := integrableOn_abs_log_pow_mul_rpow_Ioc
    n (a := -w.re) (by linarith)
  apply Integrable.mono' hmajor
  · fun_prop
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.neg_re]

theorem integral_Ioc_neg_log_pow_mul_cpow_neg
    (n : ℕ) {w : ℂ} (hw1 : w.re < 1) :
    (∫ u : ℝ in Ioc 0 1,
      (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)) =
        n.factorial / (1 - w) ^ (n + 1) := by
  have hq : 0 < (1 - w).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hmoment := integral_Ioc_log_pow_mul_cpow_sub_one n hq
  have hexp : (1 - w) - 1 = -w := by ring
  rw [hexp] at hmoment
  calc
    (∫ u : ℝ in Ioc 0 1,
        (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)) =
      (-1 : ℂ) ^ n *
        ∫ u : ℝ in Ioc 0 1,
          (Real.log u : ℂ) ^ n * (u : ℂ) ^ (-w) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with u
        rw [neg_pow]
        ring
    _ = (-1 : ℂ) ^ n *
        ((-1 : ℂ) ^ n * n.factorial / (1 - w) ^ (n + 1)) := by
      rw [hmoment]
    _ = n.factorial / (1 - w) ^ (n + 1) := by
      have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [show (-1 : ℂ) ^ n *
          ((-1 : ℂ) ^ n * n.factorial / (1 - w) ^ (n + 1)) =
        ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) *
          (n.factorial / (1 - w) ^ (n + 1)) by ring,
        hsign, one_mul]

def burnolHardyLogMomentClosed (n : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (1 - w) *
    ∑ m ∈ Finset.range (n + 1),
      (n.choose m : ℂ) * (m.factorial : ℂ) /
        (1 - w) ^ (m + 1) * (-(Real.log t : ℂ)) ^ (n - m)

theorem integral_Ioc_neg_log_pow_mul_cpow_neg_eq_closed
    (n : ℕ) {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioc 0 t,
      (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)) =
        burnolHardyLogMomentClosed n w t := by
  let f : ℝ → ℂ := fun u =>
    (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)
  let expanded : ℝ → ℂ := fun x =>
    (t : ℂ) ^ (-w) *
      ∑ m ∈ Finset.range (n + 1),
        (n.choose m : ℂ) *
          ((-(Real.log x : ℂ)) ^ m * (x : ℂ) ^ (-w)) *
            (-(Real.log t : ℂ)) ^ (n - m)
  have hscaled :
      (∫ x : ℝ in Ioc 0 1, f (t * x)) =
        ∫ x : ℝ in Ioc 0 1, expanded x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hlog :
        -(Real.log (t * x) : ℂ) =
          -(Real.log x : ℂ) + -(Real.log t : ℂ) := by
      rw [Real.log_mul ht.ne' hx.1.ne']
      push_cast
      ring
    have hcpow : ((t * x : ℝ) : ℂ) ^ (-w) =
        (t : ℂ) ^ (-w) * (x : ℂ) ^ (-w) := by
      rw [Complex.ofReal_mul]
      exact Complex.mul_cpow_ofReal_nonneg ht.le hx.1.le (-w)
    dsimp only [f, expanded]
    rw [hlog, hcpow, add_pow, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hintegralExpanded :
      (∫ x : ℝ in Ioc 0 1, expanded x) =
        (t : ℂ) ^ (-w) *
          ∑ m ∈ Finset.range (n + 1),
            (n.choose m : ℂ) * (m.factorial : ℂ) /
              (1 - w) ^ (m + 1) *
                (-(Real.log t : ℂ)) ^ (n - m) := by
    dsimp only [expanded]
    rw [integral_const_mul]
    rw [MeasureTheory.integral_finsetSum]
    · apply congrArg ((t : ℂ) ^ (-w) * ·)
      apply Finset.sum_congr rfl
      intro m _
      rw [integral_mul_const,
        integral_const_mul,
        integral_Ioc_neg_log_pow_mul_cpow_neg m hw1]
      ring
    · intro m _
      exact ((integrableOn_neg_log_pow_mul_cpow_neg_Ioc m hw1).const_mul
        (n.choose m : ℂ)).mul_const ((-(Real.log t : ℂ)) ^ (n - m))
  have hscale :
      t • (∫ x : ℝ in 0..1, f (t * x)) =
        ∫ x : ℝ in 0..t, f x := by
    simpa only [mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left
        (a := (0 : ℝ)) (b := (1 : ℝ)) f t)
  have hpow : (t : ℂ) ^ (1 - w) =
      (t : ℂ) * (t : ℂ) ^ (-w) := by
    calc
      (t : ℂ) ^ (1 - w) = (t : ℂ) ^ ((1 : ℂ) + (-w)) := by
        congr 1
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-w) :=
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')
      _ = (t : ℂ) * (t : ℂ) ^ (-w) := by rw [Complex.cpow_one]
  rw [← intervalIntegral.integral_of_le ht.le]
  change (∫ u : ℝ in 0..t, f u) = _
  rw [← hscale]
  rw [intervalIntegral.integral_of_le zero_le_one, hscaled, hintegralExpanded]
  rw [burnolHardyLogMomentClosed, hpow, Complex.real_smul]
  ring

theorem iteratedDeriv_one_sub_inv
    (n : ℕ) {w : ℂ} (hw1 : w.re < 1) :
    iteratedDeriv n (fun z : ℂ => (1 - z)⁻¹) w =
      n.factorial / (1 - w) ^ (n + 1) := by
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hfun : (fun z : ℂ => (1 - z)⁻¹) =
      fun z : ℂ => ((-1 : ℂ) * z + 1)⁻¹ := by
    funext z
    congr 1
    ring
  rw [hfun, iteratedDeriv_eq_iterate,
    congrFun (iter_deriv_inv_linear n (-1 : ℂ) 1) w]
  have hsign : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hexp : (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) := by omega
  rw [show (-1 : ℂ) * w + 1 = 1 - w by ring]
  rw [hexp, zpow_neg_coe_of_pos (1 - w) (by omega)]
  field_simp
  rw [pow_two, hsign, one_mul]

theorem iteratedDeriv_one_sub_inv_mul_cpow_neg
    (n : ℕ) {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n
        (fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w =
      (t : ℂ) ^ (-w) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℂ) * (m.factorial : ℂ) /
            (1 - w) ^ (m + 1) *
              (-(Real.log t : ℂ)) ^ (n - m) := by
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hinv : ContDiffAt ℂ n (fun z : ℂ => (1 - z)⁻¹) w := by
    fun_prop
  have hcpow : ContDiffAt ℂ n (fun z : ℂ => (t : ℂ) ^ (-z)) w := by
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    rw [show (fun z : ℂ => (t : ℂ) ^ (-z)) =
        fun z : ℂ => Complex.exp (-(Real.log t : ℂ) * z) by
      funext z
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le]
      congr 1
      ring]
    fun_prop
  change iteratedDeriv n
      ((fun z : ℂ => (1 - z)⁻¹) * fun z : ℂ => (t : ℂ) ^ (-z)) w = _
  rw [iteratedDeriv_mul hinv hcpow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [iteratedDeriv_one_sub_inv m hw1,
    iteratedDeriv_ofReal_cpow_neg (n - m) ht w]
  ring

theorem burnolHardyAverage_neg_log_pow_mul_cpow_neg
    (n : ℕ) {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    burnolHardyAverage
        (fun u : ℝ => (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)) t =
      iteratedDeriv n
        (fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ (1 - w) =
      (t : ℂ) * (t : ℂ) ^ (-w) := by
    calc
      (t : ℂ) ^ (1 - w) = (t : ℂ) ^ ((1 : ℂ) + (-w)) := by
        congr 1
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-w) :=
        Complex.cpow_add _ _ htC
      _ = (t : ℂ) * (t : ℂ) ^ (-w) := by rw [Complex.cpow_one]
  rw [burnolHardyAverage,
    integral_Ioc_neg_log_pow_mul_cpow_neg_eq_closed n hw1 ht,
    iteratedDeriv_one_sub_inv_mul_cpow_neg n hw1 ht,
    burnolHardyLogMomentClosed, hpow]
  calc
    (t : ℂ)⁻¹ * ((t : ℂ) * (t : ℂ) ^ (-w) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℂ) * (m.factorial : ℂ) /
            (1 - w) ^ (m + 1) *
              (-(Real.log t : ℂ)) ^ (n - m)) =
      ((t : ℂ)⁻¹ * (t : ℂ)) * (t : ℂ) ^ (-w) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℂ) * (m.factorial : ℂ) /
            (1 - w) ^ (m + 1) *
              (-(Real.log t : ℂ)) ^ (n - m) := by ring
    _ = (t : ℂ) ^ (-w) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℂ) * (m.factorial : ℂ) /
            (1 - w) ^ (m + 1) *
              (-(Real.log t : ℂ)) ^ (n - m) := by
      rw [inv_mul_cancel₀ htC, one_mul]

theorem burnolHardyAverage_ofReal_cpow_neg
    {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    burnolHardyAverage (fun u : ℝ => (u : ℂ) ^ (-w)) t =
      (1 - w)⁻¹ * (t : ℂ) ^ (-w) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ (1 - w) =
      (t : ℂ) * (t : ℂ) ^ (-w) := by
    calc
      (t : ℂ) ^ (1 - w) = (t : ℂ) ^ ((1 : ℂ) + (-w)) := by
        congr 1
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-w) :=
        Complex.cpow_add _ _ htC
      _ = (t : ℂ) * (t : ℂ) ^ (-w) := by rw [Complex.cpow_one]
  rw [burnolHardyAverage, integral_Ioc_ofReal_cpow_neg hw1 ht, hpow,
    div_eq_mul_inv]
  calc
    (t : ℂ)⁻¹ * ((t : ℂ) * (t : ℂ) ^ (-w) * (1 - w)⁻¹) =
        ((t : ℂ)⁻¹ * (t : ℂ)) * (t : ℂ) ^ (-w) * (1 - w)⁻¹ := by ring
    _ = (1 - w)⁻¹ * (t : ℂ) ^ (-w) := by
      rw [inv_mul_cancel₀ htC]
      ring

theorem burnolHardyAverage_const_mul
    (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    burnolHardyAverage (fun u => c * f u) t =
      c * burnolHardyAverage f t := by
  rw [burnolHardyAverage, burnolHardyAverage, integral_const_mul]
  ring

theorem burnolHardyAverage_phiGammaMain
    {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    burnolHardyAverage (fun u : ℝ => burnolPhiGammaMain u w) t =
      (1 - w)⁻¹ * burnolPhiGammaMain t w := by
  have hintegral :
      (∫ u : ℝ in Ioc 0 t, burnolPhiGammaMain u w) =
        burnolUSpectral w *
          ∫ u : ℝ in Ioc 0 t, (u : ℂ) ^ (-w) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact burnolPhiGammaMain_eq_U_mul_cpow w hu.1
  rw [burnolHardyAverage, hintegral]
  calc
    (t : ℂ)⁻¹ * (burnolUSpectral w *
        ∫ u : ℝ in Ioc 0 t, (u : ℂ) ^ (-w)) =
      burnolUSpectral w * burnolHardyAverage
        (fun u : ℝ => (u : ℂ) ^ (-w)) t := by
        rw [burnolHardyAverage]
        ring
    _ = burnolUSpectral w * ((1 - w)⁻¹ * (t : ℂ) ^ (-w)) := by
      rw [burnolHardyAverage_ofReal_cpow_neg hw1 ht]
    _ = (1 - w)⁻¹ * burnolPhiGammaMain t w := by
      rw [burnolPhiGammaMain_eq_U_mul_cpow w ht]
      ring

theorem burnolHardyAverage_two_phiGammaMain
    {w : ℂ} (hw1 : w.re < 1) {t : ℝ} (ht : 0 < t) :
    burnolHardyAverage
        (burnolHardyAverage (fun u : ℝ => burnolPhiGammaMain u w)) t =
      (1 - w)⁻¹ ^ 2 * burnolPhiGammaMain t w := by
  have hintegral :
      (∫ u : ℝ in Ioc 0 t,
          burnolHardyAverage (fun v : ℝ => burnolPhiGammaMain v w) u) =
        ∫ u : ℝ in Ioc 0 t, (1 - w)⁻¹ * burnolPhiGammaMain u w := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact burnolHardyAverage_phiGammaMain hw1 hu.1
  rw [burnolHardyAverage, hintegral, integral_const_mul]
  change (t : ℂ)⁻¹ * ((1 - w)⁻¹ *
      ∫ u : ℝ in Ioc 0 t, burnolPhiGammaMain u w) = _
  rw [show (t : ℂ)⁻¹ * ((1 - w)⁻¹ *
        ∫ u : ℝ in Ioc 0 t, burnolPhiGammaMain u w) =
      (1 - w)⁻¹ * burnolHardyAverage
        (fun u : ℝ => burnolPhiGammaMain u w) t by
    rw [burnolHardyAverage]
    ring,
    burnolHardyAverage_phiGammaMain hw1 ht]
  ring

theorem burnolHardyAverage_iteratedDeriv_spectralCpow
    (F : ℂ → ℂ) (k : ℕ) {w : ℂ} (hF : ContDiffAt ℂ k F w)
    (hw1 : w.re < 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardyAverage
        (fun u : ℝ => iteratedDeriv k
          (fun z : ℂ => F z * (u : ℂ) ^ (-z)) w) t =
      iteratedDeriv k
        (fun z : ℂ => (1 - z)⁻¹ * (F z * (t : ℂ) ^ (-z))) w := by
  let moment : ℕ → ℝ → ℂ := fun n u =>
    (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)
  let coeff : ℕ → ℂ := fun i =>
    (k.choose i : ℂ) * iteratedDeriv i F w
  have hsubset : Ioc (0 : ℝ) t ⊆ Ioc (0 : ℝ) 1 :=
    fun _ hu => ⟨hu.1, hu.2.trans ht1⟩
  have htermIntegrable : ∀ i ∈ Finset.range (k + 1),
      IntegrableOn (fun u : ℝ => coeff i * moment (k - i) u) (Ioc 0 t) := by
    intro i _
    exact ((integrableOn_neg_log_pow_mul_cpow_neg_Ioc (k - i) hw1).mono_set
      hsubset).const_mul (coeff i)
  have hintegral :
      (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k (fun z : ℂ => F z * (u : ℂ) ^ (-z)) w) =
        ∑ i ∈ Finset.range (k + 1),
          coeff i * ∫ u : ℝ in Ioc 0 t, moment (k - i) u := by
    calc
      (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k (fun z : ℂ => F z * (u : ℂ) ^ (-z)) w) =
        ∫ u : ℝ in Ioc 0 t,
          ∑ i ∈ Finset.range (k + 1), coeff i * moment (k - i) u := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
            have hcpowU : ContDiffAt ℂ k
                (fun z : ℂ => (u : ℂ) ^ (-z)) w := by
              have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.1.ne'
              rw [show (fun z : ℂ => (u : ℂ) ^ (-z)) =
                  fun z : ℂ => Complex.exp (-(Real.log u : ℂ) * z) by
                funext z
                rw [Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu.1.le]
                congr 1
                ring]
              fun_prop
            change iteratedDeriv k
                (F * fun z : ℂ => (u : ℂ) ^ (-z)) w = _
            rw [iteratedDeriv_mul hF hcpowU]
            apply Finset.sum_congr rfl
            intro i _
            rw [iteratedDeriv_ofReal_cpow_neg (k - i) hu.1 w]
      _ = ∑ i ∈ Finset.range (k + 1),
          ∫ u : ℝ in Ioc 0 t, coeff i * moment (k - i) u := by
            rw [MeasureTheory.integral_finsetSum]
            exact htermIntegrable
      _ = ∑ i ∈ Finset.range (k + 1),
          coeff i * ∫ u : ℝ in Ioc 0 t, moment (k - i) u := by
            apply Finset.sum_congr rfl
            intro i _
            rw [integral_const_mul]
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (1 - z)⁻¹) w := by
    fun_prop
  have hcpow : ContDiffAt ℂ k (fun z : ℂ => (t : ℂ) ^ (-z)) w := by
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [show (fun z : ℂ => (t : ℂ) ^ (-z)) =
        fun z : ℂ => Complex.exp (-(Real.log t : ℂ) * z) by
      funext z
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
      congr 1
      ring]
    fun_prop
  have hHardy : ContDiffAt ℂ k
      (fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w :=
    hinv.mul hcpow
  have hfun : (fun z : ℂ => (1 - z)⁻¹ * (F z * (t : ℂ) ^ (-z))) =
      fun z : ℂ => F z *
        ((1 - z)⁻¹ * (t : ℂ) ^ (-z)) := by
    funext z
    ring
  rw [hfun]
  change burnolHardyAverage
      (fun u : ℝ => iteratedDeriv k
        (fun z : ℂ => F z * (u : ℂ) ^ (-z)) w) t =
    iteratedDeriv k
      (F *
        fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w
  rw [iteratedDeriv_mul hF hHardy]
  rw [burnolHardyAverage, hintegral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (t : ℂ)⁻¹ *
      (coeff i * ∫ u : ℝ in Ioc 0 t, moment (k - i) u) =
    (k.choose i : ℂ) * iteratedDeriv i F w *
      iteratedDeriv (k - i)
        (fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w
  calc
    (t : ℂ)⁻¹ *
        (coeff i * ∫ u : ℝ in Ioc 0 t, moment (k - i) u) =
      coeff i * burnolHardyAverage (moment (k - i)) t := by
        rw [burnolHardyAverage]
        ring
    _ = coeff i * iteratedDeriv (k - i)
        (fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w := by
      rw [burnolHardyAverage_neg_log_pow_mul_cpow_neg (k - i) hw1 ht0]
    _ = (k.choose i : ℂ) * iteratedDeriv i F w *
        iteratedDeriv (k - i)
          (fun z : ℂ => (1 - z)⁻¹ * (t : ℂ) ^ (-z)) w := by
      rfl

theorem integrableOn_iteratedDeriv_spectralCpow_Ioc
    (F : ℂ → ℂ) (k : ℕ) {w : ℂ} (hF : ContDiffAt ℂ k F w)
    (hw1 : w.re < 1) :
    IntegrableOn
      (fun u : ℝ => iteratedDeriv k
        (fun z : ℂ => F z * (u : ℂ) ^ (-z)) w)
      (Ioc (0 : ℝ) 1) := by
  let moment : ℕ → ℝ → ℂ := fun n u =>
    (-(Real.log u : ℂ)) ^ n * (u : ℂ) ^ (-w)
  let coeff : ℕ → ℂ := fun i =>
    (k.choose i : ℂ) * iteratedDeriv i F w
  have hsum : IntegrableOn
      (fun u : ℝ => ∑ i ∈ Finset.range (k + 1),
        coeff i * moment (k - i) u) (Ioc (0 : ℝ) 1) := by
    apply integrable_finsetSum
    intro i _
    exact (integrableOn_neg_log_pow_mul_cpow_neg_Ioc (k - i) hw1).const_mul
      (coeff i)
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hcpowU : ContDiffAt ℂ k (fun z : ℂ => (u : ℂ) ^ (-z)) w := by
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.1.ne'
    rw [show (fun z : ℂ => (u : ℂ) ^ (-z)) =
        fun z : ℂ => Complex.exp (-(Real.log u : ℂ) * z) by
      funext z
      rw [Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu.1.le]
      congr 1
      ring]
    fun_prop
  change (∑ i ∈ Finset.range (k + 1), coeff i * moment (k - i) u) =
    iteratedDeriv k (F * fun z : ℂ => (u : ℂ) ^ (-z)) w
  rw [iteratedDeriv_mul hF hcpowU]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_ofReal_cpow_neg (k - i) hu.1 w]

theorem burnolHardyAverage_iteratedDeriv_phiGammaMain
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardyAverage
        (fun u : ℝ => iteratedDeriv k (burnolPhiGammaMain u) w) t =
      iteratedDeriv k
        (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z) w := by
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hintegral :
      (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k (burnolPhiGammaMain u) w) =
        ∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k
            (fun z : ℂ => burnolUSpectral z * (u : ℂ) ^ (-z)) w := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [show burnolPhiGammaMain u =
        fun z : ℂ => burnolUSpectral z * (u : ℂ) ^ (-z) by
      funext z
      exact burnolPhiGammaMain_eq_U_mul_cpow z hu.1]
  have htarget :
      (fun z : ℂ => (1 - z)⁻¹ *
        (burnolUSpectral z * (t : ℂ) ^ (-z))) =
      fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z := by
    funext z
    rw [burnolPhiGammaMain_eq_U_mul_cpow z ht0]
  rw [burnolHardyAverage, hintegral, ← burnolHardyAverage]
  rw [burnolHardyAverage_iteratedDeriv_spectralCpow
    burnolUSpectral k hU hw1 ht0 ht1, htarget]

theorem burnolHardyAverage_two_iteratedDeriv_phiGammaMain
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardyAverage
        (burnolHardyAverage
          (fun u : ℝ => iteratedDeriv k (burnolPhiGammaMain u) w)) t =
      iteratedDeriv k
        (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z) w := by
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (1 - z)⁻¹) w := by
    fun_prop
  let F : ℂ → ℂ := fun z => (1 - z)⁻¹ * burnolUSpectral z
  have hF : ContDiffAt ℂ k F w := by
    dsimp only [F]
    exact hinv.mul hU
  have hintegral :
      (∫ u : ℝ in Ioc 0 t,
          burnolHardyAverage
            (fun v : ℝ => iteratedDeriv k (burnolPhiGammaMain v) w) u) =
        ∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k (fun z : ℂ => F z * (u : ℂ) ^ (-z)) w := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [burnolHardyAverage_iteratedDeriv_phiGammaMain
      k hw0 hw1 hu.1 (hu.2.trans ht1)]
    rw [show (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) =
        fun z : ℂ => F z * (u : ℂ) ^ (-z) by
      funext z
      rw [burnolPhiGammaMain_eq_U_mul_cpow z hu.1]
      dsimp only [F]
      ring]
  have htarget :
      (fun z : ℂ => (1 - z)⁻¹ * (F z * (t : ℂ) ^ (-z))) =
      fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z := by
    funext z
    rw [burnolPhiGammaMain_eq_U_mul_cpow z ht0]
    dsimp only [F]
    ring
  rw [burnolHardyAverage, hintegral, ← burnolHardyAverage]
  rw [burnolHardyAverage_iteratedDeriv_spectralCpow
    F k hF hw1 ht0 ht1, htarget]

theorem integrableOn_iteratedDeriv_phiGammaMain_Ioc
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn
      (fun u : ℝ => iteratedDeriv k (burnolPhiGammaMain u) w)
      (Ioc (0 : ℝ) 1) := by
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hgeneric := integrableOn_iteratedDeriv_spectralCpow_Ioc
    burnolUSpectral k hU hw1
  apply hgeneric.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [show burnolPhiGammaMain u =
      fun z : ℂ => burnolUSpectral z * (u : ℂ) ^ (-z) by
    funext z
    exact burnolPhiGammaMain_eq_U_mul_cpow z hu.1]

theorem integrableOn_burnolPhiSeriesRemainder_Ioc
    (w : ℂ) (k : ℕ) (hw0 : 0 ≤ w.re) :
    IntegrableOn (burnolPhiSeriesRemainder w k) (Ioc (0 : ℝ) 1) := by
  have hconstant : IntegrableOn
      (fun _ : ℝ => burnolPhiSeriesBound k) (Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  apply Integrable.mono' hconstant
    (measurable_burnolPhiSeriesRemainder w k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact norm_burnolPhiSeriesRemainder_le w hw0 (by
    rw [abs_of_pos ht.1]
    exact ht.2)

theorem norm_burnolHardyAverage_phiSeriesRemainder_le
    (w : ℂ) (k : ℕ) (hw0 : 0 ≤ w.re)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolHardyAverage (burnolPhiSeriesRemainder w k) t‖ ≤
      burnolPhiSeriesBound k := by
  apply norm_burnolHardyAverage_le_of_norm_le
    ht0
  intro u hu
  exact norm_burnolPhiSeriesRemainder_le w hw0 (by
    rw [abs_of_pos hu.1]
    exact hu.2.trans ht1)

theorem continuousOn_burnolHardyAverage_phiSeriesRemainder
    (w : ℂ) (k : ℕ) (hw0 : 0 ≤ w.re) :
    ContinuousOn
      (burnolHardyAverage (burnolPhiSeriesRemainder w k))
      (Ioc (0 : ℝ) 1) := by
  have hIcc : IntegrableOn (burnolPhiSeriesRemainder w k)
      (Icc (0 : ℝ) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_burnolPhiSeriesRemainder_Ioc w k hw0
  have hprimitive : ContinuousOn
      (fun t : ℝ => ∫ u : ℝ in Ioc 0 t,
        burnolPhiSeriesRemainder w k u) (Ioc (0 : ℝ) 1) :=
    (intervalIntegral.continuousOn_primitive hIcc).mono Ioc_subset_Icc_self
  have hinverse : ContinuousOn (fun t : ℝ => (t : ℂ)⁻¹)
      (Ioc (0 : ℝ) 1) :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun t ht =>
      Complex.ofReal_ne_zero.mpr ht.1.ne'
  unfold burnolHardyAverage
  exact hinverse.mul hprimitive

theorem integrableOn_burnolHardyAverage_phiSeriesRemainder_Ioc
    (w : ℂ) (k : ℕ) (hw0 : 0 ≤ w.re) :
    IntegrableOn
      (burnolHardyAverage (burnolPhiSeriesRemainder w k))
      (Ioc (0 : ℝ) 1) := by
  have hconstant : IntegrableOn
      (fun _ : ℝ => burnolPhiSeriesBound k) (Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  apply Integrable.mono' hconstant
    ((continuousOn_burnolHardyAverage_phiSeriesRemainder w k hw0).aestronglyMeasurable
      measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact norm_burnolHardyAverage_phiSeriesRemainder_le
    w k hw0 ht.1 ht.2

theorem norm_burnolHardyAverage_two_phiSeriesRemainder_le
    (w : ℂ) (k : ℕ) (hw0 : 0 ≤ w.re)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolHardyAverage
        (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t‖ ≤
      burnolPhiSeriesBound k := by
  apply norm_burnolHardyAverage_le_of_norm_le ht0
  intro u hu
  exact norm_burnolHardyAverage_phiSeriesRemainder_le
    w k hw0 hu.1 (hu.2.trans ht1)

theorem burnolHardyAverage_phi_eq
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardyAverage (burnolPhi w k) t =
      iteratedDeriv k
          (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z) w +
        burnolHardyAverage (burnolPhiSeriesRemainder w k) t := by
  have hsubset : Ioc (0 : ℝ) t ⊆ Ioc (0 : ℝ) 1 :=
    fun _ hu => ⟨hu.1, hu.2.trans ht1⟩
  have hmain : IntegrableOn
      (fun u : ℝ => iteratedDeriv k (burnolPhiGammaMain u) w)
      (Ioc (0 : ℝ) t) :=
    (integrableOn_iteratedDeriv_phiGammaMain_Ioc k hw0 hw1).mono_set hsubset
  have hremainder : IntegrableOn (burnolPhiSeriesRemainder w k)
      (Ioc (0 : ℝ) t) :=
    (integrableOn_burnolPhiSeriesRemainder_Ioc w k hw0.le).mono_set hsubset
  have hintegral :
      (∫ u : ℝ in Ioc 0 t, burnolPhi w k u) =
        (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k (burnolPhiGammaMain u) w) +
        ∫ u : ℝ in Ioc 0 t, burnolPhiSeriesRemainder w k u := by
    calc
      (∫ u : ℝ in Ioc 0 t, burnolPhi w k u) =
        ∫ u : ℝ in Ioc 0 t,
          (iteratedDeriv k (burnolPhiGammaMain u) w +
            burnolPhiSeriesRemainder w k u) := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
              exact burnolPhi_eq_iteratedDeriv_gammaMain_add_seriesRemainder
                w k hw0 hw1 hu.1
      _ = (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k (burnolPhiGammaMain u) w) +
        ∫ u : ℝ in Ioc 0 t, burnolPhiSeriesRemainder w k u :=
          integral_add hmain hremainder
  rw [burnolHardyAverage, hintegral]
  calc
    (t : ℂ)⁻¹ *
        ((∫ u : ℝ in Ioc 0 t,
            iteratedDeriv k (burnolPhiGammaMain u) w) +
          ∫ u : ℝ in Ioc 0 t, burnolPhiSeriesRemainder w k u) =
      burnolHardyAverage
          (fun u : ℝ => iteratedDeriv k (burnolPhiGammaMain u) w) t +
        burnolHardyAverage (burnolPhiSeriesRemainder w k) t := by
          rw [burnolHardyAverage, burnolHardyAverage]
          ring
    _ = iteratedDeriv k
          (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z) w +
        burnolHardyAverage (burnolPhiSeriesRemainder w k) t := by
      rw [burnolHardyAverage_iteratedDeriv_phiGammaMain
        k hw0 hw1 ht0 ht1]

theorem burnolHardyAverage_two_phi_eq
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t =
      iteratedDeriv k
          (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z) w +
        burnolHardyAverage
          (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t := by
  have hsubset : Ioc (0 : ℝ) t ⊆ Ioc (0 : ℝ) 1 :=
    fun _ hu => ⟨hu.1, hu.2.trans ht1⟩
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (1 - z)⁻¹) w := by
    fun_prop
  let F : ℂ → ℂ := fun z => (1 - z)⁻¹ * burnolUSpectral z
  have hF : ContDiffAt ℂ k F w := by
    dsimp only [F]
    exact hinv.mul hU
  have hmainGeneric := integrableOn_iteratedDeriv_spectralCpow_Ioc
    F k hF hw1
  have hmain : IntegrableOn
      (fun u : ℝ => iteratedDeriv k
        (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w)
      (Ioc (0 : ℝ) t) := by
    apply (hmainGeneric.mono_set hsubset).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [show (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) =
        fun z : ℂ => F z * (u : ℂ) ^ (-z) by
      funext z
      rw [burnolPhiGammaMain_eq_U_mul_cpow z hu.1]
      dsimp only [F]
      ring]
  have hremainder : IntegrableOn
      (burnolHardyAverage (burnolPhiSeriesRemainder w k))
      (Ioc (0 : ℝ) t) :=
    (integrableOn_burnolHardyAverage_phiSeriesRemainder_Ioc
      w k hw0.le).mono_set hsubset
  have hintegral :
      (∫ u : ℝ in Ioc 0 t,
          burnolHardyAverage (burnolPhi w k) u) =
        (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k
            (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w) +
        ∫ u : ℝ in Ioc 0 t,
          burnolHardyAverage (burnolPhiSeriesRemainder w k) u := by
    calc
      (∫ u : ℝ in Ioc 0 t, burnolHardyAverage (burnolPhi w k) u) =
        ∫ u : ℝ in Ioc 0 t,
          (iteratedDeriv k
              (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w +
            burnolHardyAverage (burnolPhiSeriesRemainder w k) u) := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
              exact burnolHardyAverage_phi_eq
                w k hw0 hw1 hu.1 (hu.2.trans ht1)
      _ = (∫ u : ℝ in Ioc 0 t,
          iteratedDeriv k
            (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w) +
        ∫ u : ℝ in Ioc 0 t,
          burnolHardyAverage (burnolPhiSeriesRemainder w k) u :=
          integral_add hmain hremainder
  rw [burnolHardyAverage, hintegral]
  calc
    (t : ℂ)⁻¹ *
        ((∫ u : ℝ in Ioc 0 t,
            iteratedDeriv k
              (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w) +
          ∫ u : ℝ in Ioc 0 t,
            burnolHardyAverage (burnolPhiSeriesRemainder w k) u) =
      burnolHardyAverage
          (burnolHardyAverage
            (fun u : ℝ => iteratedDeriv k (burnolPhiGammaMain u) w)) t +
        burnolHardyAverage
          (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t := by
            have hmainIntegral :
                (∫ u : ℝ in Ioc 0 t,
                  iteratedDeriv k
                    (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w) =
                  ∫ u : ℝ in Ioc 0 t,
                    burnolHardyAverage
                      (fun v : ℝ => iteratedDeriv k
                        (burnolPhiGammaMain v) w) u := by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
              exact (burnolHardyAverage_iteratedDeriv_phiGammaMain
                k hw0 hw1 hu.1 (hu.2.trans ht1)).symm
            rw [hmainIntegral]
            change (t : ℂ)⁻¹ * (_ + _) = (t : ℂ)⁻¹ * _ + (t : ℂ)⁻¹ * _
            ring
    _ = iteratedDeriv k
          (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z) w +
        burnolHardyAverage
          (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t := by
      rw [burnolHardyAverage_two_iteratedDeriv_phiGammaMain
        k hw0 hw1 ht0 ht1]

/-- Burnol's pointwise `(1 - M)^2` operator. -/
def burnolHardySquareDifference (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t - 2 * burnolHardyAverage f t +
    burnolHardyAverage (burnolHardyAverage f) t

def burnolPhiHardySeriesRemainder (w : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  burnolPhiSeriesRemainder w k t -
    2 * burnolHardyAverage (burnolPhiSeriesRemainder w k) t +
      burnolHardyAverage
        (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t

def burnolPhiHardyGammaMain (t : ℝ) (w : ℂ) : ℂ :=
  burnolPhiGammaMain t w -
    2 * ((1 - w)⁻¹ * burnolPhiGammaMain t w) +
      (1 - w)⁻¹ ^ 2 * burnolPhiGammaMain t w

theorem burnolPhiHardyGammaMain_eq_ratio
    {t : ℝ} {w : ℂ} (hw1 : w.re < 1) :
    burnolPhiHardyGammaMain t w =
      (w / (1 - w)) ^ 2 * burnolPhiGammaMain t w := by
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  rw [burnolPhiHardyGammaMain, div_eq_mul_inv]
  field_simp
  ring

def burnolVSpectral (w : ℂ) : ℂ :=
  (w / (1 - w)) ^ 2 * burnolUSpectral w

theorem burnolUSpectral_eq_zetaRatio
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hzeta : riemannZeta w ≠ 0) :
    burnolUSpectral w =
      (w / (1 - w)) * (riemannZeta (1 - w) / riemannZeta w) := by
  have hn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hwne1 : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [riemannZeta_one_sub hn hwne1]
  unfold burnolUSpectral
  field_simp [hzeta]
  rw [show (((2 * Real.pi : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) by
    push_cast
    ring]
  ring

theorem burnolVSpectral_eq_source
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hzeta : riemannZeta w ≠ 0) :
    burnolVSpectral w =
      (w / (1 - w)) ^ 3 *
        (riemannZeta (1 - w) / riemannZeta w) := by
  rw [burnolVSpectral, burnolUSpectral_eq_zetaRatio hw0 hw1 hzeta]
  ring

theorem burnolVSpectral_critical_eq_APhaseMultiplier
    (xi : ℝ)
    (hzeta : riemannZeta (burnolCriticalLineAtFrequency xi) ≠ 0) :
    burnolVSpectral (burnolCriticalLineAtFrequency xi) =
      burnolAPhaseMultiplier xi := by
  rw [burnolVSpectral_eq_source (by norm_num [burnolCriticalLineAtFrequency])
      (by norm_num [burnolCriticalLineAtFrequency]) hzeta,
    burnolAPhaseMultiplier_eq_source xi hzeta]

theorem ae_burnolVSpectral_critical_eq_APhaseMultiplier :
    ∀ᵐ xi : ℝ ∂volume,
      burnolVSpectral (burnolCriticalLineAtFrequency xi) =
        burnolAPhaseMultiplier xi := by
  filter_upwards [ae_riemannZeta_burnolCriticalLineAtFrequency_ne_zero] with xi hzeta
  exact burnolVSpectral_critical_eq_APhaseMultiplier xi hzeta

theorem differentiableOn_burnolVSpectral :
    DifferentiableOn ℂ burnolVSpectral burnolOpenCriticalStrip := by
  intro w hw
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith [hw.2]
  have hratio : DifferentiableAt ℂ (fun z : ℂ => z / (1 - z)) w := by
    fun_prop
  have hU : DifferentiableAt ℂ burnolUSpectral w :=
    (differentiableOn_burnolUSpectral w hw).differentiableAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hw)
  unfold burnolVSpectral
  exact ((hratio.pow 2).mul hU).differentiableWithinAt

theorem contDiffOn_burnolVSpectral {n : WithTop ℕ∞} :
    ContDiffOn ℂ n burnolVSpectral burnolOpenCriticalStrip :=
  differentiableOn_burnolVSpectral.contDiffOn isOpen_burnolOpenCriticalStrip

theorem iteratedDeriv_burnolPhiHardyGammaMain_eq_V_cpow
    (k : ℕ) {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    iteratedDeriv k (burnolPhiHardyGammaMain t) w =
      iteratedDeriv k
        (fun z : ℂ => burnolVSpectral z * (t : ℂ) ^ (-z)) w := by
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have heq : burnolPhiHardyGammaMain t =ᶠ[𝓝 w]
      fun z : ℂ => burnolVSpectral z * (t : ℂ) ^ (-z) := by
    filter_upwards [isOpen_burnolOpenCriticalStrip.mem_nhds hwmem] with z hz
    rw [burnolPhiHardyGammaMain_eq_ratio hz.2,
      burnolPhiGammaMain_eq_U_mul_cpow z ht, burnolVSpectral]
    ring
  exact heq.iteratedDeriv_eq k

theorem iteratedDeriv_burnolPhiHardyGammaMain_eq_sum
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (burnolPhiHardyGammaMain t) w =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * iteratedDeriv i burnolVSpectral w *
          ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w)) := by
  rw [iteratedDeriv_burnolPhiHardyGammaMain_eq_V_cpow k ht hw0 hw1]
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hV : ContDiffAt ℂ k burnolVSpectral w :=
    (contDiffOn_burnolVSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hcpow : ContDiffAt ℂ k (fun z : ℂ => (t : ℂ) ^ (-z)) w := by
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    rw [show (fun z : ℂ => (t : ℂ) ^ (-z)) =
        fun z : ℂ => Complex.exp (-(Real.log t : ℂ) * z) by
      funext z
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le]
      congr 1
      ring]
    fun_prop
  change iteratedDeriv k
      (burnolVSpectral * fun z : ℂ => (t : ℂ) ^ (-z)) w = _
  rw [iteratedDeriv_mul hV hcpow]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedDeriv_ofReal_cpow_neg (k - i) ht w]

def burnolVMainDerivCoeffBound (w : ℂ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℝ) * ‖iteratedDeriv i burnolVSpectral w‖

theorem burnolVMainDerivCoeffBound_nonneg (w : ℂ) (k : ℕ) :
    0 ≤ burnolVMainDerivCoeffBound w k := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

theorem norm_iteratedDeriv_burnolPhiHardyGammaMain_le
    (k : ℕ) {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) :
    ‖iteratedDeriv k (burnolPhiHardyGammaMain t) w‖ ≤
      burnolVMainDerivCoeffBound w k *
        (1 + |Real.log t|) ^ k * t ^ (-w.re) := by
  rw [iteratedDeriv_burnolPhiHardyGammaMain_eq_sum k hw0 hw1 ht0]
  calc
    ‖∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℂ) * iteratedDeriv i burnolVSpectral w *
          ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w))‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        ‖(k.choose i : ℂ) * iteratedDeriv i burnolVSpectral w *
          ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-w))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        ((k.choose i : ℝ) * ‖iteratedDeriv i burnolVSpectral w‖) *
          ((1 + |Real.log t|) ^ k * t ^ (-w.re)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by
        simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
      have hlogBase : |Real.log t| ≤ 1 + |Real.log t| := by
        linarith [abs_nonneg (Real.log t)]
      have hlogPow : |Real.log t| ^ (k - i) ≤
          (1 + |Real.log t|) ^ k := by
        calc
          |Real.log t| ^ (k - i) ≤ (1 + |Real.log t|) ^ (k - i) :=
            pow_le_pow_left₀ (abs_nonneg _) hlogBase (k - i)
          _ ≤ (1 + |Real.log t|) ^ k :=
            pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log t)])
              (Nat.sub_le k i)
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
        Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [norm_natCast, Complex.neg_re]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hlogPow (Real.rpow_nonneg ht0.le _))
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    _ = burnolVMainDerivCoeffBound w k *
        (1 + |Real.log t|) ^ k * t ^ (-w.re) := by
      rw [burnolVMainDerivCoeffBound, mul_assoc, Finset.sum_mul]

theorem burnolPhiHardyGammaMain_eq_V_mul_cpow
    {t : ℝ} (ht : 0 < t) {w : ℂ} (hw1 : w.re < 1) :
    burnolPhiHardyGammaMain t w =
      burnolVSpectral w * (t : ℂ) ^ (-w) := by
  rw [burnolPhiHardyGammaMain_eq_ratio hw1,
    burnolPhiGammaMain_eq_U_mul_cpow w ht, burnolVSpectral]
  ring

theorem iteratedDeriv_burnolPhiHardyGammaMain_eq
    (k : ℕ) {t : ℝ} (ht : 0 < t)
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    iteratedDeriv k (burnolPhiHardyGammaMain t) w =
      iteratedDeriv k (burnolPhiGammaMain t) w -
          2 * iteratedDeriv k
            (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z) w +
        iteratedDeriv k
          (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z) w := by
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hcpow : ContDiffAt ℂ k (fun z : ℂ => (t : ℂ) ^ (-z)) w := by
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    rw [show (fun z : ℂ => (t : ℂ) ^ (-z)) =
        fun z : ℂ => Complex.exp (-(Real.log t : ℂ) * z) by
      funext z
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le]
      congr 1
      ring]
    fun_prop
  have hmain : ContDiffAt ℂ k (burnolPhiGammaMain t) w := by
    rw [show burnolPhiGammaMain t =
        fun z : ℂ => burnolUSpectral z * (t : ℂ) ^ (-z) by
      funext z
      exact burnolPhiGammaMain_eq_U_mul_cpow z ht]
    exact hU.mul hcpow
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (1 - z)⁻¹) w := by
    fun_prop
  have hone : ContDiffAt ℂ k
      (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z) w :=
    hinv.mul hmain
  have htwo : ContDiffAt ℂ k
      (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z) w :=
    (hinv.pow 2).mul hmain
  have htwice : ContDiffAt ℂ k
      (fun z : ℂ => 2 * ((1 - z)⁻¹ * burnolPhiGammaMain t z)) w :=
    by fun_prop
  unfold burnolPhiHardyGammaMain
  rw [iteratedDeriv_fun_add (hmain.sub htwice) htwo,
    iteratedDeriv_fun_sub hmain htwice,
    iteratedDeriv_const_mul_field]

theorem burnolHardySquareDifference_phi_eq
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardySquareDifference (burnolPhi w k) t =
      (iteratedDeriv k (burnolPhiGammaMain t) w -
          2 * iteratedDeriv k
            (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain t z) w +
        iteratedDeriv k
          (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain t z) w) +
        burnolPhiHardySeriesRemainder w k t := by
  rw [burnolHardySquareDifference, burnolPhiHardySeriesRemainder,
    burnolPhi_eq_iteratedDeriv_gammaMain_add_seriesRemainder
      w k hw0 hw1 ht0,
    burnolHardyAverage_phi_eq w k hw0 hw1 ht0 ht1,
    burnolHardyAverage_two_phi_eq w k hw0 hw1 ht0 ht1]
  ring

theorem burnolHardySquareDifference_phi_eq_gammaMain
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    burnolHardySquareDifference (burnolPhi w k) t =
      iteratedDeriv k (burnolPhiHardyGammaMain t) w +
        burnolPhiHardySeriesRemainder w k t := by
  rw [burnolHardySquareDifference_phi_eq w k hw0 hw1 ht0 ht1,
    iteratedDeriv_burnolPhiHardyGammaMain_eq k ht0 hw0 hw1]

theorem norm_burnolPhiHardySeriesRemainder_le
    (w : ℂ) (k : ℕ) (hw0 : 0 ≤ w.re)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolPhiHardySeriesRemainder w k t‖ ≤
      4 * burnolPhiSeriesBound k := by
  have hzero := norm_burnolPhiSeriesRemainder_le w (k := k) hw0 (by
    rw [abs_of_pos ht0]
    exact ht1)
  have hone := norm_burnolHardyAverage_phiSeriesRemainder_le
    w k hw0 ht0 ht1
  have htwo := norm_burnolHardyAverage_two_phiSeriesRemainder_le
    w k hw0 ht0 ht1
  rw [burnolPhiHardySeriesRemainder]
  calc
    ‖burnolPhiSeriesRemainder w k t -
        2 * burnolHardyAverage (burnolPhiSeriesRemainder w k) t +
          burnolHardyAverage
            (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t‖ ≤
      (‖burnolPhiSeriesRemainder w k t‖ +
        ‖(2 : ℂ) * burnolHardyAverage (burnolPhiSeriesRemainder w k) t‖) +
          ‖burnolHardyAverage
            (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t‖ := by
      exact (norm_add_le _ _).trans <|
        add_le_add (norm_sub_le _ _) (le_refl _)
    _ = ‖burnolPhiSeriesRemainder w k t‖ +
        2 * ‖burnolHardyAverage (burnolPhiSeriesRemainder w k) t‖ +
          ‖burnolHardyAverage
            (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ burnolPhiSeriesBound k + 2 * burnolPhiSeriesBound k +
        burnolPhiSeriesBound k := by
      gcongr
    _ = 4 * burnolPhiSeriesBound k := by ring

theorem norm_burnolHardySquareDifference_phi_sub_gammaMain_le
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolHardySquareDifference (burnolPhi w k) t -
        iteratedDeriv k (burnolPhiHardyGammaMain t) w‖ ≤
      4 * burnolPhiSeriesBound k := by
  rw [burnolHardySquareDifference_phi_eq_gammaMain
    w k hw0 hw1 ht0 ht1, add_sub_cancel_left]
  exact norm_burnolPhiHardySeriesRemainder_le w k hw0.le ht0 ht1

theorem norm_burnolHardyAverage_le_large
    {f : ℝ → ℂ} (n : ℕ) {C L t : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (ht : 1 ≤ t)
    (hf : IntegrableOn f (Ioc (0 : ℝ) t))
    (hlow : ‖∫ u : ℝ in Ioc 0 1, f u‖ ≤ L)
    (hbound : ∀ u : ℝ, 1 ≤ u →
      ‖f u‖ ≤ C * (1 + Real.log u) ^ n / u) :
    ‖burnolHardyAverage f t‖ ≤
      (L + C) * (1 + Real.log t) ^ (n + 1) / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlowInt : IntegrableOn f (Ioc (0 : ℝ) 1) :=
    hf.mono_set fun u hu => ⟨hu.1, hu.2.trans ht⟩
  have hhighInt : IntegrableOn f (Ioc (1 : ℝ) t) :=
    hf.mono_set fun u hu => ⟨zero_lt_one.trans hu.1, hu.2⟩
  have hsplit :
      (∫ u : ℝ in Ioc 0 t, f u) =
        (∫ u : ℝ in Ioc 0 1, f u) + ∫ u : ℝ in Ioc 1 t, f u := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one ht]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc hlowInt hhighInt
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hbase : 1 ≤ 1 + Real.log t := by linarith
  let D : ℝ := C * (1 + Real.log t) ^ n
  have hD : 0 ≤ D := mul_nonneg hC (pow_nonneg (by linarith) _)
  have hmajorInt : IntegrableOn (fun u : ℝ => D / u) (Ioc (1 : ℝ) t) := by
    apply IntegrableOn.mono_set
      ((show ContinuousOn (fun u : ℝ => D / u) (Icc (1 : ℝ) t) by
          apply continuousOn_const.div continuousOn_id
          intro u hu
          exact ne_of_gt (zero_lt_one.trans_le hu.1)).integrableOn_Icc)
    exact Ioc_subset_Icc_self
  have hhighBound :
      ‖∫ u : ℝ in Ioc 1 t, f u‖ ≤ D * Real.log t := by
    have hnorm :
        ‖∫ u : ℝ in Ioc 1 t, f u‖ ≤ ∫ u : ℝ in Ioc 1 t, D / u := by
      exact norm_integral_le_of_norm_le hmajorInt <|
        (ae_restrict_mem measurableSet_Ioc).mono fun u hu => by
          have hu0 : 0 < u := zero_lt_one.trans hu.1
          have hlog : Real.log u ≤ Real.log t :=
            Real.log_le_log hu0 hu.2
          have hpow : (1 + Real.log u) ^ n ≤
              (1 + Real.log t) ^ n := by
            apply pow_le_pow_left₀
            · linarith [Real.log_nonneg hu.1.le]
            · linarith
          calc
            ‖f u‖ ≤ C * (1 + Real.log u) ^ n / u := hbound u hu.1.le
            _ ≤ C * (1 + Real.log t) ^ n / u := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow hC) hu0.le
            _ = D / u := by rfl
    calc
      ‖∫ u : ℝ in Ioc 1 t, f u‖ ≤ ∫ u : ℝ in Ioc 1 t, D / u := hnorm
      _ = D * Real.log t := by
        simp_rw [div_eq_mul_inv]
        rw [← intervalIntegral.integral_of_le ht]
        rw [intervalIntegral.integral_const_mul]
        congr 1
        simpa only [one_div, div_one] using
          (integral_one_div_of_pos one_pos ht0)
  have hinside :
      L + D * Real.log t ≤ (L + C) * (1 + Real.log t) ^ (n + 1) := by
    have hpowOne : 1 ≤ (1 + Real.log t) ^ (n + 1) := one_le_pow₀ hbase
    have hlogLe : Real.log t ≤ 1 + Real.log t := by linarith
    have hDlog : D * Real.log t ≤
        C * (1 + Real.log t) ^ (n + 1) := by
      have hpowNonneg : 0 ≤ (1 + Real.log t) ^ n :=
        pow_nonneg (by linarith) _
      have hprod :
          (1 + Real.log t) ^ n * Real.log t ≤
            (1 + Real.log t) ^ n * (1 + Real.log t) :=
        mul_le_mul_of_nonneg_left hlogLe hpowNonneg
      dsimp only [D]
      calc
        C * (1 + Real.log t) ^ n * Real.log t =
            C * ((1 + Real.log t) ^ n * Real.log t) := by ring
        _ ≤ C * ((1 + Real.log t) ^ n * (1 + Real.log t)) :=
          mul_le_mul_of_nonneg_left hprod hC
        _ = C * (1 + Real.log t) ^ (n + 1) := by rw [pow_succ]
    calc
      L + D * Real.log t ≤
          L * (1 + Real.log t) ^ (n + 1) +
            C * (1 + Real.log t) ^ (n + 1) :=
        add_le_add (by simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hpowOne hL)) hDlog
      _ = (L + C) * (1 + Real.log t) ^ (n + 1) := by ring
  rw [burnolHardyAverage, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht0, hsplit]
  calc
    t⁻¹ * ‖(∫ u : ℝ in Ioc 0 1, f u) + ∫ u : ℝ in Ioc 1 t, f u‖ ≤
      t⁻¹ * (L + D * Real.log t) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht0.le)
        exact (norm_add_le _ _).trans (add_le_add hlow hhighBound)
    _ ≤ t⁻¹ * ((L + C) * (1 + Real.log t) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hinside (inv_nonneg.mpr ht0.le)
    _ = (L + C) * (1 + Real.log t) ^ (n + 1) / t := by
      rw [div_eq_mul_inv]
      ring

def burnolPhiLargeCoeff (w : ℂ) (k : ℕ) : ℝ :=
  (1 + ∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u) / Real.pi

theorem burnolPhiLargeCoeff_nonneg (w : ℂ) (k : ℕ) :
    0 ≤ burnolPhiLargeCoeff w k := by
  exact div_nonneg (by linarith [integral_burnolPhiTailMajor_nonneg w k])
    Real.pi_pos.le

theorem norm_burnolPhi_le_largeCoeff
    (w : ℂ) (k : ℕ) (hw1 : w.re < 1)
    {t : ℝ} (ht : 0 < t) :
    ‖burnolPhi w k t‖ ≤ burnolPhiLargeCoeff w k / t := by
  simpa only [burnolPhiLargeCoeff, div_div] using norm_burnolPhi_le w k hw1 ht

theorem norm_burnolHardyAverage_phi_le_large
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖burnolHardyAverage (burnolPhi w k) t‖ ≤
      (‖∫ u : ℝ in Ioc 0 1, burnolPhi w k u‖ + burnolPhiLargeCoeff w k) *
        (1 + Real.log t) / t := by
  simpa only [pow_one, Nat.zero_add] using
    (norm_burnolHardyAverage_le_large (f := burnolPhi w k) 0
      (burnolPhiLargeCoeff_nonneg w k) (norm_nonneg _) ht
      (integrableOn_burnolPhi_Ioc_zero w k hw0 hw1 t) (le_refl _)
      (fun u hu => by
        simpa only [pow_zero, mul_one] using
          norm_burnolPhi_le_largeCoeff w k hw1 (zero_lt_one.trans_le hu)))

theorem integrableOn_burnolHardyAverage_phi_Ioc
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    IntegrableOn (burnolHardyAverage (burnolPhi w k)) (Ioc (0 : ℝ) 1) := by
  have hwmem : w ∈ burnolOpenCriticalStrip := ⟨hw0, hw1⟩
  have hU : ContDiffAt ℂ k burnolUSpectral w :=
    (contDiffOn_burnolUSpectral w hwmem).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hwmem)
  have hden : 1 - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hinv : ContDiffAt ℂ k (fun z : ℂ => (1 - z)⁻¹) w := by
    fun_prop
  let F : ℂ → ℂ := fun z => (1 - z)⁻¹ * burnolUSpectral z
  have hF : ContDiffAt ℂ k F w := by
    dsimp only [F]
    exact hinv.mul hU
  have hmainGeneric := integrableOn_iteratedDeriv_spectralCpow_Ioc
    F k hF hw1
  have hmain : IntegrableOn
      (fun u : ℝ => iteratedDeriv k
        (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) w)
      (Ioc (0 : ℝ) 1) := by
    apply hmainGeneric.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [show (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain u z) =
        fun z : ℂ => F z * (u : ℂ) ^ (-z) by
      funext z
      rw [burnolPhiGammaMain_eq_U_mul_cpow z hu.1]
      dsimp only [F]
      ring]
  have hremainder := integrableOn_burnolHardyAverage_phiSeriesRemainder_Ioc
    w k hw0.le
  apply (hmain.add hremainder).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact (burnolHardyAverage_phi_eq w k hw0 hw1 hu.1 hu.2).symm

theorem continuousOn_burnolHardyAverage_phi_Ioc_zero
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (T : ℝ) :
    ContinuousOn (burnolHardyAverage (burnolPhi w k)) (Ioc (0 : ℝ) T) := by
  have hIcc : IntegrableOn (burnolPhi w k) (Icc (0 : ℝ) T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_burnolPhi_Ioc_zero w k hw0 hw1 T
  have hprimitive : ContinuousOn
      (fun t : ℝ => ∫ u : ℝ in Ioc 0 t, burnolPhi w k u)
      (Ioc (0 : ℝ) T) :=
    (intervalIntegral.continuousOn_primitive hIcc).mono Ioc_subset_Icc_self
  have hinverse : ContinuousOn (fun t : ℝ => (t : ℂ)⁻¹)
      (Ioc (0 : ℝ) T) :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun t ht =>
      Complex.ofReal_ne_zero.mpr ht.1.ne'
  unfold burnolHardyAverage
  exact hinverse.mul hprimitive

theorem integrableOn_burnolHardyAverage_phi_Ioc_zero
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (T : ℝ) :
    IntegrableOn (burnolHardyAverage (burnolPhi w k)) (Ioc (0 : ℝ) T) := by
  have hsmall := integrableOn_burnolHardyAverage_phi_Ioc w k hw0 hw1
  by_cases hT : T ≤ 1
  · exact hsmall.mono_set fun t ht => ⟨ht.1, ht.2.trans hT⟩
  have h1T : 1 ≤ T := le_of_lt (lt_of_not_ge hT)
  have hcont : ContinuousOn (burnolHardyAverage (burnolPhi w k))
      (Icc (1 : ℝ) T) :=
    (continuousOn_burnolHardyAverage_phi_Ioc_zero
      w k hw0 hw1 T).mono fun t ht =>
        ⟨zero_lt_one.trans_le ht.1, ht.2⟩
  have hhigh : IntegrableOn (burnolHardyAverage (burnolPhi w k))
      (Ioc (1 : ℝ) T) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← Ioc_union_Ioc_eq_Ioc zero_le_one h1T]
  exact hsmall.union hhigh

def burnolPhiHardyFirstLargeCoeff (w : ℂ) (k : ℕ) : ℝ :=
  ‖∫ u : ℝ in Ioc 0 1, burnolPhi w k u‖ + burnolPhiLargeCoeff w k

theorem burnolPhiHardyFirstLargeCoeff_nonneg (w : ℂ) (k : ℕ) :
    0 ≤ burnolPhiHardyFirstLargeCoeff w k :=
  add_nonneg (norm_nonneg _) (burnolPhiLargeCoeff_nonneg w k)

theorem norm_burnolHardyAverage_phi_le_firstLargeCoeff
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖burnolHardyAverage (burnolPhi w k) t‖ ≤
      burnolPhiHardyFirstLargeCoeff w k * (1 + Real.log t) / t := by
  exact norm_burnolHardyAverage_phi_le_large w k hw0 hw1 ht

def burnolPhiHardySecondLargeCoeff (w : ℂ) (k : ℕ) : ℝ :=
  ‖∫ u : ℝ in Ioc 0 1, burnolHardyAverage (burnolPhi w k) u‖ +
    burnolPhiHardyFirstLargeCoeff w k

theorem burnolPhiHardySecondLargeCoeff_nonneg (w : ℂ) (k : ℕ) :
    0 ≤ burnolPhiHardySecondLargeCoeff w k :=
  add_nonneg (norm_nonneg _) (burnolPhiHardyFirstLargeCoeff_nonneg w k)

theorem norm_burnolHardyAverage_two_phi_le_large
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t‖ ≤
      burnolPhiHardySecondLargeCoeff w k * (1 + Real.log t) ^ 2 / t := by
  simpa only [burnolPhiHardySecondLargeCoeff, Nat.reduceAdd] using
    (norm_burnolHardyAverage_le_large
      (f := burnolHardyAverage (burnolPhi w k)) 1
      (burnolPhiHardyFirstLargeCoeff_nonneg w k) (norm_nonneg _) ht
      (integrableOn_burnolHardyAverage_phi_Ioc_zero w k hw0 hw1 t)
      (le_refl _) (fun u hu => by
        simpa only [pow_one] using
          norm_burnolHardyAverage_phi_le_firstLargeCoeff
            w k hw0 hw1 hu))

def burnolPhiHardySquareLargeCoeff (w : ℂ) (k : ℕ) : ℝ :=
  burnolPhiLargeCoeff w k + 2 * burnolPhiHardyFirstLargeCoeff w k +
    burnolPhiHardySecondLargeCoeff w k

theorem burnolPhiHardySquareLargeCoeff_nonneg (w : ℂ) (k : ℕ) :
    0 ≤ burnolPhiHardySquareLargeCoeff w k := by
  exact add_nonneg
    (add_nonneg (burnolPhiLargeCoeff_nonneg w k)
      (mul_nonneg (by norm_num) (burnolPhiHardyFirstLargeCoeff_nonneg w k)))
    (burnolPhiHardySecondLargeCoeff_nonneg w k)

theorem norm_burnolHardySquareDifference_phi_le_large
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖burnolHardySquareDifference (burnolPhi w k) t‖ ≤
      burnolPhiHardySquareLargeCoeff w k * (1 + Real.log t) ^ 2 / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hbase : 1 ≤ 1 + Real.log t := by
    linarith [Real.log_nonneg ht]
  have hpowOne : 1 ≤ (1 + Real.log t) ^ 2 := one_le_pow₀ hbase
  have hbaseLePow : 1 + Real.log t ≤ (1 + Real.log t) ^ 2 := by
    calc
      1 + Real.log t = (1 + Real.log t) * 1 := by ring
      _ ≤ (1 + Real.log t) * (1 + Real.log t) :=
        mul_le_mul_of_nonneg_left hbase (by linarith)
      _ = (1 + Real.log t) ^ 2 := by ring
  have hphi : ‖burnolPhi w k t‖ ≤
      burnolPhiLargeCoeff w k * (1 + Real.log t) ^ 2 / t := by
    calc
      ‖burnolPhi w k t‖ ≤ burnolPhiLargeCoeff w k / t :=
        norm_burnolPhi_le_largeCoeff w k hw1 ht0
      _ ≤ burnolPhiLargeCoeff w k * (1 + Real.log t) ^ 2 / t := by
        exact div_le_div_of_nonneg_right
          (by simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hpowOne
              (burnolPhiLargeCoeff_nonneg w k))) ht0.le
  have hone : ‖burnolHardyAverage (burnolPhi w k) t‖ ≤
      burnolPhiHardyFirstLargeCoeff w k * (1 + Real.log t) ^ 2 / t := by
    calc
      ‖burnolHardyAverage (burnolPhi w k) t‖ ≤
          burnolPhiHardyFirstLargeCoeff w k * (1 + Real.log t) / t :=
        norm_burnolHardyAverage_phi_le_firstLargeCoeff w k hw0 hw1 ht
      _ ≤ burnolPhiHardyFirstLargeCoeff w k *
          (1 + Real.log t) ^ 2 / t := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbaseLePow
            (burnolPhiHardyFirstLargeCoeff_nonneg w k)) ht0.le
  have htwo := norm_burnolHardyAverage_two_phi_le_large w k hw0 hw1 ht
  unfold burnolHardySquareDifference
  calc
    ‖burnolPhi w k t - 2 * burnolHardyAverage (burnolPhi w k) t +
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t‖ ≤
      ‖burnolPhi w k t - 2 * burnolHardyAverage (burnolPhi w k) t‖ +
        ‖burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t‖ :=
      norm_add_le _ _
    _ ≤ (‖burnolPhi w k t‖ +
          ‖2 * burnolHardyAverage (burnolPhi w k) t‖) +
        ‖burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t‖ :=
      add_le_add (norm_sub_le _ _) (le_refl _)
    _ = ‖burnolPhi w k t‖ +
          2 * ‖burnolHardyAverage (burnolPhi w k) t‖ +
        ‖burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t‖ := by
      rw [norm_mul]
      norm_num
    _ ≤ burnolPhiLargeCoeff w k * (1 + Real.log t) ^ 2 / t +
          2 * (burnolPhiHardyFirstLargeCoeff w k *
            (1 + Real.log t) ^ 2 / t) +
        burnolPhiHardySecondLargeCoeff w k *
          (1 + Real.log t) ^ 2 / t := by
      gcongr
    _ = burnolPhiHardySquareLargeCoeff w k *
        (1 + Real.log t) ^ 2 / t := by
      rw [burnolPhiHardySquareLargeCoeff]
      ring

theorem continuousOn_burnolHardyAverage_Ioi
    {f : ℝ → ℂ} (hf : ∀ T : ℝ, IntegrableOn f (Ioc (0 : ℝ) T)) :
    ContinuousOn (burnolHardyAverage f) (Ioi (0 : ℝ)) := by
  intro t ht
  let T : ℝ := t + 1
  have htT : t < T := by
    dsimp only [T]
    linarith
  have hIcc : IntegrableOn f (Icc (0 : ℝ) T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hf T
  have hprimitive : ContinuousOn
      (fun x : ℝ => ∫ u : ℝ in Ioc 0 x, f u) (Ioc (0 : ℝ) T) :=
    (intervalIntegral.continuousOn_primitive hIcc).mono Ioc_subset_Icc_self
  have hinverse : ContinuousOn (fun x : ℝ => (x : ℂ)⁻¹) (Ioc (0 : ℝ) T) :=
    Complex.continuous_ofReal.continuousOn.inv₀ fun x hx =>
      Complex.ofReal_ne_zero.mpr hx.1.ne'
  have hwithin : ContinuousWithinAt (burnolHardyAverage f) (Ioc (0 : ℝ) T) t := by
    unfold burnolHardyAverage
    exact (hinverse.mul hprimitive) t ⟨ht, htT.le⟩
  exact (hwithin.continuousAt (Ioc_mem_nhds ht htT)).continuousWithinAt

theorem continuousOn_burnolHardyAverage_phi_Ioi
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    ContinuousOn (burnolHardyAverage (burnolPhi w k)) (Ioi (0 : ℝ)) :=
  continuousOn_burnolHardyAverage_Ioi
    (integrableOn_burnolPhi_Ioc_zero w k hw0 hw1)

theorem continuousOn_burnolHardyAverage_two_phi_Ioi
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    ContinuousOn (burnolHardyAverage (burnolHardyAverage (burnolPhi w k)))
      (Ioi (0 : ℝ)) :=
  continuousOn_burnolHardyAverage_Ioi
    (integrableOn_burnolHardyAverage_phi_Ioc_zero w k hw0 hw1)

theorem aestronglyMeasurable_burnolHardySquareDifference_phi_Ioi
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    AEStronglyMeasurable (burnolHardySquareDifference (burnolPhi w k))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hphi := aestronglyMeasurable_burnolPhi_restrict
    w k hw0 hw1 measurableSet_Ioi (fun _ ht => ht)
  have hone : AEStronglyMeasurable
      (burnolHardyAverage (burnolPhi w k))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_burnolHardyAverage_phi_Ioi w k hw0 hw1).aestronglyMeasurable
      (μ := volume) measurableSet_Ioi
  have htwo : AEStronglyMeasurable
      (burnolHardyAverage (burnolHardyAverage (burnolPhi w k)))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_burnolHardyAverage_two_phi_Ioi w k hw0 hw1).aestronglyMeasurable
      (μ := volume) measurableSet_Ioi
  unfold burnolHardySquareDifference
  exact (hphi.sub (hone.const_mul 2)).add htwo

theorem norm_burnolHardySquareDifference_phi_le_small
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolHardySquareDifference (burnolPhi w k) t‖ ≤
      burnolVMainDerivCoeffBound w k *
          (1 + |Real.log t|) ^ k * t ^ (-w.re) +
        4 * burnolPhiSeriesBound k := by
  rw [burnolHardySquareDifference_phi_eq_gammaMain
    w k hw0 hw1 ht0 ht1]
  exact (norm_add_le _ _).trans <| add_le_add
    (norm_iteratedDeriv_burnolPhiHardyGammaMain_le k hw0 hw1 ht0)
    (norm_burnolPhiHardySeriesRemainder_le w k hw0.le ht0 ht1)

/-- Burnol's explicit transformed boundary representative, with the physical cutoff applied. -/
def burnolYTransformed (lambda : ℝ) (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (Ici lambda).indicator (burnolHardySquareDifference (burnolPhi s k)) t

theorem aestronglyMeasurable_burnolYTransformed
    (lambda : ℝ) (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    AEStronglyMeasurable (burnolYTransformed lambda s k)
      (volume.restrict (Ioi (0 : ℝ))) := by
  unfold burnolYTransformed
  exact (aestronglyMeasurable_burnolHardySquareDifference_phi_Ioi
    s k hs0 hs1).indicator measurableSet_Ici

theorem integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi :
    IntegrableOn
      (fun t : ℝ => t ^ (-2 : ℝ) +
        (Real.log t) ^ 4 * t ^ (-2 : ℝ)) (Ioi (1 : ℝ)) := by
  have hzero := integrableOn_log_pow_mul_rpow_Ioi_one 0 (-2) (by norm_num)
  have hfour := integrableOn_log_pow_mul_rpow_Ioi_one 4 (-2) (by norm_num)
  have hsum := hzero.add hfour
  apply hsum.congr
  exact ae_of_all _ fun t => by simp only [Pi.add_apply, pow_zero, one_mul]

theorem integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi
    (n : ℕ) {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn
      (fun u : ℝ => (Real.log u : ℂ) ^ n * (u : ℂ) ^ (-a - 1))
      (Ioi (1 : ℝ)) := by
  have hmajor := integrableOn_log_pow_mul_rpow_Ioi_one
    n (-a.re - 1) (by linarith)
  apply Integrable.mono' hmajor
  · fun_prop
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hu.le),
    Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  exact le_rfl

theorem integral_Ioi_log_pow_mul_cpow_neg_sub_one
    (n : ℕ) {a : ℂ} (ha : 0 < a.re) :
    (∫ u : ℝ in Ioi 1,
      (Real.log u : ℂ) ^ n * (u : ℂ) ^ (-a - 1)) =
        n.factorial / a ^ (n + 1) := by
  let f : ℝ → ℂ := fun u =>
    (Real.log u : ℂ) ^ n * (u : ℂ) ^ (-a - 1)
  let g : ℝ → ℂ := (Ioi (1 : ℝ)).indicator f
  have hsub := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have hright : (∫ y : ℝ in Ioi 0, g y) = ∫ y : ℝ in Ioi 1, f y := by
    rw [show g = (Ioi (1 : ℝ)).indicator f by rfl,
      setIntegral_indicator measurableSet_Ioi]
    rw [show Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 by
      ext y
      simp only [mem_inter_iff, mem_Ioi]
      constructor
      · exact fun hy => hy.2
      · exact fun hy => ⟨zero_lt_one.trans hy, hy⟩]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      ((|-1| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        (Iio (1 : ℝ)).indicator
          (fun y : ℝ => (-(Real.log y : ℂ)) ^ n *
            (y : ℂ) ^ (a - 1)) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    have harg : Complex.arg (x : ℂ) ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx0.le]
      exact Real.pi_ne_zero.symm
    have hinvCpow : (((x⁻¹ : ℝ) : ℂ) ^ (-a - 1)) =
        (x : ℂ) ^ (a + 1) := by
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg]
      rw [← Complex.cpow_neg]
      congr 1
      ring
    by_cases hx1 : x < 1
    · have hinv1 : 1 < x⁻¹ := (one_lt_inv₀ hx0).2 hx1
      dsimp only [g]
      rw [Real.rpow_neg_one]
      rw [Set.indicator_of_mem (show x ∈ Iio (1 : ℝ) from hx1),
        Set.indicator_of_mem (show x⁻¹ ∈ Ioi (1 : ℝ) from hinv1)]
      dsimp only [f]
      rw [Real.log_inv, hinvCpow]
      norm_num [Complex.real_smul]
      have hpow : (x : ℂ) ^ (a + 1) =
          (x : ℂ) ^ (2 : ℂ) * (x : ℂ) ^ (a - 1) := by
        rw [← Complex.cpow_add _ _ hxC]
        congr 1
        ring
      rw [hpow, Complex.cpow_two]
      field_simp [hxC]
    · have hx1' : 1 ≤ x := not_lt.mp hx1
      have hinvNot : ¬1 < x⁻¹ := not_lt.mpr ((inv_le_one₀ hx0).2 hx1')
      dsimp only [g]
      rw [Real.rpow_neg_one]
      rw [Set.indicator_of_notMem (show x ∉ Iio (1 : ℝ) from hx1),
        Set.indicator_of_notMem (show x⁻¹ ∉ Ioi (1 : ℝ) from hinvNot)]
      simp
  have hleft :
      (∫ x : ℝ in Ioi 0,
        (|-1| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
      ∫ x : ℝ in Ioc 0 1,
        (-(Real.log x : ℂ)) ^ n * (x : ℂ) ^ (a - 1) := by
    calc
      (∫ x : ℝ in Ioi 0,
          (|-1| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        ∫ x : ℝ in Ioi 0,
          (Iio (1 : ℝ)).indicator
            (fun y : ℝ => (-(Real.log y : ℂ)) ^ n *
              (y : ℂ) ^ (a - 1)) x := by
            apply setIntegral_congr_fun measurableSet_Ioi
            exact hpoint
      _ = ∫ x : ℝ in Ioi (0 : ℝ) ∩ Iio 1,
          (-(Real.log x : ℂ)) ^ n * (x : ℂ) ^ (a - 1) :=
        setIntegral_indicator measurableSet_Iio
      _ = ∫ x : ℝ in Ioo 0 1,
          (-(Real.log x : ℂ)) ^ n * (x : ℂ) ^ (a - 1) := by
        rfl
      _ = ∫ x : ℝ in Ioc 0 1,
          (-(Real.log x : ℂ)) ^ n * (x : ℂ) ^ (a - 1) := by
        rw [integral_Ioc_eq_integral_Ioo]
  have hmoment := integral_Ioc_neg_log_pow_mul_cpow_neg
    n (w := 1 - a) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)
  have hexp : -(1 - a) = a - 1 := by ring
  rw [hexp] at hmoment
  have hden : 1 - (1 - a) = a := by ring
  rw [hden] at hmoment
  rw [← hright, ← hsub, hleft]
  exact hmoment

theorem integral_Ioi_rpow_mul_abs_sin_scaled
    {sigma : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0,
      t ^ (sigma - 2) * |Real.sin (2 * Real.pi * t * u)|) =
      u ^ (1 - sigma) *
        ∫ x : ℝ in Ioi 0,
          x ^ (sigma - 2) * |Real.sin (2 * Real.pi * x)| := by
  let q : ℝ → ℝ := fun x =>
    x ^ (sigma - 2) * |Real.sin (2 * Real.pi * x)|
  have hq : IntegrableOn q (Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_abs_sin_Ioi hsigma0 hsigma1 (2 * Real.pi)
  have hsub := integral_comp_mul_left_Ioi q 0 hu
  simp only [mul_zero] at hsub
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      t ^ (sigma - 2) * |Real.sin (2 * Real.pi * t * u)| =
        u ^ (2 - sigma) * q (u * t) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hpow : u ^ (2 - sigma) * (u * t) ^ (sigma - 2) =
        t ^ (sigma - 2) := by
      rw [Real.mul_rpow hu.le ht0.le]
      rw [← mul_assoc, ← Real.rpow_add hu]
      have hexp : 2 - sigma + (sigma - 2) = 0 := by ring
      rw [hexp, Real.rpow_zero, one_mul]
    dsimp only [q]
    rw [show 2 * Real.pi * (u * t) = 2 * Real.pi * t * u by ring]
    rw [← mul_assoc, hpow]
  calc
    (∫ t : ℝ in Ioi 0,
        t ^ (sigma - 2) * |Real.sin (2 * Real.pi * t * u)|) =
      ∫ t : ℝ in Ioi 0, u ^ (2 - sigma) * q (u * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        exact hpoint
    _ = u ^ (2 - sigma) * ∫ t : ℝ in Ioi 0, q (u * t) := by
      rw [integral_const_mul]
    _ = u ^ (2 - sigma) *
        (u⁻¹ * ∫ x : ℝ in Ioi 0, q x) := by
      rw [hsub]
      simp only [smul_eq_mul]
    _ = u ^ (1 - sigma) * ∫ x : ℝ in Ioi 0, q x := by
      rw [← mul_assoc, ← Real.rpow_neg_one u, ← Real.rpow_add hu]
      congr 1
      ring
    _ = u ^ (1 - sigma) *
        ∫ x : ℝ in Ioi 0,
          x ^ (sigma - 2) * |Real.sin (2 * Real.pi * x)| := by rfl

/-- The scalar produced by Mellin transforming the sine kernel in `burnolPhi`. -/
def burnolPhiMellinCoefficient (z : ℂ) : ℂ :=
  (((Real.pi : ℝ) : ℂ))⁻¹ *
    ((1 - z)⁻¹ * (((2 * Real.pi : ℝ) : ℂ)) ^ (1 - z) *
      Complex.cos (Real.pi * z / 2) * Complex.Gamma z)

theorem burnolPhiMellinCoefficient_mul_eq_USpectral (z : ℂ) :
    burnolPhiMellinCoefficient z * z = burnolUSpectral z := by
  have hpi : (((Real.pi : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hbase : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hscale : (((Real.pi : ℝ) : ℂ))⁻¹ *
      (((2 * Real.pi : ℝ) : ℂ)) = 2 := by
    rw [show (((2 * Real.pi : ℝ) : ℂ)) =
      (2 : ℂ) * ((Real.pi : ℝ) : ℂ) by push_cast; ring]
    field_simp [hpi]
  have hpow : (((2 * Real.pi : ℝ) : ℂ)) ^ (1 - z) =
      (((2 * Real.pi : ℝ) : ℂ)) *
        (((2 * Real.pi : ℝ) : ℂ)) ^ (-z) := by
    calc
      (((2 * Real.pi : ℝ) : ℂ)) ^ (1 - z) =
          (((2 * Real.pi : ℝ) : ℂ)) ^ ((1 : ℂ) + (-z)) := by
            congr 1
      _ = (((2 * Real.pi : ℝ) : ℂ)) ^ (1 : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ)) ^ (-z) :=
        Complex.cpow_add _ _ hbase
      _ = (((2 * Real.pi : ℝ) : ℂ)) *
          (((2 * Real.pi : ℝ) : ℂ)) ^ (-z) := by
        rw [Complex.cpow_one]
  rw [burnolPhiMellinCoefficient, burnolUSpectral, hpow, div_eq_mul_inv]
  calc
    (((Real.pi : ℝ) : ℂ))⁻¹ *
          ((1 - z)⁻¹ *
            ((((2 * Real.pi : ℝ) : ℂ)) *
              (((2 * Real.pi : ℝ) : ℂ)) ^ (-z)) *
            Complex.cos (Real.pi * z / 2) * Complex.Gamma z) * z =
        ((((Real.pi : ℝ) : ℂ))⁻¹ *
            (((2 * Real.pi : ℝ) : ℂ))) *
          (((2 * Real.pi : ℝ) : ℂ)) ^ (-z) *
          (z * (1 - z)⁻¹) * Complex.cos (Real.pi * z / 2) *
            Complex.Gamma z := by ring
    _ = 2 * (((2 * Real.pi : ℝ) : ℂ)) ^ (-z) *
          (z * (1 - z)⁻¹) * Complex.cos (Real.pi * z / 2) *
            Complex.Gamma z := by rw [hscale]

def burnolPhiMellinTailProduct
    (w : ℂ) (k : ℕ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ) ^ (z - 1) * ((Real.pi * p.2 : ℝ) : ℂ)⁻¹ *
    burnolPhiTailIntegrand w k p.2 p.1

theorem norm_burnolPhiMellinTailProduct
    (w : ℂ) (k : ℕ) (z : ℂ)
    {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    ‖burnolPhiMellinTailProduct w k z (u, t)‖ =
      Real.pi⁻¹ * ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) *
        (t ^ (z.re - 2) * |Real.sin (2 * Real.pi * t * u)|) := by
  have hpiT : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have htpow : t ^ (z.re - 1) * (Real.pi * t)⁻¹ =
      Real.pi⁻¹ * t ^ (z.re - 2) := by
    rw [mul_inv]
    calc
      t ^ (z.re - 1) * (Real.pi⁻¹ * t⁻¹) =
          Real.pi⁻¹ * (t ^ (z.re - 1) * t⁻¹) := by ring
      _ = Real.pi⁻¹ * t ^ (z.re - 2) := by
        rw [← Real.rpow_neg_one t, ← Real.rpow_add ht]
        congr 2
        ring
  rw [burnolPhiMellinTailProduct, burnolPhiTailIntegrand,
    norm_mul, norm_mul, norm_inv, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpiT,
    norm_burnolPhiTailPower_of_pos w hu,
    Complex.norm_real, Real.norm_eq_abs, htpow]
  ring

theorem integral_Ioi_burnolPhiMellinTailProduct_section
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1)
    {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0, burnolPhiMellinTailProduct w k z (u, t)) =
      burnolPhiMellinCoefficient z * burnolPhiLogFactor w k u *
        (u : ℂ) ^ (w - z - 1) := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hsine := integral_Ioi_cpow_mul_sin_eq_gamma
    (w := z) (b := 2 * Real.pi * u) (by positivity) hz0 hz1
  have hupow : (u : ℂ) ^ (w - 2) * (u : ℂ) ^ (1 - z) =
      (u : ℂ) ^ (w - z - 1) := by
    rw [← Complex.cpow_add _ _ huC]
    congr 1
    ring
  have hscalePow : (((2 * Real.pi * u : ℝ) : ℂ)) ^ (1 - z) =
      (((2 * Real.pi : ℝ) : ℂ)) ^ (1 - z) *
        (u : ℂ) ^ (1 - z) := by
    rw [show (((2 * Real.pi * u : ℝ) : ℂ)) =
      (((2 * Real.pi : ℝ) : ℂ)) * (u : ℂ) by push_cast; ring]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) hu.le (1 - z)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      burnolPhiMellinTailProduct w k z (u, t) =
        ((((Real.pi : ℝ) : ℂ))⁻¹ * burnolPhiLogFactor w k u *
          (u : ℂ) ^ (w - 2)) *
            ((t : ℂ) ^ (z - 2) *
              (Real.sin (2 * Real.pi * u * t) : ℂ)) := by
    intro t ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have htpow : (t : ℂ) ^ (z - 1) *
        (((Real.pi * t : ℝ) : ℂ))⁻¹ =
          (((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ) ^ (z - 2) := by
      rw [show (((Real.pi * t : ℝ) : ℂ)) =
        ((Real.pi : ℝ) : ℂ) * (t : ℂ) by push_cast; ring,
        mul_inv]
      calc
        (t : ℂ) ^ (z - 1) *
            ((((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ)⁻¹) =
          (((Real.pi : ℝ) : ℂ))⁻¹ *
            ((t : ℂ) ^ (z - 1) * (t : ℂ)⁻¹) := by ring
        _ = (((Real.pi : ℝ) : ℂ))⁻¹ *
            ((t : ℂ) ^ (z - 1) * (t : ℂ) ^ (-1 : ℂ)) := by
          rw [Complex.cpow_neg_one]
        _ = (((Real.pi : ℝ) : ℂ))⁻¹ *
            (t : ℂ) ^ ((z - 1) + (-1 : ℂ)) := by
          rw [Complex.cpow_add _ _ htC]
        _ = (((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ) ^ (z - 2) := by
          congr 2
          ring
    rw [burnolPhiMellinTailProduct, burnolPhiTailIntegrand, htpow]
    rw [show 2 * Real.pi * t * u = 2 * Real.pi * u * t by ring]
    ring
  calc
    (∫ t : ℝ in Ioi 0, burnolPhiMellinTailProduct w k z (u, t)) =
        ∫ t : ℝ in Ioi 0,
          ((((Real.pi : ℝ) : ℂ))⁻¹ * burnolPhiLogFactor w k u *
            (u : ℂ) ^ (w - 2)) *
              ((t : ℂ) ^ (z - 2) *
                (Real.sin (2 * Real.pi * u * t) : ℂ)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact hpoint
    _ = ((((Real.pi : ℝ) : ℂ))⁻¹ * burnolPhiLogFactor w k u *
          (u : ℂ) ^ (w - 2)) *
        (∫ t : ℝ in Ioi 0,
          (t : ℂ) ^ (z - 2) * Real.sin (2 * Real.pi * u * t)) := by
      rw [integral_const_mul]
    _ = ((((Real.pi : ℝ) : ℂ))⁻¹ * burnolPhiLogFactor w k u *
          (u : ℂ) ^ (w - 2)) *
        ((1 - z)⁻¹ * (((2 * Real.pi * u : ℝ) : ℂ)) ^ (1 - z) *
          Complex.cos (Real.pi * z / 2) * Complex.Gamma z) := by
      rw [hsine]
    _ = burnolPhiMellinCoefficient z * burnolPhiLogFactor w k u *
          ((u : ℂ) ^ (w - 2) * (u : ℂ) ^ (1 - z)) := by
      rw [hscalePow]
      unfold burnolPhiMellinCoefficient
      ring
    _ = burnolPhiMellinCoefficient z * burnolPhiLogFactor w k u *
          (u : ℂ) ^ (w - z - 1) := by rw [hupow]

theorem integrable_burnolPhiMellinTailProduct
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    Integrable (burnolPhiMellinTailProduct w k z)
      ((volume.restrict (Ioi (1 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  let C : ℝ := ∫ x : ℝ in Ioi 0,
    x ^ (z.re - 2) * |Real.sin (2 * Real.pi * x)|
  have hCint : IntegrableOn
      (fun x : ℝ => x ^ (z.re - 2) * |Real.sin (2 * Real.pi * x)|)
      (Ioi (0 : ℝ)) :=
    integrableOn_rpow_mul_abs_sin_Ioi hz0 hz1 (2 * Real.pi)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact integral_nonneg_of_ae <|
      (ae_restrict_mem measurableSet_Ioi).mono fun x hx =>
        mul_nonneg (Real.rpow_nonneg hx.le _) (abs_nonneg _)
  have hmeas : AEStronglyMeasurable (burnolPhiMellinTailProduct w k z)
      ((volume.restrict (Ioi (1 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
    unfold burnolPhiMellinTailProduct burnolPhiTailIntegrand burnolPhiLogFactor
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    let A : ℝ := Real.pi⁻¹ * ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2)
    have hA : 0 ≤ A := mul_nonneg
      (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) (norm_nonneg _))
      (Real.rpow_nonneg hu0.le _)
    have hbase := integrableOn_rpow_mul_abs_sin_Ioi
      hz0 hz1 (2 * Real.pi * u)
    have hmajor := hbase.const_mul A
    apply Integrable.mono' hmajor
    · unfold burnolPhiMellinTailProduct burnolPhiTailIntegrand burnolPhiLogFactor
      fun_prop
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [norm_burnolPhiMellinTailProduct w k z hu0 ht0]
    dsimp only [A]
    rw [show 2 * Real.pi * t * u = 2 * Real.pi * u * t by ring]
  · have hsection : ∀ u ∈ Ioi (1 : ℝ),
        (∫ t : ℝ in Ioi 0,
          ‖burnolPhiMellinTailProduct w k z (u, t)‖) =
        (Real.pi⁻¹ * C) * ‖burnolPhiLogFactor w k u‖ *
          u ^ (w.re - z.re - 1) := by
      intro u hu
      have hu0 : 0 < u := zero_lt_one.trans hu
      have hscale := integral_Ioi_rpow_mul_abs_sin_scaled hz0 hz1 hu0
      have hpow : u ^ (w.re - 2) * u ^ (1 - z.re) =
          u ^ (w.re - z.re - 1) := by
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      calc
        (∫ t : ℝ in Ioi 0,
            ‖burnolPhiMellinTailProduct w k z (u, t)‖) =
          ∫ t : ℝ in Ioi 0,
            (Real.pi⁻¹ * ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2)) *
              (t ^ (z.re - 2) * |Real.sin (2 * Real.pi * t * u)|) := by
                apply setIntegral_congr_fun measurableSet_Ioi
                intro t ht
                exact norm_burnolPhiMellinTailProduct w k z hu0 ht
        _ = (Real.pi⁻¹ * ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2)) *
            ∫ t : ℝ in Ioi 0,
              t ^ (z.re - 2) * |Real.sin (2 * Real.pi * t * u)| := by
                rw [integral_const_mul]
        _ = (Real.pi⁻¹ * ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2)) *
            (u ^ (1 - z.re) * C) := by rw [hscale]
        _ = Real.pi⁻¹ * ‖burnolPhiLogFactor w k u‖ *
            (u ^ (w.re - 2) * u ^ (1 - z.re)) * C := by ring
        _ = (Real.pi⁻¹ * C) * ‖burnolPhiLogFactor w k u‖ *
            u ^ (w.re - z.re - 1) := by rw [hpow]; ring
    let D : ℝ := Real.pi⁻¹ * C
    have hD : 0 ≤ D := mul_nonneg (inv_nonneg.mpr Real.pi_pos.le) hC
    let exponent : ℝ := w.re - z.re - 1
    have hexponent : exponent < -1 := by
      dsimp only [exponent]
      linarith
    have hprev := integrableOn_log_pow_mul_rpow_Ioi_one
      (k - 1) exponent hexponent
    have hcurrent := integrableOn_log_pow_mul_rpow_Ioi_one
      k exponent hexponent
    have hpoly := (hprev.const_mul (k : ℝ)).add
      (hcurrent.const_mul ‖w‖)
    have hmajor : IntegrableOn
        (fun u : ℝ => D *
          ((k : ℝ) * (Real.log u) ^ (k - 1) * u ^ exponent +
            ‖w‖ * (Real.log u) ^ k * u ^ exponent))
        (Ioi (1 : ℝ)) := by
      apply (hpoly.const_mul D).congr
      exact ae_of_all _ fun u => by simp only [Pi.add_apply]; ring
    have hformula : IntegrableOn
        (fun u : ℝ => D * ‖burnolPhiLogFactor w k u‖ * u ^ exponent)
        (Ioi (1 : ℝ)) := by
      apply Integrable.mono' hmajor
      · unfold burnolPhiLogFactor
        fun_prop
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := zero_lt_one.trans hu
      have hlogBound := norm_burnolPhiLogFactor_le w k hu.le
      rw [Real.norm_of_nonneg (mul_nonneg
        (mul_nonneg hD (norm_nonneg _)) (Real.rpow_nonneg hu0.le _))]
      dsimp only [exponent]
      calc
        D * ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - z.re - 1) ≤
            D * ((k : ℝ) * (Real.log u) ^ (k - 1) +
              ‖w‖ * (Real.log u) ^ k) * u ^ (w.re - z.re - 1) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogBound hD)
            (Real.rpow_nonneg hu0.le _)
        _ = D * ((k : ℝ) * (Real.log u) ^ (k - 1) *
              u ^ (w.re - z.re - 1) +
            ‖w‖ * (Real.log u) ^ k * u ^ (w.re - z.re - 1)) := by ring
    apply hformula.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [hsection u hu]

theorem integral_Ioi_burnolPhiMellinTailProduct_vertical
    (w : ℂ) (k : ℕ) (z : ℂ) (t : ℝ) :
    (∫ u : ℝ in Ioi 1, burnolPhiMellinTailProduct w k z (u, t)) =
      (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u := by
  rw [← integral_const_mul]
  rfl

theorem integral_Ioi_cpow_mul_burnolPhiTailTerm
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u) =
      burnolPhiMellinCoefficient z *
        ∫ u : ℝ in Ioi 1,
          burnolPhiLogFactor w k u * (u : ℂ) ^ (w - z - 1) := by
  have hprod := integrable_burnolPhiMellinTailProduct w k z hz0 hz1 hwz
  have hswap :
      (∫ u : ℝ in Ioi 1,
          ∫ t : ℝ in Ioi 0, burnolPhiMellinTailProduct w k z (u, t)) =
        ∫ t : ℝ in Ioi 0,
          ∫ u : ℝ in Ioi 1, burnolPhiMellinTailProduct w k z (u, t) :=
    integral_integral_swap hprod
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u) =
      ∫ t : ℝ in Ioi 0,
        ∫ u : ℝ in Ioi 1, burnolPhiMellinTailProduct w k z (u, t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          exact (integral_Ioi_burnolPhiMellinTailProduct_vertical
            w k z t).symm
    _ = ∫ u : ℝ in Ioi 1,
        ∫ t : ℝ in Ioi 0, burnolPhiMellinTailProduct w k z (u, t) :=
      hswap.symm
    _ = ∫ u : ℝ in Ioi 1,
        burnolPhiMellinCoefficient z * burnolPhiLogFactor w k u *
          (u : ℂ) ^ (w - z - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact integral_Ioi_burnolPhiMellinTailProduct_section
        w k z hz0 hz1 (zero_lt_one.trans hu)
    _ = burnolPhiMellinCoefficient z *
        ∫ u : ℝ in Ioi 1,
          burnolPhiLogFactor w k u * (u : ℂ) ^ (w - z - 1) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      ring

theorem integrableOn_burnolPhiLogFactor_mul_cpow_mellinTail
    (w z : ℂ) (k : ℕ) (hwz : w.re < z.re) :
    IntegrableOn
      (fun u : ℝ => burnolPhiLogFactor w k u *
        (u : ℂ) ^ (w - z - 1)) (Ioi (1 : ℝ)) := by
  have ha : 0 < (z - w).re := by
    simp only [Complex.sub_re]
    linarith
  have hexp : w - z - 1 = -(z - w) - 1 := by ring
  rw [show (fun u : ℝ => burnolPhiLogFactor w k u *
      (u : ℂ) ^ (w - z - 1)) =
      fun u : ℝ => burnolPhiLogFactor w k u *
        (u : ℂ) ^ (-(z - w) - 1) by
    funext u
    rw [hexp]]
  cases k with
  | zero =>
      apply ((integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi 0 ha).const_mul w).congr
      exact ae_of_all _ fun u => by
        simp only [burnolPhiLogFactor_zero, pow_zero, one_mul]
  | succ n =>
      have hprev :=
        (integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi n ha).const_mul
          ((n + 1 : ℕ) : ℂ)
      have hcurrent :=
        (integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi (n + 1) ha).const_mul w
      apply (hprev.add hcurrent).congr
      exact ae_of_all _ fun u => by
        have hsub : n + 1 - 1 = n := by omega
        simp only [Pi.add_apply, burnolPhiLogFactor, hsub]
        ring

theorem integral_Ioi_burnolPhiLogFactor_mul_cpow_mellinTail_zero
    (w z : ℂ) (hwz : w.re < z.re) :
    (∫ u : ℝ in Ioi 1,
      burnolPhiLogFactor w 0 u * (u : ℂ) ^ (w - z - 1)) =
        w / (z - w) := by
  have ha : 0 < (z - w).re := by
    simp only [Complex.sub_re]
    linarith
  have hmoment := integral_Ioi_log_pow_mul_cpow_neg_sub_one 0 ha
  have hexp : w - z - 1 = -(z - w) - 1 := by ring
  simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
    zero_add, pow_one] at hmoment
  simp_rw [burnolPhiLogFactor_zero, hexp]
  rw [integral_const_mul, hmoment]
  simp only [div_eq_mul_inv, one_mul]

theorem integral_Ioi_burnolPhiLogFactor_mul_cpow_mellinTail_succ
    (w z : ℂ) (n : ℕ) (hwz : w.re < z.re) :
    (∫ u : ℝ in Ioi 1,
      burnolPhiLogFactor w (n + 1) u * (u : ℂ) ^ (w - z - 1)) =
        (n + 1).factorial * z / (z - w) ^ (n + 2) := by
  let a : ℂ := z - w
  have ha : 0 < a.re := by
    dsimp only [a]
    simp only [Complex.sub_re]
    linarith
  have ha0 : a ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith
  have hprevInt := integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi n ha
  have hcurrentInt := integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi (n + 1) ha
  have hprev := integral_Ioi_log_pow_mul_cpow_neg_sub_one n ha
  have hcurrent := integral_Ioi_log_pow_mul_cpow_neg_sub_one (n + 1) ha
  have hexp : w - z - 1 = -a - 1 := by
    dsimp only [a]
    ring
  have hsub : n + 1 - 1 = n := by omega
  have hintegrand :
      (fun u : ℝ => burnolPhiLogFactor w (n + 1) u *
        (u : ℂ) ^ (w - z - 1)) =
      fun u : ℝ =>
        ((n + 1 : ℕ) : ℂ) *
            ((Real.log u : ℂ) ^ n * (u : ℂ) ^ (-a - 1)) +
          w * ((Real.log u : ℂ) ^ (n + 1) * (u : ℂ) ^ (-a - 1)) := by
    funext u
    simp only [burnolPhiLogFactor, hsub, hexp]
    ring
  rw [hintegrand]
  rw [integral_add (hprevInt.const_mul ((n + 1 : ℕ) : ℂ))
    (hcurrentInt.const_mul w), integral_const_mul, integral_const_mul,
    hprev, hcurrent]
  have hfactorial : ((n + 1 : ℕ) : ℂ) * n.factorial = (n + 1).factorial := by
    rw [Nat.factorial_succ]
    norm_num
  have hfirst : ((n + 1 : ℕ) : ℂ) *
      (n.factorial / (z - w) ^ (n + 1)) =
        (n + 1).factorial / (z - w) ^ (n + 1) := by
    rw [← mul_div_assoc, hfactorial]
  rw [hfirst]
  have hn2 : n + 1 + 1 = n + 2 := by omega
  rw [hn2]
  have hone : ((n + 1).factorial : ℂ) / a ^ (n + 1) =
      ((n + 1).factorial : ℂ) * a / a ^ (n + 2) := by
    apply (div_eq_div_iff (pow_ne_zero _ ha0) (pow_ne_zero _ ha0)).2
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  rw [hone]
  calc
    ((n + 1).factorial : ℂ) * a / a ^ (n + 2) +
        w * (((n + 1).factorial : ℂ) / a ^ (n + 2)) =
      ((n + 1).factorial : ℂ) * (a + w) / a ^ (n + 2) := by ring
    _ = ((n + 1).factorial : ℂ) * z / (z - w) ^ (n + 2) := by
      dsimp only [a]
      ring

theorem integral_Ioi_cpow_mul_burnolPhiTailTerm_zero
    (w z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1)
    (hwz : w.re < z.re) :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w 0 t u) =
      burnolPhiMellinCoefficient z * (w / (z - w)) := by
  rw [integral_Ioi_cpow_mul_burnolPhiTailTerm w 0 z hz0 hz1 hwz,
    integral_Ioi_burnolPhiLogFactor_mul_cpow_mellinTail_zero w z hwz]

theorem integral_Ioi_cpow_mul_burnolPhiTailTerm_succ
    (w z : ℂ) (n : ℕ) (hz0 : 0 < z.re) (hz1 : z.re < 1)
    (hwz : w.re < z.re) :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
        ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w (n + 1) t u) =
      burnolPhiMellinCoefficient z *
        ((n + 1).factorial * z / (z - w) ^ (n + 2)) := by
  rw [integral_Ioi_cpow_mul_burnolPhiTailTerm w (n + 1) z hz0 hz1 hwz,
    integral_Ioi_burnolPhiLogFactor_mul_cpow_mellinTail_succ w z n hwz]

theorem integrableOn_cpow_mul_burnolPhiTailTerm
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    IntegrableOn
      (fun t : ℝ =>
        (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u)
      (Ioi 0) := by
  have hprod := integrable_burnolPhiMellinTailProduct w k z hz0 hz1 hwz
  apply hprod.integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integral_Ioi_burnolPhiMellinTailProduct_vertical w k z t

theorem cpow_mul_burnolPhiBoundaryTerm_zero
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm 0 t =
      (((Real.pi : ℝ) : ℂ))⁻¹ *
        ((t : ℂ) ^ (z - 2) * (Real.sin (2 * Real.pi * t) : ℂ)) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have htpow : (t : ℂ) ^ (z - 1) *
      (((Real.pi * t : ℝ) : ℂ))⁻¹ =
        (((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ) ^ (z - 2) := by
    rw [show (((Real.pi * t : ℝ) : ℂ)) =
      ((Real.pi : ℝ) : ℂ) * (t : ℂ) by push_cast; ring,
      mul_inv]
    calc
      (t : ℂ) ^ (z - 1) *
          ((((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ)⁻¹) =
        (((Real.pi : ℝ) : ℂ))⁻¹ *
          ((t : ℂ) ^ (z - 1) * (t : ℂ)⁻¹) := by ring
      _ = (((Real.pi : ℝ) : ℂ))⁻¹ *
          ((t : ℂ) ^ (z - 1) * (t : ℂ) ^ (-1 : ℂ)) := by
        rw [Complex.cpow_neg_one]
      _ = (((Real.pi : ℝ) : ℂ))⁻¹ *
          (t : ℂ) ^ ((z - 1) + (-1 : ℂ)) := by
        rw [Complex.cpow_add _ _ htC]
      _ = (((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ) ^ (z - 2) := by
        congr 2
        ring
  rw [burnolPhiBoundaryTerm_zero, div_eq_mul_inv]
  calc
    (t : ℂ) ^ (z - 1) *
        ((Real.sin (2 * Real.pi * t) : ℂ) *
          (((Real.pi * t : ℝ) : ℂ))⁻¹) =
      ((t : ℂ) ^ (z - 1) * (((Real.pi * t : ℝ) : ℂ))⁻¹) *
        (Real.sin (2 * Real.pi * t) : ℂ) := by ring
    _ = ((((Real.pi : ℝ) : ℂ))⁻¹ * (t : ℂ) ^ (z - 2)) *
        (Real.sin (2 * Real.pi * t) : ℂ) := by rw [htpow]
    _ = (((Real.pi : ℝ) : ℂ))⁻¹ *
        ((t : ℂ) ^ (z - 2) * (Real.sin (2 * Real.pi * t) : ℂ)) := by ring

theorem integrableOn_cpow_mul_burnolPhiBoundaryTerm_zero
    (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm 0 t)
      (Ioi 0) := by
  have hbase := integrableOn_burnolSineMellinLogMoment_integrand
    (b := 2 * Real.pi) (by positivity) 0 hz0 hz1
  simp only [pow_zero, one_mul] at hbase
  apply (hbase.const_mul (((Real.pi : ℝ) : ℂ))⁻¹).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (cpow_mul_burnolPhiBoundaryTerm_zero z ht).symm

theorem integral_Ioi_cpow_mul_burnolPhiBoundaryTerm_zero
    (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm 0 t) =
      burnolPhiMellinCoefficient z := by
  have hsine := integral_Ioi_cpow_mul_sin_eq_gamma
    (w := z) (b := 2 * Real.pi) (by positivity) hz0 hz1
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm 0 t) =
      ∫ t : ℝ in Ioi 0,
        (((Real.pi : ℝ) : ℂ))⁻¹ *
          ((t : ℂ) ^ (z - 2) * (Real.sin (2 * Real.pi * t) : ℂ)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact cpow_mul_burnolPhiBoundaryTerm_zero z ht
    _ = (((Real.pi : ℝ) : ℂ))⁻¹ *
        ∫ t : ℝ in Ioi 0,
          (t : ℂ) ^ (z - 2) * Real.sin (2 * Real.pi * t) := by
      rw [integral_const_mul]
    _ = burnolPhiMellinCoefficient z := by
      rw [hsine]
      rfl

theorem integrableOn_cpow_mul_burnolPhiBoundaryTerm
    (k : ℕ) (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm k t)
      (Ioi 0) := by
  cases k with
  | zero => exact integrableOn_cpow_mul_burnolPhiBoundaryTerm_zero z hz0 hz1
  | succ n =>
      simpa only [burnolPhiBoundaryTerm_eq_zero_of_pos (Nat.succ_pos n), mul_zero] using
        (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Ioi 0))

theorem integral_Ioi_cpow_mul_burnolPhiBoundaryTerm_succ
    (n : ℕ) (z : ℂ) :
    (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm (n + 1) t) = 0 := by
  simp only [burnolPhiBoundaryTerm_eq_zero_of_pos (k := n + 1) (by omega),
    mul_zero, integral_zero]

theorem mellinConvergent_burnolPhi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    MellinConvergent (burnolPhi w k) z := by
  rw [MellinConvergent]
  have hboundary :=
    integrableOn_cpow_mul_burnolPhiBoundaryTerm k z hz0 hz1
  have htail := integrableOn_cpow_mul_burnolPhiTailTerm w k z hz0 hz1 hwz
  apply (hboundary.add htail).congr_fun
  · intro t _
    simp only [Pi.add_apply, burnolPhi, smul_eq_mul]
    ring
  · exact measurableSet_Ioi

theorem mellin_burnolPhi_eq_USpectral_mul_pole
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    mellin (burnolPhi w k) z =
      (k.factorial : ℂ) * burnolUSpectral z / (z - w) ^ (k + 1) := by
  have hboundary :=
    integrableOn_cpow_mul_burnolPhiBoundaryTerm k z hz0 hz1
  have htail := integrableOn_cpow_mul_burnolPhiTailTerm w k z hz0 hz1 hwz
  rw [mellin]
  have hintegrand :
      (fun t : ℝ => (t : ℂ) ^ (z - 1) • burnolPhi w k t) =
        (fun t : ℝ => (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm k t) +
          fun t : ℝ =>
            (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
              ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u := by
    funext t
    simp only [Pi.add_apply, burnolPhi, smul_eq_mul]
    ring
  rw [hintegrand]
  change (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (z - 1) * burnolPhiBoundaryTerm k t +
        (t : ℂ) ^ (z - 1) * ((Real.pi * t : ℝ) : ℂ)⁻¹ *
          ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u) =
    (k.factorial : ℂ) * burnolUSpectral z / (z - w) ^ (k + 1)
  rw [integral_add hboundary htail]
  have hCz := burnolPhiMellinCoefficient_mul_eq_USpectral z
  cases k with
  | zero =>
      simp only [Nat.factorial_zero, Nat.cast_one, zero_add, pow_one, one_mul]
      rw [integral_Ioi_cpow_mul_burnolPhiBoundaryTerm_zero z hz0 hz1,
        integral_Ioi_cpow_mul_burnolPhiTailTerm_zero w z hz0 hz1 hwz]
      have hzw : z - w ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.zero_re] at hre
        linarith
      calc
        burnolPhiMellinCoefficient z +
            burnolPhiMellinCoefficient z * (w / (z - w)) =
          burnolPhiMellinCoefficient z * z / (z - w) := by
            field_simp [hzw]
            ring
        _ = burnolUSpectral z / (z - w) := by rw [hCz]
  | succ n =>
      rw [integral_Ioi_cpow_mul_burnolPhiBoundaryTerm_succ n z,
        integral_Ioi_cpow_mul_burnolPhiTailTerm_succ w z n hz0 hz1 hwz,
        zero_add]
      have hn2 : n + 1 + 1 = n + 2 := by omega
      rw [hn2]
      calc
        burnolPhiMellinCoefficient z *
            (((n + 1).factorial : ℂ) * z / (z - w) ^ (n + 2)) =
          ((n + 1).factorial : ℂ) *
            (burnolPhiMellinCoefficient z * z) / (z - w) ^ (n + 2) := by ring
        _ = ((n + 1).factorial : ℂ) * burnolUSpectral z /
            (z - w) ^ (n + 2) := by rw [hCz]

/-- The triangular product kernel used to Mellin transform a Hardy average. -/
def burnolHardyMellinProduct (f : ℝ → ℂ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  {q : ℝ × ℝ | q.1 ≤ q.2}.indicator
    (fun q => (q.2 : ℂ) ^ (z - 2) * f q.1) p

theorem aestronglyMeasurable_burnolHardyMellinProduct
    {f : ℝ → ℂ} {z : ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) :
    AEStronglyMeasurable (burnolHardyMellinProduct f z)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hset : MeasurableSet {q : ℝ × ℝ | q.1 ≤ q.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hscalar : Measurable (fun q : ℝ × ℝ => (q.2 : ℂ) ^ (z - 2)) := by
    fun_prop
  exact (hscalar.aestronglyMeasurable.mul hf.comp_fst).indicator hset

theorem norm_burnolHardyMellinProduct
    (f : ℝ → ℂ) (z : ℂ) {u t : ℝ} (ht : 0 < t) :
    ‖burnolHardyMellinProduct f z (u, t)‖ =
      (Ici u).indicator (fun x : ℝ => x ^ (z.re - 2) * ‖f u‖) t := by
  by_cases hut : u ≤ t
  · rw [burnolHardyMellinProduct, Set.indicator_of_mem, Set.indicator_of_mem]
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Complex.sub_re]
      norm_num
    · exact hut
    · exact hut
  · rw [burnolHardyMellinProduct, Set.indicator_of_notMem,
      Set.indicator_of_notMem]
    · exact norm_zero
    · exact hut
    · exact hut

theorem integral_Ioi_norm_burnolHardyMellinProduct
    (f : ℝ → ℂ) (z : ℂ) (hz1 : z.re < 1)
    {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0, ‖burnolHardyMellinProduct f z (u, t)‖) =
      (1 - z.re)⁻¹ * ‖(u : ℂ) ^ (z - 1) * f u‖ := by
  have hset : Ioi (0 : ℝ) ∩ Ici u = Ici u := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ici]
    constructor
    · exact fun ht => ht.2
    · intro ht
      exact ⟨hu.trans_le ht, ht⟩
  have hexp : z.re - 2 < -1 := by linarith
  have hden : 1 - z.re ≠ 0 := by linarith
  have hnormMellin : ‖(u : ℂ) ^ (z - 1) * f u‖ =
      u ^ (z.re - 1) * ‖f u‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re]
    norm_num
  calc
    (∫ t : ℝ in Ioi 0, ‖burnolHardyMellinProduct f z (u, t)‖) =
        ∫ t : ℝ in Ioi 0,
          (Ici u).indicator (fun x : ℝ => x ^ (z.re - 2) * ‖f u‖) t := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            exact norm_burnolHardyMellinProduct f z ht
    _ = ∫ t : ℝ in Ioi 0 ∩ Ici u, t ^ (z.re - 2) * ‖f u‖ := by
      rw [setIntegral_indicator measurableSet_Ici]
    _ = ∫ t : ℝ in Ici u, t ^ (z.re - 2) * ‖f u‖ := by rw [hset]
    _ = ‖f u‖ * ∫ t : ℝ in Ici u, t ^ (z.re - 2) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ici
      intro t _
      ring
    _ = ‖f u‖ * ∫ t : ℝ in Ioi u, t ^ (z.re - 2) := by
      rw [integral_Ici_eq_integral_Ioi]
    _ = ‖f u‖ *
        (-(u ^ ((z.re - 2) + 1)) / ((z.re - 2) + 1)) := by
      rw [integral_Ioi_rpow_of_lt hexp hu]
    _ = (1 - z.re)⁻¹ * (u ^ (z.re - 1) * ‖f u‖) := by
      rw [show (z.re - 2) + 1 = z.re - 1 by ring]
      rw [show z.re - 1 = -(1 - z.re) by ring]
      field_simp [hden]
    _ = (1 - z.re)⁻¹ * ‖(u : ℂ) ^ (z - 1) * f u‖ := by
      rw [hnormMellin]

theorem integrableOn_burnolHardyMellinProduct_section
    (f : ℝ → ℂ) (z : ℂ) (hz1 : z.re < 1)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => burnolHardyMellinProduct f z (u, t))
      (Ioi 0) := by
  have hset : Ici u ∩ Ioi (0 : ℝ) = Ici u := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ici]
    constructor
    · exact fun ht => ht.1
    · intro ht
      exact ⟨ht, hu.trans_le ht⟩
  have hbase : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 2)) (Ioi u) :=
    integrableOn_Ioi_cpow_of_lt (by
      simp only [Complex.sub_re]
      norm_num
      linarith) hu
  change IntegrableOn
    ((Ici u).indicator (fun t : ℝ => (t : ℂ) ^ (z - 2) * f u))
      (Ioi 0)
  rw [integrableOn_indicator_iff measurableSet_Ici, hset]
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (hbase.mul_const (f u))

theorem integrable_burnolHardyMellinProduct
    {f : ℝ → ℂ} {z : ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hM : MellinConvergent f z) (hz1 : z.re < 1) :
    Integrable (burnolHardyMellinProduct f z)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas := aestronglyMeasurable_burnolHardyMellinProduct (z := z) hf
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact integrableOn_burnolHardyMellinProduct_section f z hz1 hu
  · rw [MellinConvergent] at hM
    simp only [smul_eq_mul] at hM
    have hmajor := hM.norm.const_mul (1 - z.re)⁻¹
    apply hmajor.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [integral_Ioi_norm_burnolHardyMellinProduct f z hz1 hu]

theorem integral_Ioi_burnolHardyMellinProduct_section
    (f : ℝ → ℂ) (z : ℂ) (hz1 : z.re < 1)
    {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t)) =
      (1 - z)⁻¹ * ((u : ℂ) ^ (z - 1) * f u) := by
  have hset : Ioi (0 : ℝ) ∩ Ici u = Ici u := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ici]
    constructor
    · exact fun ht => ht.2
    · intro ht
      exact ⟨hu.trans_le ht, ht⟩
  have hden : (1 - z) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  calc
    (∫ t : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t)) =
        ∫ t : ℝ in Ioi 0,
          (Ici u).indicator (fun x : ℝ => (x : ℂ) ^ (z - 2) * f u) t := by
            rfl
    _ = ∫ t : ℝ in Ioi 0 ∩ Ici u, (t : ℂ) ^ (z - 2) * f u := by
      rw [setIntegral_indicator measurableSet_Ici]
    _ = ∫ t : ℝ in Ici u, (t : ℂ) ^ (z - 2) * f u := by rw [hset]
    _ = (∫ t : ℝ in Ici u, (t : ℂ) ^ (z - 2)) * f u := by
      rw [integral_mul_const]
    _ = (∫ t : ℝ in Ioi u, (t : ℂ) ^ (z - 2)) * f u := by
      rw [integral_Ici_eq_integral_Ioi]
    _ = (-(u : ℂ) ^ ((z - 2) + 1) / ((z - 2) + 1)) * f u := by
      rw [integral_Ioi_cpow_of_lt (by
        simp only [Complex.sub_re]
        norm_num
        linarith) hu]
    _ = (1 - z)⁻¹ * ((u : ℂ) ^ (z - 1) * f u) := by
      rw [show (z - 2) + 1 = z - 1 by ring]
      rw [show z - 1 = -(1 - z) by ring]
      field_simp [hden]

theorem integral_Ioi_burnolHardyMellinProduct_vertical
    (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    (∫ u : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t)) =
      (t : ℂ) ^ (z - 2) * ∫ u : ℝ in Ioc 0 t, f u := by
  change (∫ u : ℝ in Ioi 0,
      (Iic t).indicator (fun x : ℝ => (t : ℂ) ^ (z - 2) * f x) u) = _
  rw [setIntegral_indicator measurableSet_Iic]
  change (∫ u : ℝ in Ioc 0 t, (t : ℂ) ^ (z - 2) * f u) = _
  rw [integral_const_mul]

theorem cpow_mul_burnolHardyAverage
    (f : ℝ → ℂ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (z - 1) * burnolHardyAverage f t =
      (t : ℂ) ^ (z - 2) * ∫ u : ℝ in Ioc 0 t, f u := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ (z - 1) * (t : ℂ)⁻¹ =
      (t : ℂ) ^ (z - 2) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ htC]
    congr 1
    ring
  rw [burnolHardyAverage]
  rw [← mul_assoc, hpow]

theorem mellinConvergent_burnolHardyAverage
    {f : ℝ → ℂ} {z : ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hM : MellinConvergent f z) (hz1 : z.re < 1) :
    MellinConvergent (burnolHardyAverage f) z := by
  have hprod := integrable_burnolHardyMellinProduct hf hM hz1
  rw [MellinConvergent]
  apply hprod.integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  calc
    (∫ u : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t)) =
        (t : ℂ) ^ (z - 2) * ∫ u : ℝ in Ioc 0 t, f u :=
      integral_Ioi_burnolHardyMellinProduct_vertical f z t
    _ = (t : ℂ) ^ (z - 1) * burnolHardyAverage f t :=
      (cpow_mul_burnolHardyAverage f z ht).symm
    _ = (t : ℂ) ^ (z - 1) • burnolHardyAverage f t := by
      rw [smul_eq_mul]

theorem mellin_burnolHardyAverage
    {f : ℝ → ℂ} {z : ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hM : MellinConvergent f z) (hz1 : z.re < 1) :
    mellin (burnolHardyAverage f) z = (1 - z)⁻¹ * mellin f z := by
  have hprod := integrable_burnolHardyMellinProduct hf hM hz1
  have hswap :
      (∫ u : ℝ in Ioi 0,
          ∫ t : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t)) =
        ∫ t : ℝ in Ioi 0,
          ∫ u : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t) :=
    integral_integral_swap hprod
  rw [mellin, mellin]
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (z - 1) • burnolHardyAverage f t) =
      ∫ t : ℝ in Ioi 0,
        ∫ u : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          dsimp only
          rw [smul_eq_mul, cpow_mul_burnolHardyAverage f z ht,
            integral_Ioi_burnolHardyMellinProduct_vertical]
    _ = ∫ u : ℝ in Ioi 0,
        ∫ t : ℝ in Ioi 0, burnolHardyMellinProduct f z (u, t) := hswap.symm
    _ = ∫ u : ℝ in Ioi 0,
        (1 - z)⁻¹ * ((u : ℂ) ^ (z - 1) * f u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact integral_Ioi_burnolHardyMellinProduct_section f z hz1 hu
    _ = (1 - z)⁻¹ *
        ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (z - 1) * f u := by
      rw [integral_const_mul]
    _ = (1 - z)⁻¹ *
        ∫ u : ℝ in Ioi 0, (u : ℂ) ^ (z - 1) • f u := by
      simp only [smul_eq_mul]

theorem mellinConvergent_burnolHardyAverage_phi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    MellinConvergent (burnolHardyAverage (burnolPhi w k)) z := by
  have hphiMeas := aestronglyMeasurable_burnolPhi_restrict
    w k hw0 hw1 measurableSet_Ioi (fun _ ht => ht)
  exact mellinConvergent_burnolHardyAverage hphiMeas
    (mellinConvergent_burnolPhi w k z hz0 hz1 hwz) hz1

theorem mellin_burnolHardyAverage_phi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    mellin (burnolHardyAverage (burnolPhi w k)) z =
      (1 - z)⁻¹ *
        ((k.factorial : ℂ) * burnolUSpectral z / (z - w) ^ (k + 1)) := by
  have hphiMeas := aestronglyMeasurable_burnolPhi_restrict
    w k hw0 hw1 measurableSet_Ioi (fun _ ht => ht)
  rw [mellin_burnolHardyAverage hphiMeas
      (mellinConvergent_burnolPhi w k z hz0 hz1 hwz) hz1,
    mellin_burnolPhi_eq_USpectral_mul_pole w k z hz0 hz1 hwz]

theorem mellinConvergent_burnolHardyAverage_two_phi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    MellinConvergent
      (burnolHardyAverage (burnolHardyAverage (burnolPhi w k))) z := by
  have honeMeas : AEStronglyMeasurable
      (burnolHardyAverage (burnolPhi w k))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_burnolHardyAverage_phi_Ioi w k hw0 hw1).aestronglyMeasurable
      (μ := volume) measurableSet_Ioi
  exact mellinConvergent_burnolHardyAverage honeMeas
    (mellinConvergent_burnolHardyAverage_phi
      w k z hw0 hw1 hz0 hz1 hwz) hz1

theorem mellin_burnolHardyAverage_two_phi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    mellin (burnolHardyAverage (burnolHardyAverage (burnolPhi w k))) z =
      (1 - z)⁻¹ ^ 2 *
        ((k.factorial : ℂ) * burnolUSpectral z / (z - w) ^ (k + 1)) := by
  have honeMeas : AEStronglyMeasurable
      (burnolHardyAverage (burnolPhi w k))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (continuousOn_burnolHardyAverage_phi_Ioi w k hw0 hw1).aestronglyMeasurable
      (μ := volume) measurableSet_Ioi
  rw [mellin_burnolHardyAverage honeMeas
      (mellinConvergent_burnolHardyAverage_phi
        w k z hw0 hw1 hz0 hz1 hwz) hz1,
    mellin_burnolHardyAverage_phi w k z hw0 hw1 hz0 hz1 hwz]
  ring

theorem mellinConvergent_burnolHardySquareDifference_phi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    MellinConvergent (burnolHardySquareDifference (burnolPhi w k)) z := by
  have hphi := mellinConvergent_burnolPhi w k z hz0 hz1 hwz
  have hone := mellinConvergent_burnolHardyAverage_phi
    w k z hw0 hw1 hz0 hz1 hwz
  have htwo := mellinConvergent_burnolHardyAverage_two_phi
    w k z hw0 hw1 hz0 hz1 hwz
  have hscaled : MellinConvergent
      (fun t : ℝ => 2 * burnolHardyAverage (burnolPhi w k) t) z := by
    simpa only [smul_eq_mul] using hone.const_smul (2 : ℂ)
  rw [MellinConvergent] at hphi hscaled htwo ⊢
  apply ((hphi.sub hscaled).add htwo).congr
  exact ae_of_all _ fun t => by
    simp only [Pi.add_apply, Pi.sub_apply, burnolHardySquareDifference,
      smul_eq_mul]
    ring

theorem mellin_burnolHardySquareDifference_phi
    (w : ℂ) (k : ℕ) (z : ℂ)
    (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hz0 : 0 < z.re) (hz1 : z.re < 1) (hwz : w.re < z.re) :
    mellin (burnolHardySquareDifference (burnolPhi w k)) z =
      (k.factorial : ℂ) * burnolVSpectral z / (z - w) ^ (k + 1) := by
  have hphi := mellinConvergent_burnolPhi w k z hz0 hz1 hwz
  have hone := mellinConvergent_burnolHardyAverage_phi
    w k z hw0 hw1 hz0 hz1 hwz
  have htwo := mellinConvergent_burnolHardyAverage_two_phi
    w k z hw0 hw1 hz0 hz1 hwz
  have hscaled : MellinConvergent
      (fun t : ℝ => 2 * burnolHardyAverage (burnolPhi w k) t) z := by
    simpa only [smul_eq_mul] using hone.const_smul (2 : ℂ)
  have hsub := hasMellin_sub hphi hscaled
  have hlinear := hasMellin_add hsub.1 htwo
  have hscaledValue :
      mellin (fun t : ℝ => 2 * burnolHardyAverage (burnolPhi w k) t) z =
        2 * mellin (burnolHardyAverage (burnolPhi w k)) z := by
    simpa only [smul_eq_mul] using (hasMellin_const_smul hone (2 : ℂ)).2
  have hvalue :
      mellin (burnolHardySquareDifference (burnolPhi w k)) z =
        mellin (burnolPhi w k) z -
          2 * mellin (burnolHardyAverage (burnolPhi w k)) z +
            mellin (burnolHardyAverage (burnolHardyAverage (burnolPhi w k))) z := by
    change mellin (fun t : ℝ =>
      burnolPhi w k t - 2 * burnolHardyAverage (burnolPhi w k) t +
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t) z = _
    calc
      mellin (fun t : ℝ =>
          burnolPhi w k t - 2 * burnolHardyAverage (burnolPhi w k) t +
            burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t) z =
        mellin (fun t : ℝ =>
          burnolPhi w k t - 2 * burnolHardyAverage (burnolPhi w k) t) z +
            mellin (burnolHardyAverage (burnolHardyAverage (burnolPhi w k))) z :=
        hlinear.2
      _ = mellin (burnolPhi w k) z -
          2 * mellin (burnolHardyAverage (burnolPhi w k)) z +
            mellin (burnolHardyAverage (burnolHardyAverage (burnolPhi w k))) z := by
        rw [hsub.2, hscaledValue]
  have hzden : 1 - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hzw : z - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at hre
    linarith
  rw [hvalue,
    mellin_burnolPhi_eq_USpectral_mul_pole w k z hz0 hz1 hwz,
    mellin_burnolHardyAverage_phi w k z hw0 hw1 hz0 hz1 hwz,
    mellin_burnolHardyAverage_two_phi w k z hw0 hw1 hz0 hz1 hwz,
    burnolVSpectral]
  field_simp [hzden, hzw]
  ring

theorem burnolPsi_mellinIntegrand_eq
    (w : ℂ) (k : ℕ) (z : ℂ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≠ 1) :
    (t : ℂ) ^ (z - 1) * burnolPsi w k t =
      (Ioo (0 : ℝ) 1).indicator
        (fun x : ℝ => (-(Real.log x : ℂ)) ^ k *
          (x : ℂ) ^ (-(1 - (z - w)))) t := by
  by_cases hlt : t < 1
  · have htMem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, hlt⟩
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [burnolPsi, Set.indicator_of_mem htMem, Set.indicator_of_mem htMem,
      one_div, Real.log_inv]
    push_cast
    have hpow : (t : ℂ) ^ (z - 1) * (t : ℂ) ^ (-w) =
        (t : ℂ) ^ (z - w - 1) := by
      rw [← Complex.cpow_add _ _ htC]
      congr 1
      ring
    calc
      (t : ℂ) ^ (z - 1) *
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-w)) =
        (-(Real.log t : ℂ)) ^ k *
          ((t : ℂ) ^ (z - 1) * (t : ℂ) ^ (-w)) := by ring
      _ = (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (z - w - 1) := by rw [hpow]
      _ = (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-(1 - (z - w))) := by
        congr 2
        ring
  · have hgt : 1 < t := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm ht1)
    have htNot : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_ge hgt.le) h.2
    rw [burnolPsi, Set.indicator_of_notMem htNot,
      Set.indicator_of_notMem htNot, mul_zero]

theorem mellinConvergent_burnolPsi
    (w : ℂ) (k : ℕ) (z : ℂ) (hwz : w.re < z.re) :
    MellinConvergent (burnolPsi w k) z := by
  let q : ℂ := 1 - (z - w)
  have hq1 : q.re < 1 := by
    dsimp only [q]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hbaseIoc := integrableOn_neg_log_pow_mul_cpow_neg_Ioc k hq1
  have hbaseIoo : IntegrableOn
      (fun t : ℝ => (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-q))
      (Ioo 0 1) := by
    rwa [← integrableOn_Ioc_iff_integrableOn_Ioo]
  have hindicator := hbaseIoo.integrable_indicator measurableSet_Ioo
  rw [MellinConvergent]
  apply hindicator.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with t ht ht1
  simp only [smul_eq_mul]
  exact (burnolPsi_mellinIntegrand_eq w k z ht ht1).symm

theorem mellin_burnolPsi
    (w : ℂ) (k : ℕ) (z : ℂ) (hwz : w.re < z.re) :
    mellin (burnolPsi w k) z =
      (k.factorial : ℂ) / (z - w) ^ (k + 1) := by
  let q : ℂ := 1 - (z - w)
  have hq1 : q.re < 1 := by
    dsimp only [q]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hmoment := integral_Ioc_neg_log_pow_mul_cpow_neg k hq1
  have hset : Ioi (0 : ℝ) ∩ Ioo 0 1 = Ioo 0 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    tauto
  rw [mellin]
  calc
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (z - 1) • burnolPsi w k t) =
        ∫ t : ℝ in Ioi 0,
          (Ioo (0 : ℝ) 1).indicator
            (fun x : ℝ => (-(Real.log x : ℂ)) ^ k *
              (x : ℂ) ^ (-q)) t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi,
        (volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with t ht ht1
      simp only [smul_eq_mul]
      exact burnolPsi_mellinIntegrand_eq w k z ht ht1
    _ = ∫ t : ℝ in Ioi (0 : ℝ) ∩ Ioo 0 1,
        (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-q) := by
      rw [setIntegral_indicator measurableSet_Ioo]
    _ = ∫ t : ℝ in Ioo 0 1,
        (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-q) := by rw [hset]
    _ = ∫ t : ℝ in Ioc 0 1,
        (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-q) := by
      rw [integral_Ioc_eq_integral_Ioo]
    _ = (k.factorial : ℂ) / (1 - q) ^ (k + 1) := hmoment
    _ = (k.factorial : ℂ) / (z - w) ^ (k + 1) := by
      dsimp only [q]
      congr 2
      ring

theorem burnolHardySquareDifference_phi_memLp
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    MemLp (burnolHardySquareDifference (burnolPhi w k)) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  let H : ℝ → ℂ := burnolHardySquareDifference (burnolPhi w k)
  let Csmall : ℝ := burnolVMainDerivCoeffBound w k
  let Bsmall : ℝ := 4 * burnolPhiSeriesBound k
  let Clarge : ℝ := burnolPhiHardySquareLargeCoeff w k
  have hw1 : w.re < 1 := hwHalf.trans (by norm_num)
  have hHmeas : AEStronglyMeasurable H (volume.restrict (Ioi (0 : ℝ))) :=
    aestronglyMeasurable_burnolHardySquareDifference_phi_Ioi w k hw0 hw1
  rw [memLp_two_iff_integrable_sq_norm hHmeas]
  change IntegrableOn (fun t : ℝ => ‖H t‖ ^ 2) (Ioi (0 : ℝ))
  have hsmallWeight := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    (2 * k) (a := -2 * w.re) (by linarith)
  have hsmallMajor : IntegrableOn
      (fun t : ℝ =>
        2 * Csmall ^ 2 *
            ((1 + |Real.log t|) ^ (2 * k) * t ^ (-2 * w.re)) +
          2 * Bsmall ^ 2)
      (Ioc (0 : ℝ) 1) := by
    have hweight := hsmallWeight.const_mul (2 * Csmall ^ 2)
    have hconst : IntegrableOn (fun _ : ℝ => 2 * Bsmall ^ 2)
        (Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
    exact hweight.add hconst
  have hsmall : IntegrableOn (fun t : ℝ => ‖H t‖ ^ 2)
      (Ioc (0 : ℝ) 1) := by
    apply Integrable.mono' hsmallMajor
      ((hHmeas.mono_set Ioc_subset_Ioi_self).norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
    have hbound := norm_burnolHardySquareDifference_phi_le_small
      w k hw0 hw1 ht.1 ht.2
    let A : ℝ := Csmall * (1 + |Real.log t|) ^ k * t ^ (-w.re)
    have hA : 0 ≤ A := by
      dsimp only [A, Csmall]
      exact mul_nonneg
        (mul_nonneg (burnolVMainDerivCoeffBound_nonneg w k)
          (pow_nonneg (by positivity) _))
        (Real.rpow_nonneg ht.1.le _)
    have hB : 0 ≤ Bsmall := by
      dsimp only [Bsmall]
      exact mul_nonneg (by norm_num) (burnolPhiSeriesBound_nonneg k)
    have hlogPow : ((1 + |Real.log t|) ^ k) ^ 2 =
        (1 + |Real.log t|) ^ (2 * k) := by
      rw [← pow_mul]
      congr 1
      omega
    have htPow : (t ^ (-w.re)) ^ 2 = t ^ (-2 * w.re) := by
      rw [pow_two, ← Real.rpow_add ht.1]
      congr 1
      ring
    have hASq : A ^ 2 = Csmall ^ 2 *
        ((1 + |Real.log t|) ^ (2 * k) * t ^ (-2 * w.re)) := by
      dsimp only [A]
      rw [mul_pow, mul_pow, hlogPow, htPow]
      ring
    have hsquare : (A + Bsmall) ^ 2 ≤ 2 * A ^ 2 + 2 * Bsmall ^ 2 := by
      nlinarith [sq_nonneg (A - Bsmall)]
    calc
      ‖H t‖ ^ 2 ≤ (A + Bsmall) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (by
          simpa only [H, A, Csmall, Bsmall, mul_assoc] using hbound) 2
      _ ≤ 2 * A ^ 2 + 2 * Bsmall ^ 2 := hsquare
      _ = 2 * Csmall ^ 2 *
          ((1 + |Real.log t|) ^ (2 * k) * t ^ (-2 * w.re)) +
            2 * Bsmall ^ 2 := by rw [hASq]; ring
  have hlargeMajor : IntegrableOn
      (fun t : ℝ => 8 * Clarge ^ 2 *
        (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)))
      (Ioi (1 : ℝ)) :=
    integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * Clarge ^ 2)
  have hlarge : IntegrableOn (fun t : ℝ => ‖H t‖ ^ 2)
      (Ioi (1 : ℝ)) := by
    apply Integrable.mono' hlargeMajor
      ((hHmeas.mono_set (Ioi_subset_Ioi zero_le_one)).norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hbound := norm_burnolHardySquareDifference_phi_le_large
      w k hw0 hw1 ht1
    have hboundSq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hadd : (1 + Real.log t) ^ 4 ≤
        8 * (1 + (Real.log t) ^ 4) := by
      have h := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hlog0 4
      norm_num at h
      exact h
    have hinvSq : t⁻¹ ^ 2 = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht0.le]
      exact (inv_pow t 2).trans
        (congrArg Inv.inv (Real.rpow_natCast t 2).symm)
    calc
      ‖H t‖ ^ 2 ≤ (Clarge * (1 + Real.log t) ^ 2 / t) ^ 2 := by
        simpa only [H, Clarge] using hboundSq
      _ = Clarge ^ 2 * (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, mul_pow, mul_pow, hinvSq]
        ring
      _ ≤ Clarge ^ 2 * (8 * (1 + (Real.log t) ^ 4)) *
          t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hadd (sq_nonneg Clarge))
          (Real.rpow_nonneg ht0.le _)
      _ = 8 * Clarge ^ 2 *
          (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)) := by ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hsmall.union hlarge

/-- The uncut interior Hardy-square representative as an `L2` vector. -/
def burnolHardySquarePhiL2 (w : ℂ) (k : ℕ) : positiveHalfLineComplexL2 :=
  if hw : 0 < w.re ∧ w.re < 1 / 2 then
    (burnolHardySquareDifference_phi_memLp w k hw.1 hw.2).toLp
      (burnolHardySquareDifference (burnolPhi w k))
  else 0

theorem burnolHardySquarePhiL2_coeFn
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    burnolHardySquarePhiL2 w k
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        burnolHardySquareDifference (burnolPhi w k) := by
  rw [burnolHardySquarePhiL2, dif_pos ⟨hw0, hwHalf⟩]
  exact MemLp.coeFn_toLp (burnolHardySquareDifference_phi_memLp w k hw0 hwHalf)

def burnolHardySquarePhiWeightedLog (w : ℂ) (k : ℕ) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) *
    burnolHardySquareDifference (burnolPhi w k) (Real.exp (-u))

theorem burnolHardySquarePhiWeightedLog_ae_weightedLogForwardFun
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    burnolHardySquarePhiWeightedLog w k =ᵐ[volume]
      weightedLogForwardFun (burnolHardySquarePhiL2 w k) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (burnolHardySquarePhiL2_coeFn w k hw0 hwHalf)
  filter_upwards [hsource] with u hu
  simp only [burnolHardySquarePhiWeightedLog, weightedLogForwardFun, expNeg]
  have hpoint : burnolHardySquarePhiL2 w k (Real.exp (-u)) =
      burnolHardySquareDifference (burnolPhi w k) (Real.exp (-u)) := by
    simpa only [Function.comp_apply, expNeg] using hu
  rw [← hpoint]

theorem burnolHardySquarePhiWeightedLog_memLp
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    MemLp (burnolHardySquarePhiWeightedLog w k) (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp (burnolHardySquarePhiL2 w k)).ae_eq
    (burnolHardySquarePhiWeightedLog_ae_weightedLogForwardFun
      w k hw0 hwHalf).symm

theorem burnolHardySquarePhiWeightedLog_toLp
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    (burnolHardySquarePhiWeightedLog_memLp w k hw0 hwHalf).toLp
        (burnolHardySquarePhiWeightedLog w k) =
      weightedLogPullback (burnolHardySquarePhiL2 w k) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (burnolHardySquarePhiWeightedLog_memLp w k hw0 hwHalf)
    (weightedLogForwardFun_memLp (burnolHardySquarePhiL2 w k))
    (burnolHardySquarePhiWeightedLog_ae_weightedLogForwardFun
      w k hw0 hwHalf)

theorem burnolHardySquarePhiWeightedLog_integrable
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    Integrable (burnolHardySquarePhiWeightedLog w k) := by
  have hM := mellinConvergent_burnolHardySquareDifference_phi
    w k (1 / 2 : ℂ) hw0 (hwHalf.trans (by norm_num))
      (by norm_num) (by norm_num) (by simpa using hwHalf)
  exact integrable_weightedLog_of_mellinConvergent hM

theorem burnolPsiWeightedLog_eq_weightedLog
    (w : ℂ) (k : ℕ) (u : ℝ) :
    burnolPsiWeightedLog w k u =
      (Real.exp (-u / 2) : ℂ) * burnolPsi w k (Real.exp (-u)) := by
  have hsource := weightedLogInverse_burnolPsi_pointwise
    w k (t := Real.exp (-u)) (Real.exp_pos _)
  simp only [Real.log_exp, neg_neg] at hsource
  have hfactor : (Real.exp (-u / 2) : ℂ) *
      (((Real.exp (-u)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) = 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    push_cast
    rw [← Complex.exp_add]
    rw [show (-u : ℂ) / 2 + (-u : ℂ) * (-1 / 2) = 0 by ring,
      Complex.exp_zero]
  calc
    burnolPsiWeightedLog w k u =
        1 * burnolPsiWeightedLog w k u := by rw [one_mul]
    _ = (Real.exp (-u / 2) : ℂ) *
        ((((Real.exp (-u)) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
          burnolPsiWeightedLog w k u) := by rw [← mul_assoc, hfactor, one_mul]
    _ = (Real.exp (-u / 2) : ℂ) * burnolPsi w k (Real.exp (-u)) := by
      rw [hsource]

theorem burnolPsiWeightedLog_integrable
    (w : ℂ) (k : ℕ) (hwHalf : w.re < 1 / 2) :
    Integrable (burnolPsiWeightedLog w k) := by
  have hM := mellinConvergent_burnolPsi w k (1 / 2 : ℂ)
    (by simpa using hwHalf)
  have hweighted := integrable_weightedLog_of_mellinConvergent hM
  exact hweighted.congr (ae_of_all volume fun u =>
    (burnolPsiWeightedLog_eq_weightedLog w k u).symm)

def burnolPsiTransform (w : ℂ) (k : ℕ) (xi : ℝ) : ℂ :=
  (k.factorial : ℂ) /
    (burnolCriticalLineAtFrequency xi - w) ^ (k + 1)

def burnolHardySquarePhiTransform (w : ℂ) (k : ℕ) (xi : ℝ) : ℂ :=
  burnolVSpectral (burnolCriticalLineAtFrequency xi) *
    burnolPsiTransform w k xi

theorem fourier_burnolPsiWeightedLog
    (w : ℂ) (k : ℕ) (hwHalf : w.re < 1 / 2) (xi : ℝ) :
    𝓕 (burnolPsiWeightedLog w k) xi = burnolPsiTransform w k xi := by
  let tau : ℝ := 2 * Real.pi * xi
  let s : ℂ := burnolCriticalLineAtFrequency xi
  have hs : (1 / 2 : ℂ) + tau * Complex.I = s := by
    dsimp only [tau, s, burnolCriticalLineAtFrequency]
  have hFourier := mellin_criticalLine_eq_fourier (burnolPsi w k) tau
  rw [hs, mellin_burnolPsi w k s (by
    dsimp only [s, burnolCriticalLineAtFrequency]
    norm_num
    linarith)] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  calc
    𝓕 (burnolPsiWeightedLog w k) xi =
        𝓕 (fun u : ℝ =>
          (Real.exp (-u / 2) : ℂ) * burnolPsi w k (Real.exp (-u))) xi := by
      rw [funext (burnolPsiWeightedLog_eq_weightedLog w k)]
    _ = burnolPsiTransform w k xi := by
      simpa only [burnolPsiTransform, s] using hFourier.symm

theorem fourier_burnolHardySquarePhiWeightedLog
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) (xi : ℝ) :
    𝓕 (burnolHardySquarePhiWeightedLog w k) xi =
      burnolHardySquarePhiTransform w k xi := by
  let tau : ℝ := 2 * Real.pi * xi
  let s : ℂ := burnolCriticalLineAtFrequency xi
  have hs : (1 / 2 : ℂ) + tau * Complex.I = s := by
    dsimp only [tau, s, burnolCriticalLineAtFrequency]
  have hs0 : 0 < s.re := by
    dsimp only [s, burnolCriticalLineAtFrequency]
    norm_num
  have hs1 : s.re < 1 := by
    dsimp only [s, burnolCriticalLineAtFrequency]
    norm_num
  have hws : w.re < s.re := by
    dsimp only [s, burnolCriticalLineAtFrequency]
    norm_num
    linarith
  have hFourier := mellin_criticalLine_eq_fourier
    (burnolHardySquareDifference (burnolPhi w k)) tau
  rw [hs, mellin_burnolHardySquareDifference_phi
    w k s hw0 (hwHalf.trans (by norm_num)) hs0 hs1 hws] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : ℝ =>
    (Real.exp (-u / 2) : ℂ) *
      burnolHardySquareDifference (burnolPhi w k) (Real.exp (-u))) xi = _
  rw [← hFourier]
  dsimp only [burnolHardySquarePhiTransform, burnolPsiTransform, s]
  ring

theorem integrable_inv_sq_add_affine
    {a c : ℝ} (ha : 0 < a) (hc : c ≠ 0) (b : ℝ) :
    Integrable (fun x : ℝ => (a ^ 2 + (c * x - b) ^ 2)⁻¹) := by
  let g : ℝ → ℝ := fun y => (1 + y ^ 2)⁻¹
  have hg : Integrable g := integrable_inv_one_add_sq
  have hshift : Integrable (fun y : ℝ => g (-b / a + y)) :=
    hg.comp_add_left (-b / a)
  have hscale : Integrable (fun x : ℝ => g (-b / a + (c / a) * x)) :=
    hshift.comp_mul_left' (div_ne_zero hc ha.ne')
  have hmajor := hscale.const_mul (a ^ 2)⁻¹
  apply hmajor.congr
  exact ae_of_all volume fun x => by
    dsimp only [g]
    field_simp [ha.ne', hc]
    ring

theorem burnolPsiTransform_memLp
    (w : ℂ) (k : ℕ) (hwHalf : w.re < 1 / 2) :
    MemLp (burnolPsiTransform w k) (2 : ℝ≥0∞) volume := by
  let a : ℝ := 1 / 2 - w.re
  let b : ℝ := w.im
  let c : ℝ := 2 * Real.pi
  let F : ℝ := k.factorial
  let D : ℝ := F ^ 2 / a ^ (2 * k)
  have ha : 0 < a := by dsimp only [a]; linarith
  have hc : c ≠ 0 := by dsimp only [c]; positivity
  have hbase := integrable_inv_sq_add_affine ha hc b
  have hmajor : Integrable
      (fun xi : ℝ => D * (a ^ 2 + (c * xi - b) ^ 2)⁻¹) :=
    hbase.const_mul D
  have hmeas : AEStronglyMeasurable (burnolPsiTransform w k) volume := by
    have hden : ∀ xi : ℝ,
        (burnolCriticalLineAtFrequency xi - w) ^ (k + 1) ≠ 0 := by
      intro xi
      apply pow_ne_zero
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, burnolCriticalLineAtFrequency] at hre
      norm_num at hre
      linarith
    exact (continuous_const.div
      ((continuous_burnolCriticalLineAtFrequency.sub continuous_const).pow (k + 1))
      hden).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  apply Integrable.mono' hmajor (hmeas.norm.pow 2)
  exact ae_of_all volume fun xi => by
    change ‖‖burnolPsiTransform w k xi‖ ^ 2‖ ≤
      D * (a ^ 2 + (c * xi - b) ^ 2)⁻¹
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    let s : ℂ := burnolCriticalLineAtFrequency xi
    let r : ℝ := ‖s - w‖
    have hsre : (s - w).re = a := by
      dsimp only [s, a, burnolCriticalLineAtFrequency]
      norm_num
    have hsim : (s - w).im = c * xi - b := by
      dsimp only [s, c, b, burnolCriticalLineAtFrequency]
      simp
    have hsne : s - w ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre] at hre
      simp only [Complex.zero_re] at hre
      linarith
    have hrpos : 0 < r := norm_pos_iff.mpr hsne
    have har : a ≤ r := by
      have h := Complex.abs_re_le_norm (s - w)
      rw [hsre, abs_of_pos ha] at h
      exact h
    have hpow : a ^ (2 * k) ≤ r ^ (2 * k) :=
      pow_le_pow_left₀ ha.le har (2 * k)
    have hden : a ^ (2 * k) * r ^ 2 ≤ r ^ (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      exact mul_le_mul_of_nonneg_right hpow (sq_nonneg r)
    have hrsq : r ^ 2 = a ^ 2 + (c * xi - b) ^ 2 := by
      dsimp only [r]
      rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]
      ring
    have hnorm : ‖burnolPsiTransform w k xi‖ ^ 2 =
        F ^ 2 / r ^ (2 * (k + 1)) := by
      rw [burnolPsiTransform, norm_div, norm_pow, norm_natCast]
      dsimp only [s, r, F]
      rw [div_pow]
      congr 1
      rw [← pow_mul]
      congr 1
      omega
    rw [hnorm]
    calc
      F ^ 2 / r ^ (2 * (k + 1)) ≤
          F ^ 2 / (a ^ (2 * k) * r ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg F)
          (mul_pos (pow_pos ha _) (sq_pos_of_pos hrpos)) hden
      _ = D * (a ^ 2 + (c * xi - b) ^ 2)⁻¹ := by
        dsimp only [D]
        rw [← hrsq]
        field_simp [ha.ne', hrpos.ne']

theorem ae_burnolHardySquarePhiTransform_eq_phase_mul
    (w : ℂ) (k : ℕ) :
    burnolHardySquarePhiTransform w k =ᵐ[volume]
      fun xi : ℝ => burnolAPhaseMultiplier xi * burnolPsiTransform w k xi := by
  filter_upwards [ae_burnolVSpectral_critical_eq_APhaseMultiplier] with xi hphase
  rw [burnolHardySquarePhiTransform, hphase]

theorem burnolHardySquarePhiTransform_memLp
    (w : ℂ) (k : ℕ) (hwHalf : w.re < 1 / 2) :
    MemLp (burnolHardySquarePhiTransform w k) (2 : ℝ≥0∞) volume := by
  have hproduct : MemLp
      (fun xi : ℝ => burnolAPhaseMultiplier xi • burnolPsiTransform w k xi)
      (2 : ℝ≥0∞) volume :=
    (burnolPsiTransform_memLp w k hwHalf).smul
      burnolAPhaseMultiplier_memLp_top
  exact hproduct.ae_eq
    (ae_burnolHardySquarePhiTransform_eq_phase_mul w k).symm

theorem baezDuarteFourierMellinL2_burnolPsiL2
    (w : ℂ) (k : ℕ) (hwHalf : w.re < 1 / 2) :
    baezDuarteFourierMellinL2 (burnolPsiL2 w k) =
      (burnolPsiTransform_memLp w k hwHalf).toLp (burnolPsiTransform w k) := by
  have hFourier2 : MemLp (𝓕 (burnolPsiWeightedLog w k))
      (2 : ℝ≥0∞) volume :=
    (burnolPsiTransform_memLp w k hwHalf).ae_eq
      (ae_of_all volume fun xi => (fourier_burnolPsiWeightedLog w k hwHalf xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    (burnolPsiWeightedLog_integrable w k hwHalf)
    (burnolPsiWeightedLog_memLp w k hwHalf) hFourier2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply,
    burnolPsiL2, weightedLogPullback.apply_symm_apply,
    burnolPsiWeightedLogL2, dif_pos hwHalf]
  calc
    _ = hFourier2.toLp (𝓕 (burnolPsiWeightedLog w k)) := hcompat
    _ = (burnolPsiTransform_memLp w k hwHalf).toLp
        (burnolPsiTransform w k) :=
      MemLp.toLp_congr hFourier2 (burnolPsiTransform_memLp w k hwHalf)
        (ae_of_all volume fun xi => fourier_burnolPsiWeightedLog w k hwHalf xi)

theorem baezDuarteFourierMellinL2_burnolHardySquarePhiL2
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    baezDuarteFourierMellinL2 (burnolHardySquarePhiL2 w k) =
      (burnolHardySquarePhiTransform_memLp w k hwHalf).toLp
        (burnolHardySquarePhiTransform w k) := by
  have hFourier2 : MemLp (𝓕 (burnolHardySquarePhiWeightedLog w k))
      (2 : ℝ≥0∞) volume :=
    (burnolHardySquarePhiTransform_memLp w k hwHalf).ae_eq
      (ae_of_all volume fun xi =>
        (fourier_burnolHardySquarePhiWeightedLog w k hw0 hwHalf xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    (burnolHardySquarePhiWeightedLog_integrable w k hw0 hwHalf)
    (burnolHardySquarePhiWeightedLog_memLp w k hw0 hwHalf) hFourier2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← burnolHardySquarePhiWeightedLog_toLp w k hw0 hwHalf]
  calc
    _ = hFourier2.toLp (𝓕 (burnolHardySquarePhiWeightedLog w k)) := hcompat
    _ = (burnolHardySquarePhiTransform_memLp w k hwHalf).toLp
        (burnolHardySquarePhiTransform w k) :=
      MemLp.toLp_congr hFourier2
        (burnolHardySquarePhiTransform_memLp w k hwHalf)
        (ae_of_all volume fun xi =>
          fourier_burnolHardySquarePhiWeightedLog w k hw0 hwHalf xi)

theorem burnolAPhaseFrequencyL2_burnolPsiTransform
    (w : ℂ) (k : ℕ) (hwHalf : w.re < 1 / 2) :
    burnolAPhaseFrequencyL2
        ((burnolPsiTransform_memLp w k hwHalf).toLp (burnolPsiTransform w k)) =
      (burnolHardySquarePhiTransform_memLp w k hwHalf).toLp
        (burnolHardySquarePhiTransform w k) := by
  rw [burnolAPhaseFrequencyL2_apply]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolAPhaseMultiplierLInf
      ((burnolPsiTransform_memLp w k hwHalf).toLp (burnolPsiTransform w k)),
    burnolAPhaseMultiplierLInf_coeFn,
    MemLp.coeFn_toLp (burnolPsiTransform_memLp w k hwHalf),
    MemLp.coeFn_toLp (burnolHardySquarePhiTransform_memLp w k hwHalf),
    ae_burnolHardySquarePhiTransform_eq_phase_mul w k] with
      xi hout hphase hpsi hhardy hrelation
  rw [hout]
  change burnolAPhaseMultiplierLInf xi *
      ((burnolPsiTransform_memLp w k hwHalf).toLp
        (burnolPsiTransform w k)) xi =
    ((burnolHardySquarePhiTransform_memLp w k hwHalf).toLp
      (burnolHardySquarePhiTransform w k)) xi
  rw [hphase, hpsi, hhardy, hrelation]

theorem burnolAPhaseL2_burnolPsiL2_eq_hardySquare
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    burnolAPhaseL2 (burnolPsiL2 w k) = burnolHardySquarePhiL2 w k := by
  apply baezDuarteFourierMellinL2.injective
  rw [baezDuarteFourierMellinL2_burnolAPhaseL2,
    baezDuarteFourierMellinL2_burnolPsiL2 w k hwHalf,
    burnolAPhaseFrequencyL2_burnolPsiTransform w k hwHalf,
    baezDuarteFourierMellinL2_burnolHardySquarePhiL2 w k hw0 hwHalf]

theorem burnolPreY_eq_hardySquare_cutoff
    (lambda : ℝ) (w : ℂ) (k : ℕ)
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    burnolPreY lambda w k =
      burnolAPhaseL2.symm
        (burnolCutoffL2 lambda (burnolHardySquarePhiL2 w k)) := by
  rw [burnolPreY, burnolAPhaseL2_burnolPsiL2_eq_hardySquare w k hw0 hwHalf]

theorem burnolAPhaseL2_burnolPreY_eq_hardySquare_cutoff
    (lambda : ℝ) (w : ℂ) (k : ℕ)
    (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    burnolAPhaseL2 (burnolPreY lambda w k) =
      burnolCutoffL2 lambda (burnolHardySquarePhiL2 w k) := by
  rw [burnolPreY, burnolAPhaseL2.apply_symm_apply,
    burnolAPhaseL2_burnolPsiL2_eq_hardySquare w k hw0 hwHalf]

theorem continuousOn_burnolPhiSeriesCoreTerm_parameter
    (k j : ℕ) (t : ℝ) :
    ContinuousOn (fun w : ℂ => burnolPhiSeriesCoreTerm w k t j)
      {w : ℂ | 0 < w.re} := by
  intro w hw
  change 0 < w.re at hw
  have hden : w + (2 * j : ℕ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at hre
    have hj0 : (0 : ℝ) ≤ (2 * j : ℕ) := by positivity
    linarith
  have hdenPow : (w + (2 * j : ℕ)) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ hden
  apply ContinuousAt.continuousWithinAt
  unfold burnolPhiSeriesCoreTerm
  fun_prop

theorem continuousOn_burnolPhiSeriesRemainder_parameter
    (k : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    ContinuousOn (fun w : ℂ => burnolPhiSeriesRemainder w k t)
      {w : ℂ | 0 < w.re} := by
  have hsum : ContinuousOn
      (fun w : ℂ => ∑' j : ℕ, burnolPhiSeriesCoreTerm w k t j)
      {w : ℂ | 0 < w.re} :=
    continuousOn_tsum
      (fun j => continuousOn_burnolPhiSeriesCoreTerm_parameter k j t)
      summable_burnolPhiSeriesMajor
      (fun j w hw =>
        norm_burnolPhiSeriesCoreTerm_le_major w hw.le ht j)
  unfold burnolPhiSeriesRemainder
  exact continuousOn_const.mul hsum

theorem continuousOn_burnolHardyAverage_phiSeriesRemainder_parameter
    (k : ℕ) {t : ℝ} (ht1 : t ≤ 1) :
    ContinuousOn
      (fun w : ℂ => burnolHardyAverage (burnolPhiSeriesRemainder w k) t)
      {w : ℂ | 0 < w.re} := by
  have hprimitive : ContinuousOn
      (fun w : ℂ => ∫ u : ℝ in Ioc 0 t, burnolPhiSeriesRemainder w k u)
      {w : ℂ | 0 < w.re} := by
    apply continuousOn_of_dominated
      (bound := fun _ : ℝ => burnolPhiSeriesBound k)
    · intro w hw
      exact (measurable_burnolPhiSeriesRemainder w k).aestronglyMeasurable
    · intro w hw
      change 0 < w.re at hw
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact norm_burnolPhiSeriesRemainder_le w hw.le (by
        rw [abs_of_pos hu.1]
        exact hu.2.trans ht1)
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact continuousOn_burnolPhiSeriesRemainder_parameter k (by
        rw [abs_of_pos hu.1]
        exact hu.2.trans ht1)
  unfold burnolHardyAverage
  exact continuousOn_const.mul hprimitive

theorem continuousOn_burnolHardyAverage_two_phiSeriesRemainder_parameter
    (k : ℕ) {t : ℝ} (ht1 : t ≤ 1) :
    ContinuousOn
      (fun w : ℂ =>
        burnolHardyAverage
          (burnolHardyAverage (burnolPhiSeriesRemainder w k)) t)
      {w : ℂ | 0 < w.re} := by
  have hprimitive : ContinuousOn
      (fun w : ℂ => ∫ u : ℝ in Ioc 0 t,
        burnolHardyAverage (burnolPhiSeriesRemainder w k) u)
      {w : ℂ | 0 < w.re} := by
    apply continuousOn_of_dominated
      (bound := fun _ : ℝ => burnolPhiSeriesBound k)
    · intro w hw
      change 0 < w.re at hw
      exact ((continuousOn_burnolHardyAverage_phiSeriesRemainder
        w k hw.le).mono fun u hu => ⟨hu.1, hu.2.trans ht1⟩).aestronglyMeasurable
          measurableSet_Ioc
    · intro w hw
      change 0 < w.re at hw
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact norm_burnolHardyAverage_phiSeriesRemainder_le
        w k hw.le hu.1 (hu.2.trans ht1)
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact continuousOn_burnolHardyAverage_phiSeriesRemainder_parameter
        k (hu.2.trans ht1)
  unfold burnolHardyAverage
  exact continuousOn_const.mul hprimitive

theorem continuousOn_burnolPhiHardySeriesRemainder_parameter
    (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ContinuousOn (fun w : ℂ => burnolPhiHardySeriesRemainder w k t)
      {w : ℂ | 0 < w.re} := by
  unfold burnolPhiHardySeriesRemainder
  exact ((continuousOn_burnolPhiSeriesRemainder_parameter k
      (by rw [abs_of_pos ht0]; exact ht1)).sub
    (continuousOn_const.mul
      (continuousOn_burnolHardyAverage_phiSeriesRemainder_parameter
        k ht1))).add
    (continuousOn_burnolHardyAverage_two_phiSeriesRemainder_parameter
      k ht1)

theorem continuousOn_iteratedDeriv_burnolPhiHardyGammaMain_parameter
    (k : ℕ) {t : ℝ} (ht0 : 0 < t) :
    ContinuousOn
      (fun w : ℂ => iteratedDeriv k (burnolPhiHardyGammaMain t) w)
      burnolOpenCriticalStrip := by
  let F : ℂ → ℂ := fun w => burnolVSpectral w * (t : ℂ) ^ (-w)
  have hcpow : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun w : ℂ => (t : ℂ) ^ (-w)) := by
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [show (fun w : ℂ => (t : ℂ) ^ (-w)) =
        fun w : ℂ => Complex.exp (-(Real.log t : ℂ) * w) by
      funext w
      rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]
      congr 1
      ring]
    fun_prop
  have hF : ContDiffOn ℂ (⊤ : WithTop ℕ∞) F burnolOpenCriticalStrip := by
    dsimp only [F]
    exact contDiffOn_burnolVSpectral.mul hcpow.contDiffOn
  have hderivWithin : ContinuousOn
      (iteratedDerivWithin k F burnolOpenCriticalStrip)
      burnolOpenCriticalStrip :=
    hF.continuousOn_iteratedDerivWithin (by simp)
      isOpen_burnolOpenCriticalStrip.uniqueDiffOn
  have hderiv : ContinuousOn (iteratedDeriv k F)
      burnolOpenCriticalStrip :=
    hderivWithin.congr
      (iteratedDerivWithin_of_isOpen isOpen_burnolOpenCriticalStrip).symm
  apply hderiv.congr
  intro w hw
  simpa only [F] using
    (iteratedDeriv_burnolPhiHardyGammaMain_eq_V_cpow
      k ht0 hw.1 hw.2)

theorem continuousOn_burnolHardySquareDifference_phi_parameter_small
    (k : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ContinuousOn
      (fun w : ℂ => burnolHardySquareDifference (burnolPhi w k) t)
      burnolOpenCriticalStrip := by
  have hmain :=
    continuousOn_iteratedDeriv_burnolPhiHardyGammaMain_parameter k ht0
  have hremainder : ContinuousOn
      (fun w : ℂ => burnolPhiHardySeriesRemainder w k t)
      burnolOpenCriticalStrip :=
    (continuousOn_burnolPhiHardySeriesRemainder_parameter
      k ht0 ht1).mono fun w hw => hw.1
  apply (hmain.add hremainder).congr
  intro w hw
  exact burnolHardySquareDifference_phi_eq_gammaMain
    w k hw.1 hw.2 ht0 ht1

theorem continuousAt_burnolPhi_parameter
    (s : ℂ) (k : ℕ) (t : ℝ) (hs1 : s.re < 1) :
    ContinuousAt (fun w : ℂ => burnolPhi w k t) s := by
  let b : ℝ := (1 + s.re) / 2
  let N : ℝ := ‖s‖ + 1
  let B : ℝ → ℝ := fun u =>
    (k : ℝ) * (Real.log u) ^ (k - 1) * u ^ (b - 2) +
      N * (Real.log u) ^ k * u ^ (b - 2)
  have hsb : s.re < b := by
    dsimp only [b]
    linarith
  have hb1 : b < 1 := by
    dsimp only [b]
    linarith
  have hsN : ‖s‖ < N := by
    dsimp only [N]
    linarith
  have hre : ∀ᶠ w : ℂ in 𝓝 s, w.re < b :=
    (Complex.continuous_re.isOpen_preimage (Iio b) isOpen_Iio).mem_nhds hsb
  have hnorm : ∀ᶠ w : ℂ in 𝓝 s, ‖w‖ < N :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hsN
  have hB_integrable : Integrable B (volume.restrict (Ioi (1 : ℝ))) := by
    have hfirst :=
      (integrableOn_log_pow_mul_rpow_Ioi_one (k - 1) (b - 2) (by linarith)).const_mul
        (k : ℝ)
    have hsecond :=
      (integrableOn_log_pow_mul_rpow_Ioi_one k (b - 2) (by linarith)).const_mul N
    apply (hfirst.add hsecond).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp only [B]
    simp only [Pi.add_apply]
    ring
  have hintegral : ContinuousAt
      (fun w : ℂ => ∫ u : ℝ in Ioi 1, burnolPhiTailIntegrand w k t u) s := by
    apply continuousAt_of_dominated (bound := B)
    · exact Eventually.of_forall fun w =>
        (measurable_burnolPhiTailIntegrand w k t).aestronglyMeasurable
    · filter_upwards [hre, hnorm] with w hwre hwnorm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : 1 ≤ u := hu.le
      have hu0 : 0 < u := one_pos.trans hu
      have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
      have hfactor := norm_burnolPhiLogFactor_le w k hu1
      have hfactor' : ‖burnolPhiLogFactor w k u‖ ≤
          (k : ℝ) * (Real.log u) ^ (k - 1) +
            N * (Real.log u) ^ k := by
        exact hfactor.trans <| by
          gcongr
      have hpower : u ^ (w.re - 2) ≤ u ^ (b - 2) :=
        Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
      have htail := norm_burnolPhiTailIntegrand_le_major w k t hu0
      calc
        ‖burnolPhiTailIntegrand w k t u‖ ≤
            ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) := htail
        _ ≤ ((k : ℝ) * (Real.log u) ^ (k - 1) +
              N * (Real.log u) ^ k) * u ^ (b - 2) := by
          exact mul_le_mul hfactor' hpower
            (Real.rpow_nonneg hu0.le _) <|
              add_nonneg
                (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog0 _))
                (mul_nonneg (by dsimp only [N]; positivity) (pow_nonneg hlog0 _))
        _ = B u := by
          dsimp only [B]
          ring
    · exact hB_integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := one_pos.trans hu
      have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
      have hfactor : ContinuousAt
          (fun w : ℂ => (k : ℂ) * (Real.log u : ℂ) ^ (k - 1) +
            w * (Real.log u : ℂ) ^ k) s := by
        fun_prop
      have hcpow : ContinuousAt (fun w : ℂ => (u : ℂ) ^ (w - 2)) s := by
        rw [show (fun w : ℂ => (u : ℂ) ^ (w - 2)) =
            fun w : ℂ => Complex.exp ((Real.log u : ℂ) * (w - 2)) by
          funext w
          rw [Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu0.le]]
        fun_prop
      unfold burnolPhiTailIntegrand burnolPhiLogFactor
      exact (hfactor.mul hcpow).mul continuousAt_const
  unfold burnolPhi
  exact continuousAt_const.add (continuousAt_const.mul hintegral)

theorem continuousOn_iteratedDeriv_of_contDiffOn_burnolOpenCriticalStrip
    (F : ℂ → ℂ)
    (hF : ContDiffOn ℂ (⊤ : WithTop ℕ∞) F burnolOpenCriticalStrip)
    (k : ℕ) :
    ContinuousOn (iteratedDeriv k F) burnolOpenCriticalStrip := by
  have hwithin := hF.continuousOn_iteratedDerivWithin (m := k) (by simp)
    isOpen_burnolOpenCriticalStrip.uniqueDiffOn
  exact hwithin.congr
    (iteratedDerivWithin_of_isOpen isOpen_burnolOpenCriticalStrip).symm

theorem continuousOn_burnolHardyAverage_phi_parameter_one (k : ℕ) :
    ContinuousOn
      (fun w : ℂ => burnolHardyAverage (burnolPhi w k) 1)
      burnolOpenCriticalStrip := by
  let F : ℂ → ℂ := fun z => (1 - z)⁻¹ * burnolUSpectral z
  have hinv : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun z : ℂ => (1 - z)⁻¹) burnolOpenCriticalStrip := by
    intro z hz
    have hden : 1 - z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
      linarith [hz.2]
    fun_prop
  have hF : ContDiffOn ℂ (⊤ : WithTop ℕ∞) F burnolOpenCriticalStrip := by
    dsimp only [F]
    exact hinv.mul contDiffOn_burnolUSpectral
  have hmain :=
    continuousOn_iteratedDeriv_of_contDiffOn_burnolOpenCriticalStrip F hF k
  have hremainder : ContinuousOn
      (fun w : ℂ =>
        burnolHardyAverage (burnolPhiSeriesRemainder w k) 1)
      burnolOpenCriticalStrip :=
    (continuousOn_burnolHardyAverage_phiSeriesRemainder_parameter
      k le_rfl).mono fun w hw => hw.1
  have hgamma :
      (fun z : ℂ => (1 - z)⁻¹ * burnolPhiGammaMain 1 z) = F := by
    funext z
    rw [burnolPhiGammaMain_eq_U_mul_cpow z one_pos]
    simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, F]
  apply (hmain.add hremainder).congr
  intro w hw
  change burnolHardyAverage (burnolPhi w k) 1 =
    iteratedDeriv k F w +
      burnolHardyAverage (burnolPhiSeriesRemainder w k) 1
  rw [burnolHardyAverage_phi_eq w k hw.1 hw.2 one_pos le_rfl, hgamma]

theorem continuousOn_burnolHardyAverage_two_phi_parameter_one (k : ℕ) :
    ContinuousOn
      (fun w : ℂ =>
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1)
      burnolOpenCriticalStrip := by
  let F : ℂ → ℂ := fun z => (1 - z)⁻¹ ^ 2 * burnolUSpectral z
  have hinv : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun z : ℂ => (1 - z)⁻¹) burnolOpenCriticalStrip := by
    intro z hz
    have hden : 1 - z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
      linarith [hz.2]
    fun_prop
  have hF : ContDiffOn ℂ (⊤ : WithTop ℕ∞) F burnolOpenCriticalStrip := by
    dsimp only [F]
    exact (hinv.pow 2).mul contDiffOn_burnolUSpectral
  have hmain :=
    continuousOn_iteratedDeriv_of_contDiffOn_burnolOpenCriticalStrip F hF k
  have hremainder : ContinuousOn
      (fun w : ℂ =>
        burnolHardyAverage
          (burnolHardyAverage (burnolPhiSeriesRemainder w k)) 1)
      burnolOpenCriticalStrip :=
    (continuousOn_burnolHardyAverage_two_phiSeriesRemainder_parameter
      k le_rfl).mono fun w hw => hw.1
  have hgamma :
      (fun z : ℂ => (1 - z)⁻¹ ^ 2 * burnolPhiGammaMain 1 z) = F := by
    funext z
    rw [burnolPhiGammaMain_eq_U_mul_cpow z one_pos]
    simp only [Complex.ofReal_one, Complex.one_cpow, mul_one, F]
  apply (hmain.add hremainder).congr
  intro w hw
  change burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1 =
    iteratedDeriv k F w +
      burnolHardyAverage
        (burnolHardyAverage (burnolPhiSeriesRemainder w k)) 1
  rw [burnolHardyAverage_two_phi_eq w k hw.1 hw.2 one_pos le_rfl,
    hgamma]

theorem eventually_burnolPhiLargeCoeff_le
    (s : ℂ) (k : ℕ) (hs1 : s.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ w : ℂ in 𝓝 s,
        w.re < 1 ∧ burnolPhiLargeCoeff w k ≤ C := by
  let b : ℝ := (1 + s.re) / 2
  let N : ℝ := ‖s‖ + 1
  let B : ℝ → ℝ := fun u =>
    (k : ℝ) * (Real.log u) ^ (k - 1) * u ^ (b - 2) +
      N * (Real.log u) ^ k * u ^ (b - 2)
  let C : ℝ := (1 + ∫ u : ℝ in Ioi 1, B u) / Real.pi
  have hsb : s.re < b := by
    dsimp only [b]
    linarith
  have hb1 : b < 1 := by
    dsimp only [b]
    linarith
  have hsN : ‖s‖ < N := by
    dsimp only [N]
    linarith
  have hre : ∀ᶠ w : ℂ in 𝓝 s, w.re < b :=
    (Complex.continuous_re.isOpen_preimage (Iio b) isOpen_Iio).mem_nhds hsb
  have hnorm : ∀ᶠ w : ℂ in 𝓝 s, ‖w‖ < N :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hsN
  have hB_integrable : Integrable B (volume.restrict (Ioi (1 : ℝ))) := by
    have hfirst :=
      (integrableOn_log_pow_mul_rpow_Ioi_one (k - 1) (b - 2) (by linarith)).const_mul
        (k : ℝ)
    have hsecond :=
      (integrableOn_log_pow_mul_rpow_Ioi_one k (b - 2) (by linarith)).const_mul N
    apply (hfirst.add hsecond).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    dsimp only [B]
    simp only [Pi.add_apply]
    ring
  have hB_nonneg : 0 ≤ ∫ u : ℝ in Ioi 1, B u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu.le
    dsimp only [B]
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog0 _))
        (Real.rpow_nonneg (one_pos.trans hu).le _))
      (mul_nonneg
        (mul_nonneg (by dsimp only [N]; positivity) (pow_nonneg hlog0 _))
        (Real.rpow_nonneg (one_pos.trans hu).le _))
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (by linarith) Real.pi_pos.le
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hre, hnorm] with w hwre hwnorm
  have hw1 : w.re < 1 := hwre.trans hb1
  have hmajor : burnolPhiTailMajor w k ≤ᵐ[volume.restrict (Ioi 1)] B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := hu.le
    have hu0 : 0 < u := one_pos.trans hu
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hfactor := norm_burnolPhiLogFactor_le w k hu1
    have hfactor' : ‖burnolPhiLogFactor w k u‖ ≤
        (k : ℝ) * (Real.log u) ^ (k - 1) +
          N * (Real.log u) ^ k := by
      exact hfactor.trans <| by
        gcongr
    have hpower : u ^ (w.re - 2) ≤ u ^ (b - 2) :=
      Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    unfold burnolPhiTailMajor
    calc
      ‖burnolPhiLogFactor w k u‖ * u ^ (w.re - 2) ≤
          ((k : ℝ) * (Real.log u) ^ (k - 1) +
            N * (Real.log u) ^ k) * u ^ (b - 2) := by
        exact mul_le_mul hfactor' hpower
          (Real.rpow_nonneg hu0.le _) <|
            add_nonneg
              (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hlog0 _))
              (mul_nonneg (by dsimp only [N]; positivity) (pow_nonneg hlog0 _))
      _ = B u := by
        dsimp only [B]
        ring
  have hintegral :
      (∫ u : ℝ in Ioi 1, burnolPhiTailMajor w k u) ≤
        ∫ u : ℝ in Ioi 1, B u :=
    integral_mono_ae (integrableOn_burnolPhiTailMajor w k hw1)
      hB_integrable hmajor
  refine ⟨hw1, ?_⟩
  unfold burnolPhiLargeCoeff
  dsimp only [C]
  exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le

theorem burnolHardyAverage_phi_eq_split_one
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    burnolHardyAverage (burnolPhi w k) t =
      (t : ℂ)⁻¹ *
        (burnolHardyAverage (burnolPhi w k) 1 +
          ∫ u : ℝ in Ioc 1 t, burnolPhi w k u) := by
  have hfull := integrableOn_burnolPhi_Ioc_zero w k hw0 hw1 t
  have hlow : IntegrableOn (burnolPhi w k) (Ioc (0 : ℝ) 1) :=
    hfull.mono_set fun u hu => ⟨hu.1, hu.2.trans ht⟩
  have hhigh : IntegrableOn (burnolPhi w k) (Ioc (1 : ℝ) t) :=
    hfull.mono_set fun u hu => ⟨zero_lt_one.trans hu.1, hu.2⟩
  have hsplit :
      (∫ u : ℝ in Ioc 0 t, burnolPhi w k u) =
        (∫ u : ℝ in Ioc 0 1, burnolPhi w k u) +
          ∫ u : ℝ in Ioc 1 t, burnolPhi w k u := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one ht]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc hlow hhigh
  have hanchor : burnolHardyAverage (burnolPhi w k) 1 =
      ∫ u : ℝ in Ioc 0 1, burnolPhi w k u := by
    simp [burnolHardyAverage]
  rw [burnolHardyAverage, hsplit]
  rw [hanchor]

theorem burnolHardyAverage_two_phi_eq_split_one
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t =
      (t : ℂ)⁻¹ *
        (burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1 +
          ∫ u : ℝ in Ioc 1 t,
            burnolHardyAverage (burnolPhi w k) u) := by
  have hfull :=
    integrableOn_burnolHardyAverage_phi_Ioc_zero w k hw0 hw1 t
  have hlow : IntegrableOn (burnolHardyAverage (burnolPhi w k))
      (Ioc (0 : ℝ) 1) :=
    hfull.mono_set fun u hu => ⟨hu.1, hu.2.trans ht⟩
  have hhigh : IntegrableOn (burnolHardyAverage (burnolPhi w k))
      (Ioc (1 : ℝ) t) :=
    hfull.mono_set fun u hu => ⟨zero_lt_one.trans hu.1, hu.2⟩
  have hsplit :
      (∫ u : ℝ in Ioc 0 t, burnolHardyAverage (burnolPhi w k) u) =
        (∫ u : ℝ in Ioc 0 1, burnolHardyAverage (burnolPhi w k) u) +
          ∫ u : ℝ in Ioc 1 t,
            burnolHardyAverage (burnolPhi w k) u := by
    rw [← Ioc_union_Ioc_eq_Ioc zero_le_one ht]
    exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc hlow hhigh
  have hanchor :
      burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1 =
        ∫ u : ℝ in Ioc 0 1,
          burnolHardyAverage (burnolPhi w k) u := by
    simp [burnolHardyAverage]
  rw [burnolHardyAverage, hsplit]
  rw [hanchor]

theorem continuousAt_burnolHardyAverage_phi_parameter_large
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ContinuousAt
      (fun w : ℂ => burnolHardyAverage (burnolPhi w k) t) s := by
  obtain ⟨C, hC0, hlarge⟩ := eventually_burnolPhiLargeCoeff_le s k hs1
  have hsStrip : s ∈ burnolOpenCriticalStrip := ⟨hs0, hs1⟩
  have hstrip : ∀ᶠ w : ℂ in 𝓝 s, w ∈ burnolOpenCriticalStrip :=
    isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip
  have hintegral : ContinuousAt
      (fun w : ℂ => ∫ u : ℝ in Ioc 1 t, burnolPhi w k u) s := by
    apply continuousAt_of_dominated (bound := fun _ : ℝ => C)
    · filter_upwards [hstrip] with w hw
      exact aestronglyMeasurable_burnolPhi_restrict w k hw.1 hw.2
        measurableSet_Ioc fun u hu => zero_lt_one.trans hu.1
    · filter_upwards [hstrip, hlarge] with w hw hwlarge
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := zero_lt_one.trans hu.1
      calc
        ‖burnolPhi w k u‖ ≤ burnolPhiLargeCoeff w k / u :=
          norm_burnolPhi_le_largeCoeff w k hw.2 hu0
        _ ≤ burnolPhiLargeCoeff w k := by
          simpa only [div_one] using
            (div_le_div_of_nonneg_left (burnolPhiLargeCoeff_nonneg w k)
              one_pos hu.1.le)
        _ ≤ C := hwlarge.2
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact continuousAt_burnolPhi_parameter s k u hs1
  have hanchor : ContinuousAt
      (fun w : ℂ => burnolHardyAverage (burnolPhi w k) 1) s :=
    (continuousOn_burnolHardyAverage_phi_parameter_one k s hsStrip).continuousAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  have hformula : ContinuousAt
      (fun w : ℂ => (t : ℂ)⁻¹ *
        (burnolHardyAverage (burnolPhi w k) 1 +
          ∫ u : ℝ in Ioc 1 t, burnolPhi w k u)) s :=
    continuousAt_const.mul (hanchor.add hintegral)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hstrip] with w hw
  exact burnolHardyAverage_phi_eq_split_one
    w k hw.1 hw.2 ht

theorem continuousAt_burnolHardyAverage_two_phi_parameter_large
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {t : ℝ} (ht : 1 ≤ t) :
    ContinuousAt
      (fun w : ℂ =>
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) t) s := by
  obtain ⟨C, hC0, hlarge⟩ := eventually_burnolPhiLargeCoeff_le s k hs1
  have hsStrip : s ∈ burnolOpenCriticalStrip := ⟨hs0, hs1⟩
  have hstrip : ∀ᶠ w : ℂ in 𝓝 s, w ∈ burnolOpenCriticalStrip :=
    isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip
  have hanchorOne : ContinuousAt
      (fun w : ℂ => burnolHardyAverage (burnolPhi w k) 1) s :=
    (continuousOn_burnolHardyAverage_phi_parameter_one k s hsStrip).continuousAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  let D : ℝ := ‖burnolHardyAverage (burnolPhi s k) 1‖ + 1 + C
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hanchorBound : ∀ᶠ w : ℂ in 𝓝 s,
      ‖burnolHardyAverage (burnolPhi w k) 1‖ <
        ‖burnolHardyAverage (burnolPhi s k) 1‖ + 1 :=
    hanchorOne.norm (Iio_mem_nhds (by linarith))
  have hfirst : ∀ᶠ w : ℂ in 𝓝 s,
      burnolPhiHardyFirstLargeCoeff w k ≤ D := by
    filter_upwards [hlarge, hanchorBound] with w hwlarge hwanchor
    have hanchorEq :
        (∫ u : ℝ in Ioc 0 1, burnolPhi w k u) =
          burnolHardyAverage (burnolPhi w k) 1 := by
      simp [burnolHardyAverage]
    rw [burnolPhiHardyFirstLargeCoeff, hanchorEq]
    dsimp only [D]
    linarith
  have hintegral : ContinuousAt
      (fun w : ℂ => ∫ u : ℝ in Ioc 1 t,
        burnolHardyAverage (burnolPhi w k) u) s := by
    apply continuousAt_of_dominated
      (bound := fun _ : ℝ => D * (1 + Real.log t))
    · filter_upwards [hstrip] with w hw
      exact ((continuousOn_burnolHardyAverage_phi_Ioc_zero
        w k hw.1 hw.2 t).mono fun u hu =>
          ⟨zero_lt_one.trans hu.1, hu.2⟩).aestronglyMeasurable
            measurableSet_Ioc
    · filter_upwards [hstrip, hfirst] with w hw hwfirst
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := zero_lt_one.trans hu.1
      have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu.1.le
      have hlogLe : Real.log u ≤ Real.log t :=
        Real.log_le_log hu0 hu.2
      have hsource := norm_burnolHardyAverage_phi_le_firstLargeCoeff
        w k hw.1 hw.2 hu.1.le
      calc
        ‖burnolHardyAverage (burnolPhi w k) u‖ ≤
            burnolPhiHardyFirstLargeCoeff w k * (1 + Real.log u) / u :=
          hsource
        _ ≤ D * (1 + Real.log u) / u := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hwfirst (by linarith)) hu0.le
        _ ≤ D * (1 + Real.log u) := by
          simpa only [div_one] using
            (div_le_div_of_nonneg_left
              (mul_nonneg hD0 (by linarith)) one_pos hu.1.le)
        _ ≤ D * (1 + Real.log t) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hD0
    · exact integrableOn_const measure_Ioc_lt_top.ne
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact continuousAt_burnolHardyAverage_phi_parameter_large
        s k hs0 hs1 hu.1.le
  have hanchorTwo : ContinuousAt
      (fun w : ℂ =>
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1) s :=
    (continuousOn_burnolHardyAverage_two_phi_parameter_one k s hsStrip).continuousAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  have hformula : ContinuousAt
      (fun w : ℂ => (t : ℂ)⁻¹ *
        (burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1 +
          ∫ u : ℝ in Ioc 1 t,
            burnolHardyAverage (burnolPhi w k) u)) s :=
    continuousAt_const.mul (hanchorTwo.add hintegral)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hstrip] with w hw
  exact burnolHardyAverage_two_phi_eq_split_one
    w k hw.1 hw.2 ht

theorem continuousAt_burnolHardySquareDifference_phi_parameter
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {t : ℝ} (ht0 : 0 < t) :
    ContinuousAt
      (fun w : ℂ => burnolHardySquareDifference (burnolPhi w k) t) s := by
  by_cases ht1 : t ≤ 1
  · have hsStrip : s ∈ burnolOpenCriticalStrip := ⟨hs0, hs1⟩
    exact (continuousOn_burnolHardySquareDifference_phi_parameter_small
      k ht0 ht1 s hsStrip).continuousAt
        (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  · have htLarge : 1 ≤ t := le_of_lt (lt_of_not_ge ht1)
    have hphi := continuousAt_burnolPhi_parameter s k t hs1
    have hone := continuousAt_burnolHardyAverage_phi_parameter_large
      s k hs0 hs1 htLarge
    have htwo := continuousAt_burnolHardyAverage_two_phi_parameter_large
      s k hs0 hs1 htLarge
    unfold burnolHardySquareDifference
    exact (hphi.sub (continuousAt_const.mul hone)).add htwo

theorem continuousAt_burnolYTransformed_parameter
    (lambda : ℝ) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    {t : ℝ} (ht0 : 0 < t) :
    ContinuousAt (fun w : ℂ => burnolYTransformed lambda w k t)
      s := by
  by_cases ht : t ∈ Ici lambda
  · simp only [burnolYTransformed, Set.indicator_of_mem ht]
    exact continuousAt_burnolHardySquareDifference_phi_parameter
      s k hs0 hs1 ht0
  · simp only [burnolYTransformed, Set.indicator_of_notMem ht]
    exact continuousAt_const

theorem continuousOn_burnolVMainDerivCoeffBound_parameter (k : ℕ) :
    ContinuousOn (fun w : ℂ => burnolVMainDerivCoeffBound w k)
      burnolOpenCriticalStrip := by
  have hderiv : ∀ i : ℕ,
      ContinuousOn (fun w : ℂ => iteratedDeriv i burnolVSpectral w)
        burnolOpenCriticalStrip := fun i =>
    continuousOn_iteratedDeriv_of_contDiffOn_burnolOpenCriticalStrip
      burnolVSpectral contDiffOn_burnolVSpectral i
  unfold burnolVMainDerivCoeffBound
  exact continuousOn_finsetSum _ fun i _ =>
    continuousOn_const.mul (hderiv i).norm

theorem eventually_burnolVMainDerivCoeffBound_le
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ w : ℂ in 𝓝 s,
        w ∈ burnolOpenCriticalStrip ∧ burnolVMainDerivCoeffBound w k ≤ C := by
  let C : ℝ := burnolVMainDerivCoeffBound s k + 1
  have hsStrip : s ∈ burnolOpenCriticalStrip := ⟨hs0, hs1⟩
  have hcont : ContinuousAt (fun w : ℂ => burnolVMainDerivCoeffBound w k) s :=
    (continuousOn_burnolVMainDerivCoeffBound_parameter k s hsStrip).continuousAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  have hbound : ∀ᶠ w : ℂ in 𝓝 s,
      burnolVMainDerivCoeffBound w k < C :=
    hcont (Iio_mem_nhds (by dsimp only [C]; linarith))
  have hstrip : ∀ᶠ w : ℂ in 𝓝 s, w ∈ burnolOpenCriticalStrip :=
    isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    linarith [burnolVMainDerivCoeffBound_nonneg s k]
  · filter_upwards [hstrip, hbound] with w hw hC
    exact ⟨hw, hC.le⟩

theorem eventually_burnolPhiHardySquareLargeCoeff_le
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ w : ℂ in 𝓝 s,
        w ∈ burnolOpenCriticalStrip ∧
          burnolPhiHardySquareLargeCoeff w k ≤ C := by
  obtain ⟨Cphi, hCphi0, hphi⟩ :=
    eventually_burnolPhiLargeCoeff_le s k hs1
  have hsStrip : s ∈ burnolOpenCriticalStrip := ⟨hs0, hs1⟩
  have hstrip : ∀ᶠ w : ℂ in 𝓝 s, w ∈ burnolOpenCriticalStrip :=
    isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip
  have hcontOne : ContinuousAt
      (fun w : ℂ => burnolHardyAverage (burnolPhi w k) 1) s :=
    (continuousOn_burnolHardyAverage_phi_parameter_one k s hsStrip).continuousAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  have hcontTwo : ContinuousAt
      (fun w : ℂ =>
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1) s :=
    (continuousOn_burnolHardyAverage_two_phi_parameter_one k s hsStrip).continuousAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)
  let Cone : ℝ := ‖burnolHardyAverage (burnolPhi s k) 1‖ + 1
  let Ctwo : ℝ :=
    ‖burnolHardyAverage (burnolHardyAverage (burnolPhi s k)) 1‖ + 1
  let Cfirst : ℝ := Cone + Cphi
  let Csecond : ℝ := Ctwo + Cfirst
  let C : ℝ := Cphi + 2 * Cfirst + Csecond
  have hCone0 : 0 ≤ Cone := by
    dsimp only [Cone]
    positivity
  have hCtwo0 : 0 ≤ Ctwo := by
    dsimp only [Ctwo]
    positivity
  have hCfirst0 : 0 ≤ Cfirst := by
    dsimp only [Cfirst]
    positivity
  have hCsecond0 : 0 ≤ Csecond := by
    dsimp only [Csecond]
    positivity
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hone : ∀ᶠ w : ℂ in 𝓝 s,
      ‖burnolHardyAverage (burnolPhi w k) 1‖ < Cone :=
    hcontOne.norm (Iio_mem_nhds (by dsimp only [Cone]; linarith))
  have htwo : ∀ᶠ w : ℂ in 𝓝 s,
      ‖burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1‖ < Ctwo :=
    hcontTwo.norm (Iio_mem_nhds (by dsimp only [Ctwo]; linarith))
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hstrip, hphi, hone, htwo] with w hw hwphi hwone hwtwo
  have hanchorOne :
      (∫ u : ℝ in Ioc 0 1, burnolPhi w k u) =
        burnolHardyAverage (burnolPhi w k) 1 := by
    simp [burnolHardyAverage]
  have hanchorTwo :
      (∫ u : ℝ in Ioc 0 1, burnolHardyAverage (burnolPhi w k) u) =
        burnolHardyAverage (burnolHardyAverage (burnolPhi w k)) 1 := by
    simp [burnolHardyAverage]
  have hfirst : burnolPhiHardyFirstLargeCoeff w k ≤ Cfirst := by
    rw [burnolPhiHardyFirstLargeCoeff, hanchorOne]
    dsimp only [Cfirst]
    linarith
  have hsecond : burnolPhiHardySecondLargeCoeff w k ≤ Csecond := by
    rw [burnolPhiHardySecondLargeCoeff, hanchorTwo]
    dsimp only [Csecond]
    linarith
  refine ⟨hw, ?_⟩
  rw [burnolPhiHardySquareLargeCoeff]
  dsimp only [C]
  linarith

def burnolYBoundaryLocalMajor
    (lambda CV CL : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (Icc lambda 1).indicator
      (fun u : ℝ =>
        CV * (1 + |Real.log u|) ^ k * u ^ (-1 : ℝ) +
          4 * burnolPhiSeriesBound k) t +
    (Ioi (1 : ℝ)).indicator
      (fun u : ℝ => CL * (1 + Real.log u) ^ 2 / u) t

theorem integrableOn_sq_burnolYBoundaryLocalMajor
    {lambda CV CL : ℝ} (hlambda0 : 0 < lambda) (k : ℕ) :
    IntegrableOn (fun t : ℝ => burnolYBoundaryLocalMajor lambda CV CL k t ^ 2)
      (Ioi (0 : ℝ)) := by
  let small : ℝ → ℝ := fun t =>
    CV * (1 + |Real.log t|) ^ k * t ^ (-1 : ℝ) +
      4 * burnolPhiSeriesBound k
  let large : ℝ → ℝ := fun t => CL * (1 + Real.log t) ^ 2 / t
  have hsmall : Integrable (fun t : ℝ => (Icc lambda 1).indicator
      (fun u => small u ^ 2) t) := by
    have hsmallOn : IntegrableOn (fun u : ℝ => small u ^ 2)
        (Icc lambda 1) := by
      have hcont : ContinuousOn (fun u : ℝ => small u ^ 2)
          (Icc lambda 1) := by
        intro t ht
        have ht0 : 0 < t := hlambda0.trans_le ht.1
        have hlog : ContinuousAt (fun u : ℝ => Real.log u) t :=
          Real.continuousAt_log ht0.ne'
        have hrpow : ContinuousAt (fun u : ℝ => u ^ (-1 : ℝ)) t :=
          Real.continuousAt_rpow_const t (-1) (Or.inl ht0.ne')
        dsimp only [small]
        exact ((((continuousAt_const.mul
          ((continuousAt_const.add hlog.abs).pow k)).mul hrpow).add
            continuousAt_const).pow 2).continuousWithinAt
      exact hcont.integrableOn_Icc
    exact hsmallOn.integrable_indicator measurableSet_Icc
  have hlargeMajor : IntegrableOn
      (fun t : ℝ => 8 * CL ^ 2 *
        (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)))
      (Ioi (1 : ℝ)) :=
    integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * CL ^ 2)
  have hlargeOn : IntegrableOn (fun t : ℝ => large t ^ 2) (Ioi (1 : ℝ)) := by
    apply Integrable.mono' hlargeMajor
    · have hcont : ContinuousOn (fun t : ℝ => large t ^ 2) (Ioi (1 : ℝ)) := by
        intro t ht
        have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
        dsimp only [large]
        fun_prop
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have ht1 : 1 ≤ t := ht.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hadd : (1 + Real.log t) ^ 4 ≤
        8 * (1 + (Real.log t) ^ 4) := by
      have h := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hlog0 4
      norm_num at h
      exact h
    have hinvSq : t⁻¹ ^ 2 = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht0.le]
      exact (inv_pow t 2).trans
        (congrArg Inv.inv (Real.rpow_natCast t 2).symm)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    dsimp only [large]
    calc
      (CL * (1 + Real.log t) ^ 2 / t) ^ 2 =
          CL ^ 2 * (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, mul_pow, mul_pow, hinvSq]
        ring
      _ ≤ CL ^ 2 * (8 * (1 + (Real.log t) ^ 4)) *
          t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hadd (sq_nonneg CL))
          (Real.rpow_nonneg ht0.le _)
      _ = 8 * CL ^ 2 *
          (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)) := by
        ring
  have hlarge : Integrable (fun t : ℝ => (Ioi (1 : ℝ)).indicator
      (fun u => large u ^ 2) t) :=
    hlargeOn.integrable_indicator measurableSet_Ioi
  have hsum := hsmall.add hlarge
  apply hsum.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  dsimp only [small, large]
  unfold burnolYBoundaryLocalMajor
  by_cases hsmallMem : t ∈ Icc lambda 1
  · have hlargeNot : t ∉ Ioi (1 : ℝ) := fun h => (not_lt_of_ge hsmallMem.2) h
    simp [hsmallMem, hlargeNot]
  · by_cases hlargeMem : t ∈ Ioi (1 : ℝ)
    · simp [hsmallMem, hlargeMem]
    · simp [hsmallMem, hlargeMem]

theorem norm_burnolYTransformed_le_boundaryLocalMajor
    {lambda CV CL : ℝ} (hlambda1 : lambda ≤ 1)
    (hCV0 : 0 ≤ CV)
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hCV : burnolVMainDerivCoeffBound w k ≤ CV)
    (hCL : burnolPhiHardySquareLargeCoeff w k ≤ CL)
    {t : ℝ} (ht0 : 0 < t) :
    ‖burnolYTransformed lambda w k t‖ ≤
      burnolYBoundaryLocalMajor lambda CV CL k t := by
  by_cases hlambdaT : lambda ≤ t
  · have htCutoff : t ∈ Ici lambda := hlambdaT
    rw [burnolYTransformed, Set.indicator_of_mem htCutoff]
    by_cases ht1 : t ≤ 1
    · have htSmall : t ∈ Icc lambda 1 := ⟨hlambdaT, ht1⟩
      have htLarge : t ∉ Ioi (1 : ℝ) := fun h => (not_lt_of_ge ht1) h
      rw [burnolYBoundaryLocalMajor,
        Set.indicator_of_mem htSmall, Set.indicator_of_notMem htLarge, add_zero]
      have hpower : t ^ (-w.re) ≤ t ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
      have hbound := norm_burnolHardySquareDifference_phi_le_small
        w k hw0 hw1 ht0 ht1
      calc
        ‖burnolHardySquareDifference (burnolPhi w k) t‖ ≤
            burnolVMainDerivCoeffBound w k *
                (1 + |Real.log t|) ^ k * t ^ (-w.re) +
              4 * burnolPhiSeriesBound k := hbound
        _ ≤ CV * (1 + |Real.log t|) ^ k * t ^ (-1 : ℝ) +
              4 * burnolPhiSeriesBound k := by
          gcongr
    · have htLarge : t ∈ Ioi (1 : ℝ) := lt_of_not_ge ht1
      have htSmall : t ∉ Icc lambda 1 := fun h => ht1 h.2
      rw [burnolYBoundaryLocalMajor,
        Set.indicator_of_notMem htSmall, Set.indicator_of_mem htLarge, zero_add]
      have hbound := norm_burnolHardySquareDifference_phi_le_large
        w k hw0 hw1 htLarge.le
      calc
        ‖burnolHardySquareDifference (burnolPhi w k) t‖ ≤
            burnolPhiHardySquareLargeCoeff w k *
              (1 + Real.log t) ^ 2 / t := hbound
        _ ≤ CL * (1 + Real.log t) ^ 2 / t := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCL
              (pow_nonneg (by linarith [Real.log_nonneg htLarge.le]) _)) ht0.le
  · have htCutoff : t ∉ Ici lambda := not_le.mpr (lt_of_not_ge hlambdaT)
    have htSmall : t ∉ Icc lambda 1 := fun h => htCutoff h.1
    have htLarge : t ∉ Ioi (1 : ℝ) := by
      intro h
      exact hlambdaT (hlambda1.trans h.le)
    rw [burnolYTransformed, Set.indicator_of_notMem htCutoff,
      norm_zero, burnolYBoundaryLocalMajor,
      Set.indicator_of_notMem htSmall, Set.indicator_of_notMem htLarge,
      zero_add]

theorem burnolYTransformed_memLp
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MemLp (burnolYTransformed lambda s k) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  let H : ℝ → ℂ := burnolHardySquareDifference (burnolPhi s k)
  let Csmall : ℝ := burnolVMainDerivCoeffBound s k
  let Bsmall : ℝ := 4 * burnolPhiSeriesBound k
  let Clarge : ℝ := burnolPhiHardySquareLargeCoeff s k
  have hHmeas : AEStronglyMeasurable H (volume.restrict (Ioi (0 : ℝ))) :=
    aestronglyMeasurable_burnolHardySquareDifference_phi_Ioi s k hs0 hs1
  have hYmeas : AEStronglyMeasurable (burnolYTransformed lambda s k)
      (volume.restrict (Ioi (0 : ℝ))) :=
    aestronglyMeasurable_burnolYTransformed lambda s k hs0 hs1
  rw [memLp_two_iff_integrable_sq_norm hYmeas]
  change IntegrableOn (fun t : ℝ => ‖burnolYTransformed lambda s k t‖ ^ 2)
    (Ioi (0 : ℝ))
  have hsmallMajor : IntegrableOn
      (fun t : ℝ =>
        (Csmall * (1 + |Real.log t|) ^ k * t ^ (-s.re) + Bsmall) ^ 2)
      (Icc lambda 1) := by
    have hcont : ContinuousOn
        (fun t : ℝ =>
          (Csmall * (1 + |Real.log t|) ^ k * t ^ (-s.re) + Bsmall) ^ 2)
        (Icc lambda 1) := by
      intro t ht
      have ht0 : 0 < t := hlambda0.trans_le ht.1
      have hlog : ContinuousAt (fun x : ℝ => Real.log x) t :=
        Real.continuousAt_log ht0.ne'
      have hrpow : ContinuousAt (fun x : ℝ => x ^ (-s.re)) t :=
        Real.continuousAt_rpow_const t (-s.re) (Or.inl ht0.ne')
      exact (((continuousAt_const.mul
        ((continuousAt_const.add hlog.abs).pow k)).mul hrpow).add
          continuousAt_const).pow 2 |>.continuousWithinAt
    exact hcont.integrableOn_Icc
  have hsmall : IntegrableOn
      (fun t : ℝ => ‖burnolYTransformed lambda s k t‖ ^ 2)
      (Ioc (0 : ℝ) 1) := by
    have hindicator : (fun t : ℝ => ‖burnolYTransformed lambda s k t‖ ^ 2) =
        (Ici lambda).indicator (fun t : ℝ => ‖H t‖ ^ 2) := by
      funext t
      by_cases ht : t ∈ Ici lambda
      · simp [burnolYTransformed, H, ht]
      · simp [burnolYTransformed, H, ht]
    rw [hindicator, integrableOn_indicator_iff measurableSet_Ici]
    have hset : Ici lambda ∩ Ioc (0 : ℝ) 1 = Icc lambda 1 := by
      ext t
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · intro ht
        exact ⟨ht.1, ht.2.2⟩
      · intro ht
        exact ⟨ht.1, hlambda0.trans_le ht.1, ht.2⟩
    rw [hset]
    apply Integrable.mono' hsmallMajor
      ((hHmeas.mono_set (fun t ht => hlambda0.trans_le ht.1)).norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
    have ht0 : 0 < t := hlambda0.trans_le ht.1
    have hbound := norm_burnolHardySquareDifference_phi_le_small
      s k hs0 hs1 ht0 ht.2
    dsimp only [H, Csmall, Bsmall]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hlargeMajor : IntegrableOn
      (fun t : ℝ => 8 * Clarge ^ 2 *
        (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)))
      (Ioi (1 : ℝ)) :=
    integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * Clarge ^ 2)
  have hlarge : IntegrableOn
      (fun t : ℝ => ‖burnolYTransformed lambda s k t‖ ^ 2)
      (Ioi (1 : ℝ)) := by
    apply Integrable.mono' hlargeMajor
      ((hYmeas.mono_set (Ioi_subset_Ioi zero_le_one)).norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlambda : lambda ≤ t := hlambda1.trans ht1
    have hY : burnolYTransformed lambda s k t = H t := by
      simp [burnolYTransformed, H, hlambda]
    have hbound := norm_burnolHardySquareDifference_phi_le_large
      s k hs0 hs1 ht1
    have hboundSq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hadd : (1 + Real.log t) ^ 4 ≤
        8 * (1 + (Real.log t) ^ 4) := by
      have h := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hlog0 4
      norm_num at h
      exact h
    have hinvSq : t⁻¹ ^ 2 = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht0.le]
      exact (inv_pow t 2).trans
        (congrArg Inv.inv (Real.rpow_natCast t 2).symm)
    rw [hY]
    calc
      ‖H t‖ ^ 2 ≤ (Clarge * (1 + Real.log t) ^ 2 / t) ^ 2 := by
        simpa only [H, Clarge] using hboundSq
      _ = Clarge ^ 2 * (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, mul_pow, mul_pow, hinvSq]
        ring
      _ ≤ Clarge ^ 2 * (8 * (1 + (Real.log t) ^ 4)) *
          t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hadd (sq_nonneg Clarge))
          (Real.rpow_nonneg ht0.le _)
      _ = 8 * Clarge ^ 2 *
          (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)) := by ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hsmall.union hlarge

/-- The explicit transformed representative as an `L2` vector, totalized off its source domain. -/
def burnolYTransformedL2
    (lambda : ℝ) (s : ℂ) (k : ℕ) : positiveHalfLineComplexL2 :=
  if h : 0 < lambda ∧ lambda ≤ 1 ∧ 0 < s.re ∧ s.re < 1 then
    (burnolYTransformed_memLp h.1 h.2.1 s k h.2.2.1 h.2.2.2).toLp
      (burnolYTransformed lambda s k)
  else 0

theorem burnolYTransformedL2_coeFn
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    burnolYTransformedL2 lambda s k =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolYTransformed lambda s k := by
  rw [burnolYTransformedL2, dif_pos ⟨hlambda0, hlambda1, hs0, hs1⟩]
  exact MemLp.coeFn_toLp
    (burnolYTransformed_memLp hlambda0 hlambda1 s k hs0 hs1)

theorem tendsto_burnolYTransformedL2
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs : s.re = 1 / 2) :
    Tendsto (fun w : ℂ => burnolYTransformedL2 lambda w k)
      (𝓝[{w : ℂ | w.re < 1 / 2}] s)
      (𝓝 (burnolYTransformedL2 lambda s k)) := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  obtain ⟨CV0, hCV00, hCVevent⟩ :=
    eventually_burnolVMainDerivCoeffBound_le s k hs0 hs1
  obtain ⟨CL0, hCL00, hCLevent⟩ :=
    eventually_burnolPhiHardySquareLargeCoeff_le s k hs0 hs1
  let CV : ℝ := CV0 + burnolVMainDerivCoeffBound s k
  let CL : ℝ := CL0 + burnolPhiHardySquareLargeCoeff s k
  let D : ℝ → ℝ := burnolYBoundaryLocalMajor lambda CV CL k
  let l : Filter ℂ := 𝓝[{w : ℂ | w.re < 1 / 2}] s
  have hCV0 : 0 ≤ CV := by
    dsimp only [CV]
    exact add_nonneg hCV00 (burnolVMainDerivCoeffBound_nonneg s k)
  have hCVs : burnolVMainDerivCoeffBound s k ≤ CV := by
    dsimp only [CV]
    linarith
  have hCLs : burnolPhiHardySquareLargeCoeff s k ≤ CL := by
    dsimp only [CL]
    linarith
  have hCVwithin : ∀ᶠ w : ℂ in l,
      w ∈ burnolOpenCriticalStrip ∧ burnolVMainDerivCoeffBound w k ≤ CV := by
    filter_upwards [hCVevent.filter_mono inf_le_left] with w hw
    exact ⟨hw.1, hw.2.trans (by
      dsimp only [CV]
      linarith [burnolVMainDerivCoeffBound_nonneg s k])⟩
  have hCLwithin : ∀ᶠ w : ℂ in l,
      w ∈ burnolOpenCriticalStrip ∧
        burnolPhiHardySquareLargeCoeff w k ≤ CL := by
    filter_upwards [hCLevent.filter_mono inf_le_left] with w hw
    exact ⟨hw.1, hw.2.trans (by
      dsimp only [CL]
      linarith [burnolPhiHardySquareLargeCoeff_nonneg s k])⟩
  have hD_sq_integrable : Integrable (fun t : ℝ => 4 * D t ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_sq_burnolYBoundaryLocalMajor
      (CV := CV) (CL := CL) hlambda0 k).const_mul 4
  have hsBound : ∀ t : ℝ, 0 < t →
      ‖burnolYTransformed lambda s k t‖ ≤ D t := by
    intro t ht
    exact norm_burnolYTransformed_le_boundaryLocalMajor
      hlambda1 hCV0 s k hs0 hs1 hCVs hCLs ht
  have hmeas : ∀ᶠ w : ℂ in l,
      AEStronglyMeasurable
        (fun t : ℝ =>
          ‖burnolYTransformed lambda w k t -
            burnolYTransformed lambda s k t‖ ^ 2)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hCVwithin] with w hw
    exact (((aestronglyMeasurable_burnolYTransformed
      lambda w k hw.1.1 hw.1.2).sub
        (aestronglyMeasurable_burnolYTransformed
          lambda s k hs0 hs1)).norm.pow 2)
  have hbound : ∀ᶠ w : ℂ in l,
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ‖‖burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t‖ ^ 2‖ ≤ 4 * D t ^ 2 := by
    filter_upwards [hCVwithin, hCLwithin] with w hwCV hwCL
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hwBound : ‖burnolYTransformed lambda w k t‖ ≤ D t :=
      norm_burnolYTransformed_le_boundaryLocalMajor
        hlambda1 hCV0 w k hwCV.1.1 hwCV.1.2 hwCV.2 hwCL.2 ht
    have hsBound' := hsBound t ht
    have hD0 : 0 ≤ D t := (norm_nonneg _).trans hwBound
    have hdiff :
        ‖burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t‖ ≤ 2 * D t := by
      calc
        ‖burnolYTransformed lambda w k t -
            burnolYTransformed lambda s k t‖ ≤
            ‖burnolYTransformed lambda w k t‖ +
              ‖burnolYTransformed lambda s k t‖ := norm_sub_le _ _
        _ ≤ D t + D t := add_le_add hwBound hsBound'
        _ = 2 * D t := by ring
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc
      ‖burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t‖ ^ 2 ≤ (2 * D t) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hdiff 2
      _ = 4 * D t ^ 2 := by ring
  have hpointwise : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun w : ℂ =>
        ‖burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t‖ ^ 2) l (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hy : Tendsto (fun w : ℂ => burnolYTransformed lambda w k t)
        l (𝓝 (burnolYTransformed lambda s k t)) :=
      (continuousAt_burnolYTransformed_parameter
        lambda s k hs0 hs1 ht).tendsto.mono_left inf_le_left
    have hc : Tendsto
        (fun _ : ℂ => burnolYTransformed lambda s k t) l
        (𝓝 (burnolYTransformed lambda s k t)) := tendsto_const_nhds
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hy.sub hc).norm.pow 2)
  have hintegral : Tendsto (fun w : ℂ =>
      ∫ t : ℝ in Ioi 0,
        ‖burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => 4 * D t ^ 2) hmeas hbound hD_sq_integrable hpointwise
    simpa using h
  have hmem : ∀ᶠ w : ℂ in l,
      MemLp (fun t : ℝ =>
        burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t)
        (2 : ℝ≥0∞) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hCVwithin] with w hw
    exact (burnolYTransformed_memLp hlambda0 hlambda1 w k hw.1.1 hw.1.2).sub
      (burnolYTransformed_memLp hlambda0 hlambda1 s k hs0 hs1)
  have hsqrt : Tendsto (fun w : ℂ => ENNReal.ofReal <|
      Real.sqrt (∫ t : ℝ in Ioi 0,
        ‖burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t‖ ^ 2)) l (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hintegral.sqrt
  have hELp : Tendsto (fun w : ℂ =>
      eLpNorm (fun t : ℝ =>
        burnolYTransformed lambda w k t -
          burnolYTransformed lambda s k t)
        (2 : ℝ≥0∞) (volume.restrict (Ioi (0 : ℝ)))) l (𝓝 0) := by
    apply hsqrt.congr'
    filter_upwards [hmem] with w hw
    rw [hw.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun w : ℂ => burnolYTransformedL2 lambda w k)
    (burnolYTransformedL2 lambda s k)).2
  apply hELp.congr'
  filter_upwards [hCVwithin] with w hw
  exact eLpNorm_congr_ae <|
    ((burnolYTransformedL2_coeFn hlambda0 hlambda1 w k hw.1.1 hw.1.2).sub
      (burnolYTransformedL2_coeFn hlambda0 hlambda1 s k hs0 hs1)).symm

theorem burnolYTransformedL2_eq_cutoff_hardySquare
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (w : ℂ) (k : ℕ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    burnolYTransformedL2 lambda w k =
      burnolCutoffL2 lambda (burnolHardySquarePhiL2 w k) := by
  have hw1 : w.re < 1 := hwHalf.trans (by norm_num)
  apply Lp.ext
  filter_upwards [
    burnolYTransformedL2_coeFn hlambda0 hlambda1 w k hw0 hw1,
    burnolCutoffL2_coeFn lambda (burnolHardySquarePhiL2 w k),
    burnolHardySquarePhiL2_coeFn w k hw0 hwHalf] with t hY hcutoff hhardy
  rw [hY, hcutoff]
  unfold burnolYTransformed
  by_cases ht : t ∈ Ici lambda
  · simp only [Set.indicator_of_mem ht]
    exact hhardy.symm
  · simp only [Set.indicator_of_notMem ht]

/-- Burnol's boundary-vector candidate obtained by transporting the explicit representative
through the inverse total phase. Boundary convergence is proved separately. -/
def burnolY (lambda : ℝ) (s : ℂ) (k : ℕ) : positiveHalfLineComplexL2 :=
  burnolAPhaseL2.symm (burnolYTransformedL2 lambda s k)

theorem tendsto_burnolPreY
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs : s.re = 1 / 2) :
    Tendsto (fun w : ℂ => burnolPreY lambda w k)
      (𝓝[{w : ℂ | w.re < 1 / 2}] s)
      (𝓝 (burnolY lambda s k)) := by
  let l : Filter ℂ := 𝓝[{w : ℂ | w.re < 1 / 2}] s
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  have htransformed := tendsto_burnolYTransformedL2
    hlambda0 hlambda1 s k hs
  have htransformed' : Tendsto
      (fun w : ℂ => burnolYTransformedL2 lambda w k) l
      (𝓝 (burnolYTransformedL2 lambda s k)) := by
    simpa only [l] using htransformed
  have htransported : Tendsto
      (fun w : ℂ => burnolAPhaseL2.symm (burnolYTransformedL2 lambda w k))
      l (𝓝 (burnolY lambda s k)) := by
    rw [burnolY]
    exact burnolAPhaseL2.symm.continuous.continuousAt.tendsto.comp htransformed'
  have hstripNhds : ∀ᶠ w : ℂ in 𝓝 s, w ∈ burnolOpenCriticalStrip :=
    isOpen_burnolOpenCriticalStrip.mem_nhds ⟨hs0, hs1⟩
  have hstrip : ∀ᶠ w : ℂ in l, w ∈ burnolOpenCriticalStrip :=
    hstripNhds.filter_mono inf_le_left
  have hleft : ∀ᶠ w : ℂ in l, w.re < 1 / 2 := by
    simpa only [Set.mem_setOf_eq] using
      (eventually_mem_nhdsWithin : ∀ᶠ w : ℂ in l, w ∈ {w | w.re < 1 / 2})
  apply htransported.congr'
  filter_upwards [hstrip, hleft] with w hw hwHalf
  calc
    burnolAPhaseL2.symm (burnolYTransformedL2 lambda w k) =
        burnolAPhaseL2.symm
          (burnolCutoffL2 lambda (burnolHardySquarePhiL2 w k)) := by
      exact congrArg burnolAPhaseL2.symm
        (burnolYTransformedL2_eq_cutoff_hardySquare
          hlambda0 hlambda1 w k hw.1 hwHalf)
    _ = burnolPreY lambda w k :=
      (burnolPreY_eq_hardySquare_cutoff lambda w k hw.1 hwHalf).symm

theorem continuousAt_iteratedDeriv_burnolBoundaryPairingSource
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ContinuousAt (fun w : ℂ =>
      iteratedDeriv k (burnolBoundaryPairingSource theta) w) s := by
  let S : Set ℂ := {0}ᶜ ∩ {1}ᶜ
  have hSopen : IsOpen S :=
    isOpen_compl_singleton.inter isOpen_compl_singleton
  have hsS : s ∈ S := by
    exact ⟨by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff],
      by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]⟩
  have hdiff : DifferentiableOn ℂ (burnolBoundaryPairingSource theta) S := by
    intro w hw
    have hw0 : w ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw.1
    have hw1 : w ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hw.2
    have htheta0 : ((theta : ℝ) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt theta.prop.1)
    have hcpow : DifferentiableAt ℂ
        (fun z : ℂ => ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) w := by
      rw [show (fun z : ℂ => ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - z)) =
          fun z : ℂ => Complex.exp
            ((Real.log (theta : ℝ) : ℂ) * ((1 / 2 : ℂ) - z)) by
        funext z
        rw [Complex.cpow_def_of_ne_zero htheta0,
          ← Complex.ofReal_log theta.prop.1.le]]
      fun_prop
    have harg1 : 1 - w ≠ 1 := by
      intro h
      apply hw0
      linear_combination -h
    have harg0 : 1 - w ≠ 0 := sub_ne_zero.mpr hw1.symm
    have hzeta : DifferentiableAt ℂ
        (fun z : ℂ => riemannZeta (1 - z)) w :=
      (differentiableAt_riemannZeta harg1).comp w (by fun_prop)
    have hlinear : DifferentiableAt ℂ (fun z : ℂ => 1 - z) w := by
      fun_prop
    have hZ : DifferentiableAt ℂ (fun z : ℂ => burnolZ (1 - z)) w := by
      unfold burnolZ
      exact ((hlinear.sub_const 1).mul hzeta).div (hlinear.pow 2)
        (pow_ne_zero 2 harg0)
    unfold burnolBoundaryPairingSource
    exact (hcpow.mul hZ).differentiableWithinAt
  have hcontDiff : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (burnolBoundaryPairingSource theta) S :=
    hdiff.contDiffOn hSopen
  have hwithin := hcontDiff.continuousOn_iteratedDerivWithin (m := k) (by simp)
    hSopen.uniqueDiffOn
  have hderiv : ContinuousOn
      (iteratedDeriv k (burnolBoundaryPairingSource theta)) S :=
    hwithin.congr (iteratedDerivWithin_of_isOpen hSopen).symm
  exact (hderiv s hsS).continuousAt (hSopen.mem_nhds hsS)

theorem inner_normalizedModelKernel_burnolY_eq_iteratedDeriv
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) (hs : s.re = 1 / 2) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolY lambda s k) =
      iteratedDeriv k (burnolBoundaryPairingSource theta) s := by
  let l : Filter ℂ := 𝓝[{w : ℂ | w.re < 1 / 2}] s
  have hs0re : 0 < s.re := by rw [hs]; norm_num
  have hs1re : s.re < 1 := by rw [hs]; norm_num
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs0re
    norm_num at hs0re
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs1re
    norm_num at hs1re
  have hpre := tendsto_burnolPreY hlambda0 hlambda1 s k hs
  have hpre' : Tendsto (fun w : ℂ => burnolPreY lambda w k) l
      (𝓝 (burnolY lambda s k)) := by
    simpa only [l] using hpre
  have hinnerMap : Continuous (fun y : positiveHalfLineComplexL2 =>
      inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta) y) := by
    fun_prop
  have hleft : Tendsto (fun w : ℂ =>
      inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w k)) l
      (𝓝 (inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolY lambda s k))) := by
    have hcomp := hinnerMap.continuousAt.tendsto.comp hpre'
    change Tendsto (fun w : ℂ =>
      inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w k)) l
      (𝓝 (inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolY lambda s k))) at hcomp
    exact hcomp
  have hright : Tendsto (fun w : ℂ =>
      iteratedDeriv k (burnolBoundaryPairingSource theta) w) l
      (𝓝 (iteratedDeriv k (burnolBoundaryPairingSource theta) s)) :=
    (continuousAt_iteratedDeriv_burnolBoundaryPairingSource
      theta s k hs0 hs1).tendsto.mono_left inf_le_left
  have hstripNhds : ∀ᶠ w : ℂ in 𝓝 s, w ∈ burnolOpenCriticalStrip :=
    isOpen_burnolOpenCriticalStrip.mem_nhds ⟨hs0re, hs1re⟩
  have hstrip : ∀ᶠ w : ℂ in l, w ∈ burnolOpenCriticalStrip :=
    hstripNhds.filter_mono inf_le_left
  have hhalf : ∀ᶠ w : ℂ in l, w.re < 1 / 2 := by
    simpa only [Set.mem_setOf_eq] using
      (eventually_mem_nhdsWithin : ∀ᶠ w : ℂ in l, w ∈ {w | w.re < 1 / 2})
  have hright' : Tendsto (fun w : ℂ =>
      inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolPreY lambda w k)) l
      (𝓝 (iteratedDeriv k (burnolBoundaryPairingSource theta) s)) := by
    apply hright.congr'
    filter_upwards [hstrip, hhalf] with w hw hwHalf
    exact (inner_normalizedModelKernel_burnolPreY_eq_iteratedDeriv
      lambda theta w k hlambdaTheta hw.1 hwHalf).symm
  have hsClosure : s ∈ closure {w : ℂ | w.re < 1 / 2} := by
    rw [show {w : ℂ | w.re < 1 / 2} =
        Complex.re ⁻¹' Iio (1 / 2 : ℝ) by rfl,
      ← Complex.isOpenMap_re.preimage_closure_eq_closure_preimage
        Complex.continuous_re,
      closure_Iio]
    change s.re ≤ 1 / 2
    rw [hs]
  letI : l.NeBot := by
    dsimp only [l]
    exact mem_closure_iff_nhdsWithin_neBot.mp hsClosure
  exact tendsto_nhds_unique hleft hright'

def burnolBoundaryPairingFactor
    (theta : burnolContinuousParameter) (w : ℂ) : ℂ :=
  -(((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w)) *
    (1 - w)⁻¹ * burnolUSpectral w

theorem burnolBoundaryPairingSource_eq_factor_mul_zeta
    (theta : burnolContinuousParameter) {w : ℂ}
    (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    burnolBoundaryPairingSource theta w =
      burnolBoundaryPairingFactor theta w * riemannZeta w := by
  have hn : ∀ n : ℕ, w ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hwne1 : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hden : 1 - w ≠ 0 := sub_ne_zero.mpr hwne1.symm
  rw [burnolBoundaryPairingSource, burnolZ,
    riemannZeta_one_sub hn hwne1, burnolBoundaryPairingFactor,
    burnolUSpectral]
  field_simp
  ring_nf
  rw [Complex.ofReal_mul]
  ac_rfl

theorem contDiffOn_burnolBoundaryPairingFactor
    (theta : burnolContinuousParameter) :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (burnolBoundaryPairingFactor theta)
      burnolOpenCriticalStrip := by
  have htheta0 : ((theta : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt theta.property.1)
  have hcpow : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun w : ℂ => ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w)) := by
    rw [show (fun w : ℂ => ((theta : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - w)) =
        fun w : ℂ => Complex.exp
          ((Real.log (theta : ℝ) : ℂ) * ((1 / 2 : ℂ) - w)) by
      funext w
      rw [Complex.cpow_def_of_ne_zero htheta0,
        ← Complex.ofReal_log theta.property.1.le]]
    fun_prop
  have hinv : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun w : ℂ => (1 - w)⁻¹) burnolOpenCriticalStrip := by
    intro w hw
    have hden : 1 - w ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
      linarith [hw.2]
    fun_prop
  unfold burnolBoundaryPairingFactor
  exact (hcpow.neg.contDiffOn.mul hinv).mul contDiffOn_burnolUSpectral

theorem iteratedDeriv_burnolBoundaryPairingSource_eq_zero_of_order
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (horder : (k + 1 : ℕ∞) ≤ analyticOrderAt riemannZeta s) :
    iteratedDeriv k (burnolBoundaryPairingSource theta) s = 0 := by
  have hsStrip : s ∈ burnolOpenCriticalStrip := ⟨hs0, hs1⟩
  have hsne1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hsne1)
  have hzetaContDiff : ContDiffAt ℂ k riemannZeta s :=
    hzetaAnalytic.contDiffAt
  have hfactorContDiff : ContDiffAt ℂ k
      (burnolBoundaryPairingFactor theta) s :=
    ((contDiffOn_burnolBoundaryPairingFactor theta s hsStrip).contDiffAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip)).of_le (by simp)
  have hzero : ∀ i < k + 1, iteratedDeriv i riemannZeta s = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      hzetaAnalytic).mp horder
  have heq : burnolBoundaryPairingSource theta =ᶠ[𝓝 s]
      fun w : ℂ => burnolBoundaryPairingFactor theta w * riemannZeta w := by
    filter_upwards [isOpen_burnolOpenCriticalStrip.mem_nhds hsStrip] with w hw
    exact burnolBoundaryPairingSource_eq_factor_mul_zeta theta hw.1 hw.2
  rw [heq.iteratedDeriv_eq k]
  change iteratedDeriv k
      (burnolBoundaryPairingFactor theta * riemannZeta) s = 0
  rw [iteratedDeriv_mul hfactorContDiff hzetaContDiff]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
  simp only [hzero (k - i) (by omega), mul_zero]

private theorem iteratedDeriv_conj_conj_complex (f : ℂ → ℂ) (k : ℕ) :
    iteratedDeriv k (conj ∘ f ∘ conj) =
      conj ∘ iteratedDeriv k f ∘ conj := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ, ih, deriv_conj_conj, ← iteratedDeriv_succ]

theorem burnolZ_conj (z : ℂ) :
    burnolZ (conj z) = conj (burnolZ z) := by
  simp only [burnolZ, map_div₀, map_mul, map_sub, map_one, map_pow,
    ← riemannZeta_conj]

theorem burnolDirectPairingSource_conj
    (theta : burnolContinuousParameter) (z : ℂ) :
    burnolDirectPairingSource theta (conj z) =
      conj (burnolDirectPairingSource theta z) := by
  have harg : (((theta : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg theta.property.1.le]
    exact Real.pi_pos.ne
  have hpow := Complex.cpow_conj (((theta : ℝ) : ℂ))
    (z - (1 / 2 : ℂ)) harg
  rw [burnolDirectPairingSource, burnolDirectPairingSource,
    burnolZ_conj, map_mul]
  congr 1
  simpa only [map_sub, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
    Complex.ofReal_one, Complex.ofReal_ofNat] using hpow

theorem star_iteratedDeriv_burnolDirectPairingSource_conj
    (theta : burnolContinuousParameter) (z : ℂ) (k : ℕ) :
    conj (iteratedDeriv k (burnolDirectPairingSource theta) (conj z)) =
      iteratedDeriv k (burnolDirectPairingSource theta) z := by
  have hfun : conj ∘ burnolDirectPairingSource theta ∘ conj =
      burnolDirectPairingSource theta := by
    funext w
    change conj (burnolDirectPairingSource theta (conj w)) =
      burnolDirectPairingSource theta w
    rw [burnolDirectPairingSource_conj]
    simp
  have hderiv := congrFun
    (iteratedDeriv_conj_conj_complex (burnolDirectPairingSource theta) k) z
  rw [hfun] at hderiv
  simpa only [Function.comp_apply] using hderiv.symm

theorem burnolBoundaryPairingSource_eq_direct_one_sub
    (theta : burnolContinuousParameter) :
    burnolBoundaryPairingSource theta =
      fun w : ℂ => burnolDirectPairingSource theta (1 - w) := by
  funext w
  rw [burnolBoundaryPairingSource, burnolDirectPairingSource]
  congr 1
  ring

theorem conj_eq_one_sub_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    conj s = 1 - s := by
  apply Complex.ext
  · norm_num [hs]
  · simp

theorem star_iteratedDeriv_burnolBoundaryPairingSource_eq_direct
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hs : s.re = 1 / 2) :
    conj (iteratedDeriv k (burnolBoundaryPairingSource theta) s) =
      (-1 : ℂ) ^ k *
        iteratedDeriv k (burnolDirectPairingSource theta) s := by
  rw [burnolBoundaryPairingSource_eq_direct_one_sub]
  rw [congrFun
    (iteratedDeriv_comp_const_sub k (burnolDirectPairingSource theta) 1) s]
  simp only [smul_eq_mul, map_mul, map_pow, map_neg, map_one]
  rw [← conj_eq_one_sub_of_re_eq_half hs,
    star_iteratedDeriv_burnolDirectPairingSource_conj]

theorem inner_burnolY_normalizedModelKernel
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) (hs : s.re = 1 / 2) :
    inner (𝕜 := ℂ) (burnolY lambda s k)
        (burnolNormalizedModelKernelL2 theta) =
      (-1 : ℂ) ^ k *
        iteratedDeriv k (burnolDirectPairingSource theta) s := by
  calc
    inner (𝕜 := ℂ) (burnolY lambda s k)
        (burnolNormalizedModelKernelL2 theta) =
        star (inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
          (burnolY lambda s k)) :=
      (inner_conj_symm (burnolY lambda s k)
        (burnolNormalizedModelKernelL2 theta)).symm
    _ = star (iteratedDeriv k (burnolBoundaryPairingSource theta) s) := by
      rw [inner_normalizedModelKernel_burnolY_eq_iteratedDeriv
        hlambda0 hlambda1 theta s k hlambdaTheta hs]
    _ = (-1 : ℂ) ^ k *
        iteratedDeriv k (burnolDirectPairingSource theta) s :=
      star_iteratedDeriv_burnolBoundaryPairingSource_eq_direct theta s k hs

theorem inner_normalizedModelKernel_burnolY_eq_zero_of_order
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) (hs : s.re = 1 / 2)
    (horder : (k + 1 : ℕ∞) ≤ analyticOrderAt riemannZeta s) :
    inner (𝕜 := ℂ) (burnolNormalizedModelKernelL2 theta)
        (burnolY lambda s k) = 0 := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  rw [inner_normalizedModelKernel_burnolY_eq_iteratedDeriv
      hlambda0 hlambda1 theta s k hlambdaTheta hs,
    iteratedDeriv_burnolBoundaryPairingSource_eq_zero_of_order
      theta s k hs0 hs1 horder]

theorem inner_modelKernel_burnolY_eq_zero_of_order
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (theta : burnolContinuousParameter) (s : ℂ) (k : ℕ)
    (hlambdaTheta : lambda ≤ (theta : ℝ)) (hs : s.re = 1 / 2)
    (horder : (k + 1 : ℕ∞) ≤ analyticOrderAt riemannZeta s) :
    inner (𝕜 := ℂ) (burnolModelKernelL2 theta)
        (burnolY lambda s k) = 0 := by
  rw [← burnolModelKernelL2_eq_sqrt_smul_normalized theta,
    inner_smul_left,
    inner_normalizedModelKernel_burnolY_eq_zero_of_order
      hlambda0 hlambda1 theta s k hlambdaTheta hs horder,
    mul_zero]

theorem burnolY_mem_modelKernelSpan_orthogonal
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs : s.re = 1 / 2)
    (_hzeta : riemannZeta s = 0)
    (horder : (k + 1 : ℕ∞) ≤ analyticOrderAt riemannZeta s) :
    burnolY lambda s k ∈ (burnolModelKernelSpan lambda)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction
    (p := fun u _ => inner (𝕜 := ℂ) u (burnolY lambda s k) = 0)
    ?gen ?zero ?add ?smul hu
  · rintro _ ⟨theta, htheta, rfl⟩
    exact inner_modelKernel_burnolY_eq_zero_of_order
      hlambda0 hlambda1 theta s k htheta hs horder
  · simp
  · intro x y hx hy hx0 hy0
    simp [inner_add_left, hx0, hy0]
  · intro c x hx hx0
    simp [inner_smul_left, hx0]

theorem burnolAPhaseL2_burnolY
    (lambda : ℝ) (s : ℂ) (k : ℕ) :
    burnolAPhaseL2 (burnolY lambda s k) = burnolYTransformedL2 lambda s k := by
  rw [burnolY, burnolAPhaseL2.apply_symm_apply]

theorem burnolAPhaseL2_burnolY_coeFn
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    burnolAPhaseL2 (burnolY lambda s k) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolYTransformed lambda s k := by
  rw [burnolAPhaseL2_burnolY]
  exact burnolYTransformedL2_coeFn hlambda0 hlambda1 s k hs0 hs1

theorem burnolYTransformed_eq_zero_of_lt
    {lambda t : ℝ} (hlt : t < lambda) (s : ℂ) (k : ℕ) :
    burnolYTransformed lambda s k t = 0 := by
  rw [burnolYTransformed, Set.indicator_of_notMem]
  exact fun ht => (not_le_of_gt hlt) ht

theorem norm_burnolYTransformed_sub_gammaMain_le
    {lambda t : ℝ} (hlambdaT : lambda ≤ t)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolYTransformed lambda s k t -
        iteratedDeriv k (burnolPhiHardyGammaMain t) s‖ ≤
      4 * burnolPhiSeriesBound k := by
  rw [burnolYTransformed,
    Set.indicator_of_mem (show t ∈ Ici lambda from hlambdaT)]
  exact norm_burnolHardySquareDifference_phi_sub_gammaMain_le
    s k hs0 hs1 ht0 ht1

theorem norm_burnolYTransformed_sub_V_cpow_le
    {lambda t : ℝ} (hlambdaT : lambda ≤ t)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolYTransformed lambda s k t -
        iteratedDeriv k
          (fun z : ℂ => burnolVSpectral z * (t : ℂ) ^ (-z)) s‖ ≤
      4 * burnolPhiSeriesBound k := by
  rw [← iteratedDeriv_burnolPhiHardyGammaMain_eq_V_cpow
    k ht0 hs0 hs1]
  exact norm_burnolYTransformed_sub_gammaMain_le
    hlambdaT s k hs0 hs1 ht0 ht1

theorem norm_burnolYTransformed_le_large
    {lambda t : ℝ} (hlambda1 : lambda ≤ 1)
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (ht : 1 ≤ t) :
    ‖burnolYTransformed lambda s k t‖ ≤
      burnolPhiHardySquareLargeCoeff s k *
        (1 + |Real.log t|) ^ 2 / t := by
  have hlambdaT : lambda ≤ t := hlambda1.trans ht
  rw [burnolYTransformed,
    Set.indicator_of_mem (show t ∈ Ici lambda from hlambdaT),
    abs_of_nonneg (Real.log_nonneg ht)]
  exact norm_burnolHardySquareDifference_phi_le_large s k hs0 hs1 ht

end LeanLab.Riemann
