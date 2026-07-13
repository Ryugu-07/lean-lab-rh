import LeanLab.Riemann.BurnolY
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

set_option linter.style.header false

/-!
# Burnol's finite-dimensional asymptotics

This file formalizes the normalized boundary vectors, their Gram and target-pairing limits, and
the finite Hilbert/Cauchy matrix calculation used in Burnol's lower bound.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal FourierTransform InnerProductSpace Real Topology

namespace LeanLab.Riemann

/-- The positive logarithmic scale in Burnol's normalization. -/
def burnolLogScale (lambda : ℝ) : ℝ :=
  Real.log lambda⁻¹

theorem burnolLogScale_eq_neg_log (lambda : ℝ) :
    burnolLogScale lambda = -Real.log lambda := by
  rw [burnolLogScale, Real.log_inv]

theorem burnolLogScale_pos {lambda : ℝ} (hlambda0 : 0 < lambda)
    (hlambda1 : lambda < 1) :
    0 < burnolLogScale lambda := by
  rw [burnolLogScale]
  exact Real.log_pos ((one_lt_inv₀ hlambda0).2 hlambda1)

theorem tendsto_burnolLogScale_nhdsGT_zero :
    Tendsto burnolLogScale (𝓝[>] (0 : ℝ)) atTop := by
  exact Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

/-- Burnol's logarithmically normalized boundary vector. -/
def burnolX (lambda : ℝ) (s : ℂ) (k : ℕ) : positiveHalfLineComplexL2 :=
  (((burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) •
    burnolY lambda s k

theorem burnolAPhaseL2_burnolX (lambda : ℝ) (s : ℂ) (k : ℕ) :
    burnolAPhaseL2 (burnolX lambda s k) =
      (((burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) •
        burnolYTransformedL2 lambda s k := by
  rw [burnolX, map_smul, burnolAPhaseL2_burnolY]

theorem tendsto_burnolLogScale_rpow_neg
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun lambda : ℝ => (burnolLogScale lambda) ^ (-a))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp tendsto_burnolLogScale_nhdsGT_zero

theorem tendsto_burnolLogScale_inv :
    Tendsto (fun lambda : ℝ => (burnolLogScale lambda)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_burnolLogScale_nhdsGT_zero.inv_tendsto_atTop

theorem eventually_burnolLogScale_pos :
    ∀ᶠ lambda : ℝ in 𝓝[>] (0 : ℝ), 0 < burnolLogScale lambda := by
  have hlt : ∀ᶠ lambda : ℝ in 𝓝[>] (0 : ℝ), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hlt] with lambda hlambda0 hlambda1
  exact burnolLogScale_pos hlambda0 hlambda1

theorem continuous_burnolVSpectral_on_criticalLine :
    Continuous (fun xi : ℝ =>
      burnolVSpectral (burnolCriticalLineAtFrequency xi)) := by
  rw [continuous_iff_continuousAt]
  intro xi
  have hsMem : burnolCriticalLineAtFrequency xi ∈ burnolOpenCriticalStrip := by
    constructor <;> norm_num [burnolCriticalLineAtFrequency]
  have hV : ContinuousAt burnolVSpectral
      (burnolCriticalLineAtFrequency xi) :=
    ((differentiableOn_burnolVSpectral _ hsMem).differentiableAt
      (isOpen_burnolOpenCriticalStrip.mem_nhds hsMem)).continuousAt
  exact hV.comp continuous_burnolCriticalLineAtFrequency.continuousAt

theorem norm_burnolVSpectral_criticalLine (xi : ℝ) :
    ‖burnolVSpectral (burnolCriticalLineAtFrequency xi)‖ = 1 := by
  have hae : (fun eta : ℝ =>
      ‖burnolVSpectral (burnolCriticalLineAtFrequency eta)‖) =ᵐ[volume]
        fun _ : ℝ => 1 := by
    filter_upwards [ae_burnolVSpectral_critical_eq_APhaseMultiplier] with eta heta
    rw [heta, norm_burnolAPhaseMultiplier]
  have hEq := Measure.eq_of_ae_eq hae
    continuous_burnolVSpectral_on_criticalLine.norm continuous_const
  exact congrFun hEq xi

theorem norm_burnolVSpectral_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    ‖burnolVSpectral s‖ = 1 := by
  let xi : ℝ := s.im / (2 * Real.pi)
  have hxi : 2 * Real.pi * xi = s.im := by
    dsimp only [xi]
    field_simp [Real.pi_ne_zero]
  have hparam : s = burnolCriticalLineAtFrequency xi := by
    apply Complex.ext
    · norm_num [burnolCriticalLineAtFrequency, hs]
    · simpa [burnolCriticalLineAtFrequency] using hxi.symm
  rw [hparam, norm_burnolVSpectral_criticalLine]

/-! ## Truncated logarithmic moments -/

theorem hasDerivAt_neg_negLog_pow_div (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => -((-Real.log y) ^ (n + 1)) / (n + 1 : ℝ))
      ((-Real.log x) ^ n / x) x := by
  have hlog : HasDerivAt (fun y : ℝ => -Real.log y) (-x⁻¹) x :=
    (Real.hasDerivAt_log hx.ne').neg
  have hpow := (hlog.pow (n + 1)).neg.div_const (n + 1 : ℝ)
  simp only [Pi.neg_apply, Pi.pow_apply] at hpow
  have hcoeff :
      -(↑(n + 1) * (-Real.log x) ^ (n + 1 - 1) * -x⁻¹) / (↑n + 1) =
        (-Real.log x) ^ n / x := by
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp [hx.ne']
  rw [hcoeff] at hpow
  exact hpow

theorem integral_Ioc_negLog_pow_div
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (n : ℕ) :
    (∫ t : ℝ in Ioc lambda 1, (-Real.log t) ^ n / t) =
      (burnolLogScale lambda) ^ (n + 1) / (n + 1 : ℝ) := by
  let F : ℝ → ℝ := fun t =>
    -((-Real.log t) ^ (n + 1)) / (n + 1 : ℝ)
  let f : ℝ → ℝ := fun t => (-Real.log t) ^ n / t
  have hcontinuous : ContinuousOn f (Icc lambda 1) := by
    intro t ht
    have ht0 : 0 < t := hlambda0.trans_le ht.1
    exact (((Real.continuousAt_log ht0.ne').neg.pow n).div
      continuousAt_id ht0.ne').continuousWithinAt
  have hintegrable : IntervalIntegrable f volume lambda 1 :=
    hcontinuous.intervalIntegrable_of_Icc hlambda1.le
  have hderiv : ∀ t ∈ uIcc lambda 1, HasDerivAt F (f t) t := by
    intro t ht
    rw [uIcc_of_le hlambda1.le] at ht
    exact hasDerivAt_neg_negLog_pow_div n (hlambda0.trans_le ht.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable
  rw [← intervalIntegral.integral_of_le hlambda1.le, hFTC]
  have hn : 0 < n + 1 := by omega
  dsimp only [F, f]
  rw [Real.log_one, neg_zero, zero_pow hn.ne']
  rw [burnolLogScale_eq_neg_log]
  ring

theorem integral_Ioc_negLog_pow_div_complex
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (n : ℕ) :
    (∫ t : ℝ in Ioc lambda 1, (((-Real.log t) ^ n / t : ℝ) : ℂ)) =
      (((burnolLogScale lambda) ^ (n + 1) / (n + 1 : ℝ) : ℝ) : ℂ) := by
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (integral_Ioc_negLog_pow_div hlambda0 hlambda1 n)
  calc
    (∫ t : ℝ in Ioc lambda 1, (((-Real.log t) ^ n / t : ℝ) : ℂ)) =
        ((∫ t : ℝ in Ioc lambda 1, (-Real.log t) ^ n / t : ℝ) : ℂ) :=
      integral_complex_ofReal
    _ = _ := h

theorem burnolCriticalCpow_mul_conj
    {s : ℂ} (hs : s.re = 1 / 2) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-s) * conj ((t : ℂ) ^ (-s)) = ((t⁻¹ : ℝ) : ℂ) := by
  rw [Complex.mul_conj', Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.neg_re, hs]
  norm_num
  norm_cast
  rw [← Real.rpow_mul_natCast ht.le]
  norm_num
  rw [Real.rpow_neg_one]

theorem integral_Ioc_criticalLogMoment
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ) :
    (∫ t : ℝ in Ioc lambda 1,
      ((-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-s)) *
        conj ((t : ℂ) ^ (-s))) =
      (((burnolLogScale lambda) ^ (n + 1) / (n + 1 : ℝ) : ℝ) : ℂ) := by
  rw [← integral_Ioc_negLog_pow_div_complex hlambda0 hlambda1 n]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [mul_assoc, burnolCriticalCpow_mul_conj hs (hlambda0.trans ht.1)]
  push_cast
  rw [div_eq_mul_inv]

theorem tendsto_normalized_integral_Ioc_criticalLogMoment
    {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (n + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-s)) *
            conj ((t : ℂ) ^ (-s))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have heq : (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (n + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-s)) *
            conj ((t : ℂ) ^ (-s)))) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      fun _ : ℝ => ((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne] with
        lambda hlambda0 hlambda1
    rw [integral_Ioc_criticalLogMoment hlambda0 hlambda1 hs n]
    have hscaleNe : burnolLogScale lambda ≠ 0 :=
      (burnolLogScale_pos hlambda0 hlambda1).ne'
    push_cast
    field_simp [hscaleNe]
  exact tendsto_const_nhds.congr' heq.symm

/-! ## Oscillatory logarithmic moments -/

/-- A primitive for `(-log t)^n * t^(-a-1)` when `a != 0`. -/
def burnolOscillatoryPrimitive (a : ℂ) : ℕ → ℝ → ℂ
  | 0, t => -a⁻¹ * (t : ℂ) ^ (-a)
  | n + 1, t =>
      -a⁻¹ * ((-(Real.log t : ℂ)) ^ (n + 1) * (t : ℂ) ^ (-a)) -
        ((n + 1 : ℕ) : ℂ) * a⁻¹ * burnolOscillatoryPrimitive a n t

theorem hasDerivAt_complex_negLog {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (-(Real.log x : ℂ)))
      (((-t⁻¹ : ℝ) : ℂ)) t := by
  have hlogReal : HasDerivAt (fun x : ℝ => -Real.log x) (-t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').neg
  have hraw := Complex.ofRealCLM.hasDerivAt.scomp t hlogReal
  have heq : (Complex.ofRealCLM ∘ fun x : ℝ => -Real.log x) =ᶠ[𝓝 t]
      fun x : ℝ => (-(Real.log x : ℂ)) :=
    Filter.Eventually.of_forall fun x => by simp
  have h := hraw.congr_of_eventuallyEq heq.symm
  simpa only [Complex.real_smul, Complex.ofReal_neg,
    Complex.ofReal_inv, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using h

theorem ofReal_inv_mul_cpow_neg_eq_cpow_neg_sub_one
    (a : ℂ) {t : ℝ} (ht : 0 < t) :
    ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ (-a) = (t : ℂ) ^ (-a - 1) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  calc
    ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ (-a) =
        (t : ℂ)⁻¹ * (t : ℂ) ^ (-a) := by push_cast; rfl
    _ = (t : ℂ) ^ (-1 : ℂ) * (t : ℂ) ^ (-a) := by
      rw [Complex.cpow_neg_one]
    _ = (t : ℂ) ^ ((-1 : ℂ) + -a) :=
      (Complex.cpow_add _ _ htC).symm
    _ = (t : ℂ) ^ (-a - 1) := by
      congr 1
      ring

theorem hasDerivAt_burnolOscillatoryPrimitive
    {a : ℂ} (ha : a ≠ 0) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (burnolOscillatoryPrimitive a n)
      ((-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1)) t := by
  induction n with
  | zero =>
      have hcpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-a))
          ((-a) * (t : ℂ) ^ (-a - 1)) t :=
        hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr ha)
      have hbase := hcpow.const_mul (-a⁻¹)
      have hcoeff : -a⁻¹ * ((-a) * (t : ℂ) ^ (-a - 1)) =
          (t : ℂ) ^ (-a - 1) := by
        field_simp [ha]
      rw [hcoeff] at hbase
      simpa only [burnolOscillatoryPrimitive, pow_zero, one_mul] using hbase
  | succ n ih =>
      have hlogComplex := hasDerivAt_complex_negLog ht
      have hcpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-a))
          ((-a) * (t : ℂ) ^ (-a - 1)) t :=
        hasDerivAt_ofReal_cpow_const ht.ne' (neg_ne_zero.mpr ha)
      let main : ℝ → ℂ := fun x =>
        (-(Real.log x : ℂ)) ^ (n + 1) * (x : ℂ) ^ (-a)
      have hmainRaw := (hlogComplex.pow (n + 1)).mul hcpow
      have hmainEq :
          ((fun x : ℝ => (-(Real.log x : ℂ))) ^ (n + 1) *
            fun x : ℝ => (x : ℂ) ^ (-a)) =ᶠ[𝓝 t] main :=
        Filter.Eventually.of_forall fun x => by rfl
      have hmain := hmainRaw.congr_of_eventuallyEq hmainEq.symm
      have hderiv := (hmain.const_mul (-a⁻¹)).sub
        (ih.const_mul (((n + 1 : ℕ) : ℂ) * a⁻¹))
      let D : ℂ :=
        -a⁻¹ *
              (((n + 1 : ℕ) : ℂ) *
                  (-(Real.log t : ℂ)) ^ n * ((-t⁻¹ : ℝ) : ℂ) *
                  (t : ℂ) ^ (-a) +
                (-(Real.log t : ℂ)) ^ (n + 1) *
                  ((-a) * (t : ℂ) ^ (-a - 1))) -
          (((n + 1 : ℕ) : ℂ) * a⁻¹) *
            ((-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1))
      have hfun :
          ((fun x : ℝ => -a⁻¹ * main x) -
            fun x : ℝ => (((n + 1 : ℕ) : ℂ) * a⁻¹) *
              burnolOscillatoryPrimitive a n x) =ᶠ[𝓝 t]
            burnolOscillatoryPrimitive a (n + 1) :=
        Filter.Eventually.of_forall fun x => by
          simp only [Pi.sub_apply, burnolOscillatoryPrimitive, main]
      have hderiv' : HasDerivAt (burnolOscillatoryPrimitive a (n + 1)) D t := by
        have h := hderiv.congr_of_eventuallyEq hfun.symm
        simpa only [D, main, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply,
          Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using h
      have hminus : ((-t⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ (-a) =
          -(t : ℂ) ^ (-a - 1) := by
        calc
          ((-t⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ (-a) =
              -(((t⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ (-a)) := by push_cast; ring
          _ = -(t : ℂ) ^ (-a - 1) := by
            rw [ofReal_inv_mul_cpow_neg_eq_cpow_neg_sub_one a ht]
      have hD : D =
          (-(Real.log t : ℂ)) ^ (n + 1) * (t : ℂ) ^ (-a - 1) := by
        dsimp only [D]
        rw [mul_assoc (((n + 1 : ℕ) : ℂ) *
          (-(Real.log t : ℂ)) ^ n) (((-t⁻¹ : ℝ) : ℂ))
            ((t : ℂ) ^ (-a)), hminus]
        field_simp [ha]
        ring
      rw [hD] at hderiv'
      exact hderiv'

theorem integral_Ioc_oscillatoryLogMoment_eq_primitive_sub
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {a : ℂ} (ha : a ≠ 0) (n : ℕ) :
    (∫ t : ℝ in Ioc lambda 1,
      (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1)) =
      burnolOscillatoryPrimitive a n 1 -
        burnolOscillatoryPrimitive a n lambda := by
  let f : ℝ → ℂ := fun t =>
    (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1)
  have hcontinuous : ContinuousOn f (Icc lambda 1) := by
    intro t ht
    have ht0 : 0 < t := hlambda0.trans_le ht.1
    dsimp only [f]
    change ContinuousWithinAt
      (((fun x : ℝ => (-(Real.log x : ℂ))) ^ n) *
        fun x : ℝ => (x : ℂ) ^ (-a - 1)) (Icc lambda 1) t
    exact (((hasDerivAt_complex_negLog ht0).continuousAt.pow n).mul
        (Complex.continuousAt_ofReal_cpow_const t (-a - 1)
          (Or.inr ht0.ne'))).continuousWithinAt
  have hintegrable : IntervalIntegrable f volume lambda 1 :=
    hcontinuous.intervalIntegrable_of_Icc hlambda1.le
  have hderiv : ∀ t ∈ uIcc lambda 1,
      HasDerivAt (burnolOscillatoryPrimitive a n) (f t) t := by
    intro t ht
    rw [uIcc_of_le hlambda1.le] at ht
    exact hasDerivAt_burnolOscillatoryPrimitive ha n
      (hlambda0.trans_le ht.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hintegrable
  rw [← intervalIntegral.integral_of_le hlambda1.le, hFTC]

def burnolOscillatoryPrimitiveCoeff (a : ℂ) : ℕ → ℝ
  | 0 => ‖a⁻¹‖
  | n + 1 => ‖a⁻¹‖ + (n + 1 : ℝ) * ‖a⁻¹‖ *
      burnolOscillatoryPrimitiveCoeff a n

theorem burnolOscillatoryPrimitiveCoeff_nonneg (a : ℂ) (n : ℕ) :
    0 ≤ burnolOscillatoryPrimitiveCoeff a n := by
  induction n with
  | zero => exact norm_nonneg _
  | succ n ih =>
      rw [burnolOscillatoryPrimitiveCoeff]
      positivity

theorem norm_cpow_neg_eq_one_of_re_eq_zero
    {a : ℂ} (haRe : a.re = 0) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (-a)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re, haRe]
  norm_num

theorem norm_negLogComplex_pow
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    ‖(-(Real.log t : ℂ)) ^ n‖ = (-Real.log t) ^ n := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
  rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos hlog]

theorem norm_burnolOscillatoryPrimitive_le
    {a : ℂ} (haRe : a.re = 0) (n : ℕ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖burnolOscillatoryPrimitive a n t‖ ≤
      burnolOscillatoryPrimitiveCoeff a n *
        (1 + -Real.log t) ^ n := by
  have hlog : 0 ≤ -Real.log t :=
    neg_nonneg.mpr (Real.log_nonpos ht0.le ht1)
  induction n with
  | zero =>
      rw [burnolOscillatoryPrimitive, burnolOscillatoryPrimitiveCoeff,
        pow_zero, mul_one, norm_mul, norm_neg,
        norm_cpow_neg_eq_one_of_re_eq_zero haRe ht0, mul_one]
  | succ n ih =>
      have hbase : 1 ≤ 1 + -Real.log t := by linarith
      have hpow : (1 + -Real.log t) ^ n ≤
          (1 + -Real.log t) ^ (n + 1) :=
        pow_le_pow_right₀ hbase (Nat.le_succ n)
      have hlog_le : -Real.log t ≤ 1 + -Real.log t := by linarith
      rw [burnolOscillatoryPrimitive, burnolOscillatoryPrimitiveCoeff]
      calc
        ‖-a⁻¹ *
              ((-(Real.log t : ℂ)) ^ (n + 1) * (t : ℂ) ^ (-a)) -
            ((n + 1 : ℕ) : ℂ) * a⁻¹ *
              burnolOscillatoryPrimitive a n t‖ ≤
            ‖-a⁻¹ *
              ((-(Real.log t : ℂ)) ^ (n + 1) * (t : ℂ) ^ (-a))‖ +
              ‖((n + 1 : ℕ) : ℂ) * a⁻¹ *
                burnolOscillatoryPrimitive a n t‖ := norm_sub_le _ _
        _ = ‖a⁻¹‖ * (-Real.log t) ^ (n + 1) +
              (n + 1 : ℝ) * ‖a⁻¹‖ *
                ‖burnolOscillatoryPrimitive a n t‖ := by
          rw [norm_mul, norm_neg, norm_mul,
            norm_negLogComplex_pow ht0 ht1,
            norm_cpow_neg_eq_one_of_re_eq_zero haRe ht0,
            mul_one, norm_mul, norm_mul, Complex.norm_natCast]
          norm_cast
        _ ≤ ‖a⁻¹‖ * (1 + -Real.log t) ^ (n + 1) +
              (n + 1 : ℝ) * ‖a⁻¹‖ *
                (burnolOscillatoryPrimitiveCoeff a n *
                  (1 + -Real.log t) ^ n) := by
          gcongr
        _ ≤ ‖a⁻¹‖ * (1 + -Real.log t) ^ (n + 1) +
              (n + 1 : ℝ) * ‖a⁻¹‖ *
                (burnolOscillatoryPrimitiveCoeff a n *
                  (1 + -Real.log t) ^ (n + 1)) := by
          gcongr
          exact burnolOscillatoryPrimitiveCoeff_nonneg a n
        _ = (‖a⁻¹‖ + (n + 1 : ℝ) * ‖a⁻¹‖ *
              burnolOscillatoryPrimitiveCoeff a n) *
                (1 + -Real.log t) ^ (n + 1) := by ring

theorem norm_integral_Ioc_oscillatoryLogMoment_le
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {a : ℂ} (ha : a ≠ 0) (haRe : a.re = 0) (n : ℕ) :
    ‖∫ t : ℝ in Ioc lambda 1,
      (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1)‖ ≤
      2 * burnolOscillatoryPrimitiveCoeff a n *
        (1 + burnolLogScale lambda) ^ n := by
  rw [integral_Ioc_oscillatoryLogMoment_eq_primitive_sub
    hlambda0 hlambda1 ha n]
  have hone := norm_burnolOscillatoryPrimitive_le haRe n one_pos le_rfl
  have hlambda := norm_burnolOscillatoryPrimitive_le haRe n hlambda0 hlambda1.le
  rw [burnolLogScale_eq_neg_log]
  calc
    ‖burnolOscillatoryPrimitive a n 1 -
        burnolOscillatoryPrimitive a n lambda‖ ≤
      ‖burnolOscillatoryPrimitive a n 1‖ +
        ‖burnolOscillatoryPrimitive a n lambda‖ := norm_sub_le _ _
    _ ≤ burnolOscillatoryPrimitiveCoeff a n * (1 + -Real.log 1) ^ n +
        burnolOscillatoryPrimitiveCoeff a n *
          (1 + -Real.log lambda) ^ n := add_le_add hone hlambda
    _ ≤ 2 * burnolOscillatoryPrimitiveCoeff a n *
        (1 + -Real.log lambda) ^ n := by
      have hlog : 0 ≤ -Real.log lambda :=
        neg_nonneg.mpr (Real.log_nonpos hlambda0.le hlambda1.le)
      rw [Real.log_one, neg_zero, add_zero, one_pow]
      have hpow : 1 ≤ (1 + -Real.log lambda) ^ n :=
        one_le_pow₀ (by linarith)
      nlinarith [burnolOscillatoryPrimitiveCoeff_nonneg a n]

theorem tendsto_normalized_integral_Ioc_oscillatoryLogMoment
    {a : ℂ} (ha : a ≠ 0) (haRe : a.re = 0) (n : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (n + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let C : ℝ := 2 * burnolOscillatoryPrimitiveCoeff a n * (2 : ℝ) ^ n
  have hmajor : Tendsto (fun lambda : ℝ => C * (burnolLogScale lambda)⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [mul_zero] using tendsto_burnolLogScale_inv.const_mul C
  have hscaleOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      1 ≤ burnolLogScale lambda :=
    tendsto_atTop.1 tendsto_burnolLogScale_nhdsGT_zero 1
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have hbound : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ‖((((burnolLogScale lambda) ^ (n + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioc lambda 1,
            (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1))‖ ≤
        C * (burnolLogScale lambda)⁻¹ := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne, hscaleOne] with
        lambda hlambda0 hlambda1 hscaleOne
    have hscalePos : 0 < burnolLogScale lambda :=
      burnolLogScale_pos hlambda0 hlambda1
    have hscalePowNonneg :
        0 ≤ ((burnolLogScale lambda) ^ (n + 1))⁻¹ :=
      inv_nonneg.mpr (pow_nonneg hscalePos.le _)
    have hsumPow :
        (1 + burnolLogScale lambda) ^ n ≤
          (2 * burnolLogScale lambda) ^ n := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hscalePowNonneg]
    calc
      ((burnolLogScale lambda) ^ (n + 1))⁻¹ *
          ‖∫ t : ℝ in Ioc lambda 1,
            (-(Real.log t : ℂ)) ^ n * (t : ℂ) ^ (-a - 1)‖ ≤
          ((burnolLogScale lambda) ^ (n + 1))⁻¹ *
            (2 * burnolOscillatoryPrimitiveCoeff a n *
              (1 + burnolLogScale lambda) ^ n) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_Ioc_oscillatoryLogMoment_le
            hlambda0 hlambda1 ha haRe n)
          hscalePowNonneg
      _ ≤ ((burnolLogScale lambda) ^ (n + 1))⁻¹ *
            (2 * burnolOscillatoryPrimitiveCoeff a n *
              (2 * burnolLogScale lambda) ^ n) := by
        gcongr
        exact mul_nonneg (by norm_num)
          (burnolOscillatoryPrimitiveCoeff_nonneg a n)
      _ = C * (burnolLogScale lambda)⁻¹ := by
        dsimp only [C]
        rw [mul_pow]
        field_simp [hscalePos.ne']
        ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun lambda => norm_nonneg _)
    hbound hmajor

theorem criticalCpow_mul_conj_eq_oscillatory
    {s₁ s₂ : ℂ} (hs₂ : s₂.re = 1 / 2)
    {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (-s₁) * conj ((t : ℂ) ^ (-s₂)) =
      (t : ℂ) ^ (-(s₁ - s₂) - 1) := by
  have harg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  have hconj : conj ((t : ℂ) ^ (-s₂)) =
      (t : ℂ) ^ (-conj s₂) := by
    simpa using (Complex.cpow_conj (t : ℂ) (-s₂) harg).symm
  rw [hconj, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
  rw [conj_eq_one_sub_of_re_eq_half hs₂]
  congr 1
  ring

theorem criticalLogMonomial_mul_conj_eq_oscillatory
    {s₁ s₂ : ℂ} (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) {t : ℝ} (ht : 0 < t) :
    ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
        conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)) =
      (-(Real.log t : ℂ)) ^ (k + l) *
        (t : ℂ) ^ (-(s₁ - s₂) - 1) := by
  rw [map_mul, map_pow, map_neg, Complex.conj_ofReal]
  calc
    (-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁) *
        ((-(Real.log t : ℂ)) ^ l * conj ((t : ℂ) ^ (-s₂))) =
      ((-(Real.log t : ℂ)) ^ k * (-(Real.log t : ℂ)) ^ l) *
        ((t : ℂ) ^ (-s₁) * conj ((t : ℂ) ^ (-s₂))) := by ring
    _ = _ := by
      rw [← pow_add, criticalCpow_mul_conj_eq_oscillatory hs₂ ht]

theorem tendsto_normalized_integral_Ioc_distinctCriticalLogMonomial
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (hne : s₁ ≠ s₂) (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have ha : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hne
  have haRe : (s₁ - s₂).re = 0 := by
    simp only [Complex.sub_re, hs₁, hs₂]
    ring
  have hbase := tendsto_normalized_integral_Ioc_oscillatoryLogMoment
    ha haRe (k + l)
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have heq : (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)))) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      fun lambda : ℝ =>
        ((((burnolLogScale lambda) ^ ((k + l) + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioc lambda 1,
            (-(Real.log t : ℂ)) ^ (k + l) *
              (t : ℂ) ^ (-(s₁ - s₂) - 1)) := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne] with
        lambda hlambda0 hlambda1
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact criticalLogMonomial_mul_conj_eq_oscillatory
      hs₂ k l (hlambda0.trans ht.1)
  exact hbase.congr' heq.symm

theorem tendsto_normalized_integral_Ioc_sameCriticalLogMonomial
    {s : ℂ} (hs : s.re = 1 / 2) (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
  have hbase := tendsto_normalized_integral_Ioc_criticalLogMoment
    hs (k + l)
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have heq : (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s)))) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      fun lambda : ℝ =>
        ((((burnolLogScale lambda) ^ ((k + l) + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioc lambda 1,
            ((-(Real.log t : ℂ)) ^ (k + l) * (t : ℂ) ^ (-s)) *
              conj ((t : ℂ) ^ (-s))) := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne] with
        lambda hlambda0 hlambda1
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [map_mul, map_pow, map_neg, Complex.conj_ofReal]
    ring_nf
  exact hbase.congr' heq.symm

theorem tendsto_normalized_integral_Ioc_criticalLogMonomial
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) := by
  by_cases h : s₁ = s₂
  · subst s₂
    simpa using tendsto_normalized_integral_Ioc_sameCriticalLogMonomial
      hs₁ k l
  · simpa [h] using tendsto_normalized_integral_Ioc_distinctCriticalLogMonomial
      hs₁ hs₂ h k l

theorem tendsto_moreNormalized_integral_Ioc_criticalLogMonomial
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l d : ℕ) (hd : 0 < d) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + d + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hfactor : Tendsto (fun lambda : ℝ =>
      (((burnolLogScale lambda) ^ d)⁻¹))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [inv_pow, zero_pow hd.ne'] using
      tendsto_burnolLogScale_inv.pow d
  have hbase := tendsto_normalized_integral_Ioc_criticalLogMonomial
    hs₁ hs₂ k l
  have hprod : Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ d)⁻¹ : ℝ) : ℂ) *
        (((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioc lambda 1,
            ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
              conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_zero, zero_mul] using
      (hfactor.ofReal.mul hbase)
  have heq : (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + d + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
            conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)))) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      fun lambda : ℝ =>
        ((((burnolLogScale lambda) ^ d)⁻¹ : ℝ) : ℂ) *
          (((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
            (∫ t : ℝ in Ioc lambda 1,
              ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
                conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)))) := by
    filter_upwards [eventually_burnolLogScale_pos] with lambda hscale
    push_cast
    rw [show k + l + d + 1 = d + (k + l + 1) by omega, pow_add]
    field_simp [hscale.ne']
  exact hprod.congr' heq.symm

def burnolVExpansionCoeff (s : ℂ) (k i : ℕ) : ℂ :=
  (k.choose i : ℂ) * iteratedDeriv i burnolVSpectral s

theorem integrableOn_criticalLogMonomialPair_Ioc
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (s₁ s₂ : ℂ) (k l : ℕ) :
    IntegrableOn (fun t : ℝ =>
      ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
        conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)))
      (Ioc lambda 1) := by
  have hcontinuous : ContinuousOn (fun t : ℝ =>
      ((-(Real.log t : ℂ)) ^ k * (t : ℂ) ^ (-s₁)) *
        conj ((-(Real.log t : ℂ)) ^ l * (t : ℂ) ^ (-s₂)))
      (Icc lambda 1) := by
    intro t ht
    have ht0 : 0 < t := hlambda0.trans_le ht.1
    have hlog : ContinuousAt (fun x : ℝ => (-(Real.log x : ℂ))) t :=
      ((Complex.continuous_ofReal.continuousAt.comp'
        (Real.continuousAt_log ht0.ne')).neg)
    have hcpow₁ : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s₁)) t :=
      Complex.continuousAt_ofReal_cpow_const t (-s₁) (Or.inr ht0.ne')
    have hcpow₂ : ContinuousAt (fun x : ℝ => (x : ℂ) ^ (-s₂)) t :=
      Complex.continuousAt_ofReal_cpow_const t (-s₂) (Or.inr ht0.ne')
    have hleft := (hlog.pow k).mul hcpow₁
    have hright := (hlog.pow l).mul hcpow₂
    exact (hleft.mul (Complex.continuous_conj.continuousAt.comp' hright)).continuousWithinAt
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hlambda1.le]
  exact hcontinuous.intervalIntegrable_of_Icc hlambda1.le

def burnolNormalizedExpansionTerm
    (lambda : ℝ) (s₁ : ℂ) (k i : ℕ) (s₂ : ℂ) (l j : ℕ) : ℂ :=
  burnolVExpansionCoeff s₁ k i * conj (burnolVExpansionCoeff s₂ l j) *
    (((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
      (∫ t : ℝ in Ioc lambda 1,
        ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
          conj ((-(Real.log t : ℂ)) ^ (l - j) * (t : ℂ) ^ (-s₂))))

theorem tendsto_burnolNormalizedExpansionTerm
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    {k l i j : ℕ} (hi : i ≤ k) (hj : j ≤ l) :
    Tendsto (fun lambda : ℝ =>
      burnolNormalizedExpansionTerm lambda s₁ k i s₂ l j)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if i = 0 ∧ j = 0 then
        if s₁ = s₂ then
          ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)
        else 0 else 0)) := by
  by_cases htop : i = 0 ∧ j = 0
  · rcases htop with ⟨rfl, rfl⟩
    have hbase := tendsto_normalized_integral_Ioc_criticalLogMonomial
      hs₁ hs₂ k l
    by_cases heq : s₁ = s₂
    · subst s₂
      have hphase : burnolVSpectral s₁ * conj (burnolVSpectral s₁) = 1 := by
        rw [Complex.mul_conj', norm_burnolVSpectral_of_re_eq_half hs₁]
        norm_num
      simpa [burnolNormalizedExpansionTerm, burnolVExpansionCoeff,
        hphase] using
        hbase.const_mul (burnolVSpectral s₁ * conj (burnolVSpectral s₁))
    · simpa [burnolNormalizedExpansionTerm, burnolVExpansionCoeff, heq] using
        hbase.const_mul (burnolVSpectral s₁ * conj (burnolVSpectral s₂))
  · have hd : 0 < i + j := by omega
    have hexp : (k - i) + (l - j) + (i + j) + 1 = k + l + 1 := by omega
    have hbase := tendsto_moreNormalized_integral_Ioc_criticalLogMonomial
      hs₁ hs₂ (k - i) (l - j) (i + j) hd
    simpa [burnolNormalizedExpansionTerm, htop, hexp] using
      hbase.const_mul
        (burnolVExpansionCoeff s₁ k i * conj (burnolVExpansionCoeff s₂ l j))

def burnolNormalizedExpandedGram
    (lambda : ℝ) (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (k + 1),
    ∑ j ∈ Finset.range (l + 1),
      burnolNormalizedExpansionTerm lambda s₁ k i s₂ l j

theorem sum_range_sum_range_ite_zero_zero (k l : ℕ) (c : ℂ) :
    (∑ i ∈ Finset.range (k + 1),
      ∑ j ∈ Finset.range (l + 1),
        if i = 0 ∧ j = 0 then c else 0) = c := by
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hjne
      simp [hjne]
    · simp
  · intro i hi hine
    simp [hine]
  · simp

theorem tendsto_burnolNormalizedExpandedGram
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      burnolNormalizedExpandedGram lambda s₁ k s₂ l)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) := by
  have hsum := tendsto_finsetSum (Finset.range (k + 1)) fun i hi =>
    tendsto_finsetSum (Finset.range (l + 1)) fun j hj =>
      tendsto_burnolNormalizedExpansionTerm hs₁ hs₂
        (by simpa using hi) (by simpa using hj)
  by_cases heq : s₁ = s₂
  · simpa [burnolNormalizedExpandedGram, heq,
      sum_range_sum_range_ite_zero_zero] using hsum
  · simpa [burnolNormalizedExpandedGram, heq] using hsum

theorem burnolNormalizedExpandedGram_eq_gammaMainPairing
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    burnolNormalizedExpandedGram lambda s₁ k s₂ l =
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
            conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)) := by
  have hpoint : ∀ t ∈ Ioc lambda 1,
      iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
          conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂) =
        ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (l + 1),
            (burnolVExpansionCoeff s₁ k i *
                conj (burnolVExpansionCoeff s₂ l j)) *
              (((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
                conj ((-(Real.log t : ℂ)) ^ (l - j) * (t : ℂ) ^ (-s₂))) := by
    intro t ht
    have ht0 : 0 < t := hlambda0.trans ht.1
    rw [iteratedDeriv_burnolPhiHardyGammaMain_eq_sum k
        (by rw [hs₁]; norm_num) (by rw [hs₁]; norm_num) ht0,
      iteratedDeriv_burnolPhiHardyGammaMain_eq_sum l
        (by rw [hs₂]; norm_num) (by rw [hs₂]; norm_num) ht0]
    simp_rw [map_sum, map_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [burnolVExpansionCoeff, map_mul, Complex.conj_natCast]
    ring
  have htermIntegrable : ∀ i ∈ Finset.range (k + 1),
      ∀ j ∈ Finset.range (l + 1),
        Integrable (fun t : ℝ =>
          (burnolVExpansionCoeff s₁ k i *
              conj (burnolVExpansionCoeff s₂ l j)) *
            (((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
              conj ((-(Real.log t : ℂ)) ^ (l - j) * (t : ℂ) ^ (-s₂))))
          (volume.restrict (Ioc lambda 1)) := by
    intro i hi j hj
    exact (integrableOn_criticalLogMonomialPair_Ioc
      hlambda0 hlambda1 s₁ s₂ (k - i) (l - j)).const_mul _
  have hintegral :
      (∫ t : ℝ in Ioc lambda 1,
          iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
            conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)) =
        ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (l + 1),
            (burnolVExpansionCoeff s₁ k i *
                conj (burnolVExpansionCoeff s₂ l j)) *
              (∫ t : ℝ in Ioc lambda 1,
                ((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
                  conj ((-(Real.log t : ℂ)) ^ (l - j) *
                    (t : ℂ) ^ (-s₂))) := by
    calc
      (∫ t : ℝ in Ioc lambda 1,
          iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
            conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)) =
          ∫ t : ℝ in Ioc lambda 1,
            ∑ i ∈ Finset.range (k + 1),
              ∑ j ∈ Finset.range (l + 1),
                (burnolVExpansionCoeff s₁ k i *
                    conj (burnolVExpansionCoeff s₂ l j)) *
                  (((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
                    conj ((-(Real.log t : ℂ)) ^ (l - j) *
                      (t : ℂ) ^ (-s₂))) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpoint t ht
      _ = ∑ i ∈ Finset.range (k + 1),
          ∫ t : ℝ in Ioc lambda 1,
            ∑ j ∈ Finset.range (l + 1),
              (burnolVExpansionCoeff s₁ k i *
                  conj (burnolVExpansionCoeff s₂ l j)) *
                (((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
                  conj ((-(Real.log t : ℂ)) ^ (l - j) *
                    (t : ℂ) ^ (-s₂))) := by
        rw [integral_finsetSum]
        intro i hi
        exact integrable_finsetSum (Finset.range (l + 1))
          (htermIntegrable i hi)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro j hj
          rw [integral_const_mul]
        · exact htermIntegrable i hi
  rw [burnolNormalizedExpandedGram, hintegral]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [burnolNormalizedExpansionTerm]
  ring

theorem tendsto_normalized_gammaMainPairing
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
            conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) := by
  have hbase := tendsto_burnolNormalizedExpandedGram hs₁ hs₂ k l
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have heq : (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioc lambda 1,
          iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
            conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂))) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      fun lambda : ℝ => burnolNormalizedExpandedGram lambda s₁ k s₂ l := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne] with
        lambda hlambda0 hlambda1
    exact (burnolNormalizedExpandedGram_eq_gammaMainPairing
      hlambda0 hlambda1 hs₁ hs₂ k l).symm
  exact hbase.congr' heq.symm

def burnolGramErrorSmallMajor
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) (t : ℝ) : ℝ :=
  let A₁ := burnolVMainDerivCoeffBound s₁ k
  let A₂ := burnolVMainDerivCoeffBound s₂ l
  let C₁ := 4 * burnolPhiSeriesBound k
  let C₂ := 4 * burnolPhiSeriesBound l
  C₁ * (A₂ * (1 + |Real.log t|) ^ l * t ^ (-(1 / 2 : ℝ)) + C₂) +
    A₁ * (1 + |Real.log t|) ^ k * t ^ (-(1 / 2 : ℝ)) * C₂

def burnolGramErrorLargeMajor
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) (t : ℝ) : ℝ :=
  8 * burnolPhiHardySquareLargeCoeff s₁ k *
    burnolPhiHardySquareLargeCoeff s₂ l *
      (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ))

def burnolGramErrorMajor
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (burnolGramErrorSmallMajor s₁ k s₂ l) t +
    (Ioi (1 : ℝ)).indicator (burnolGramErrorLargeMajor s₁ k s₂ l) t

theorem integrableOn_burnolGramErrorMajor
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) :
    IntegrableOn (burnolGramErrorMajor s₁ k s₂ l) (Ioi (0 : ℝ)) := by
  let A₁ := burnolVMainDerivCoeffBound s₁ k
  let A₂ := burnolVMainDerivCoeffBound s₂ l
  let C₁ := 4 * burnolPhiSeriesBound k
  let C₂ := 4 * burnolPhiSeriesBound l
  let B₁ := burnolPhiHardySquareLargeCoeff s₁ k
  let B₂ := burnolPhiHardySquareLargeCoeff s₂ l
  have hk := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    k (a := -(1 / 2 : ℝ)) (by norm_num)
  have hl := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    l (a := -(1 / 2 : ℝ)) (by norm_num)
  have hsmallOn : IntegrableOn
      (burnolGramErrorSmallMajor s₁ k s₂ l) (Ioc (0 : ℝ) 1) := by
    have hlTerm := hl.const_mul (C₁ * A₂)
    have hkTerm := hk.const_mul (A₁ * C₂)
    have hconst : IntegrableOn (fun _ : ℝ => C₁ * C₂)
        (Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
    change Integrable (burnolGramErrorSmallMajor s₁ k s₂ l)
      (volume.restrict (Ioc (0 : ℝ) 1))
    exact ((hlTerm.add hconst).add hkTerm).congr <| ae_of_all _ fun t => by
      dsimp only [burnolGramErrorSmallMajor, A₁, A₂, C₁, C₂]
      simp only [Pi.add_apply]
      ring
  have hlargeOn : IntegrableOn
      (burnolGramErrorLargeMajor s₁ k s₂ l) (Ioi (1 : ℝ)) := by
    change Integrable (burnolGramErrorLargeMajor s₁ k s₂ l)
      (volume.restrict (Ioi (1 : ℝ)))
    exact (integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * B₁ * B₂)).congr <| ae_of_all _ fun t => by
        dsimp only [burnolGramErrorLargeMajor, B₁, B₂]
  have hsmall : Integrable (fun t : ℝ =>
      (Ioc (0 : ℝ) 1).indicator
        (burnolGramErrorSmallMajor s₁ k s₂ l) t) :=
    hsmallOn.integrable_indicator measurableSet_Ioc
  have hlarge : Integrable (fun t : ℝ =>
      (Ioi (1 : ℝ)).indicator
        (burnolGramErrorLargeMajor s₁ k s₂ l) t) :=
    hlargeOn.integrable_indicator measurableSet_Ioi
  exact (hsmall.add hlarge).integrableOn.congr
    (ae_of_all _ fun t => by rfl)

def burnolGammaMainCutoff
    (lambda : ℝ) (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (Icc lambda 1).indicator
    (fun u : ℝ => iteratedDeriv k (burnolPhiHardyGammaMain u) s) t

theorem burnolGramErrorSmallMajor_nonneg
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ burnolGramErrorSmallMajor s₁ k s₂ l t := by
  have hA₁ := burnolVMainDerivCoeffBound_nonneg s₁ k
  have hA₂ := burnolVMainDerivCoeffBound_nonneg s₂ l
  have hC₁ : 0 ≤ 4 * burnolPhiSeriesBound k :=
    mul_nonneg (by norm_num) (burnolPhiSeriesBound_nonneg k)
  have hC₂ : 0 ≤ 4 * burnolPhiSeriesBound l :=
    mul_nonneg (by norm_num) (burnolPhiSeriesBound_nonneg l)
  have hrpow : 0 ≤ t ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ht.le _
  dsimp only [burnolGramErrorSmallMajor]
  positivity

theorem burnolGramErrorLargeMajor_nonneg
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ burnolGramErrorLargeMajor s₁ k s₂ l t := by
  have hB₁ := burnolPhiHardySquareLargeCoeff_nonneg s₁ k
  have hB₂ := burnolPhiHardySquareLargeCoeff_nonneg s₂ l
  have hrpow : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht.le _
  dsimp only [burnolGramErrorLargeMajor]
  positivity

theorem norm_burnolYPairing_sub_gammaMainCutoffPairing_le
    {lambda t : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) (ht0 : 0 < t) :
    ‖burnolYTransformed lambda s₁ k t *
          conj (burnolYTransformed lambda s₂ l t) -
        burnolGammaMainCutoff lambda s₁ k t *
          conj (burnolGammaMainCutoff lambda s₂ l t)‖ ≤
      burnolGramErrorMajor s₁ k s₂ l t := by
  let A₁ := burnolVMainDerivCoeffBound s₁ k
  let A₂ := burnolVMainDerivCoeffBound s₂ l
  let C₁ := 4 * burnolPhiSeriesBound k
  let C₂ := 4 * burnolPhiSeriesBound l
  let B₁ := burnolPhiHardySquareLargeCoeff s₁ k
  let B₂ := burnolPhiHardySquareLargeCoeff s₂ l
  have hs₁0 : 0 < s₁.re := by rw [hs₁]; norm_num
  have hs₁1 : s₁.re < 1 := by rw [hs₁]; norm_num
  have hs₂0 : 0 < s₂.re := by rw [hs₂]; norm_num
  have hs₂1 : s₂.re < 1 := by rw [hs₂]; norm_num
  have hA₁0 : 0 ≤ A₁ := burnolVMainDerivCoeffBound_nonneg s₁ k
  have hA₂0 : 0 ≤ A₂ := burnolVMainDerivCoeffBound_nonneg s₂ l
  have hC₁0 : 0 ≤ C₁ :=
    mul_nonneg (by norm_num) (burnolPhiSeriesBound_nonneg k)
  have hC₂0 : 0 ≤ C₂ :=
    mul_nonneg (by norm_num) (burnolPhiSeriesBound_nonneg l)
  have hB₁0 : 0 ≤ B₁ := burnolPhiHardySquareLargeCoeff_nonneg s₁ k
  have hB₂0 : 0 ≤ B₂ := burnolPhiHardySquareLargeCoeff_nonneg s₂ l
  by_cases ht1 : t ≤ 1
  · have htSmall : t ∈ Ioc (0 : ℝ) 1 := ⟨ht0, ht1⟩
    have htNotLarge : t ∉ Ioi (1 : ℝ) := fun h => (not_lt_of_ge ht1) h
    rw [burnolGramErrorMajor, Set.indicator_of_mem htSmall,
      Set.indicator_of_notMem htNotLarge, add_zero]
    by_cases hlambdaT : lambda ≤ t
    · have htCutoff : t ∈ Icc lambda 1 := ⟨hlambdaT, ht1⟩
      rw [burnolGammaMainCutoff, Set.indicator_of_mem htCutoff,
        burnolGammaMainCutoff, Set.indicator_of_mem htCutoff]
      have hE₁ :
          ‖burnolYTransformed lambda s₁ k t -
            iteratedDeriv k (burnolPhiHardyGammaMain t) s₁‖ ≤ C₁ :=
        norm_burnolYTransformed_sub_gammaMain_le hlambdaT s₁ k
          hs₁0 hs₁1 ht0 ht1
      have hE₂ :
          ‖burnolYTransformed lambda s₂ l t -
            iteratedDeriv l (burnolPhiHardyGammaMain t) s₂‖ ≤ C₂ :=
        norm_burnolYTransformed_sub_gammaMain_le hlambdaT s₂ l
          hs₂0 hs₂1 ht0 ht1
      have hG₁ : ‖iteratedDeriv k (burnolPhiHardyGammaMain t) s₁‖ ≤
          A₁ * (1 + |Real.log t|) ^ k * t ^ (-(1 / 2 : ℝ)) := by
        simpa [A₁, hs₁] using
          norm_iteratedDeriv_burnolPhiHardyGammaMain_le k hs₁0 hs₁1 ht0
      have hG₂ : ‖iteratedDeriv l (burnolPhiHardyGammaMain t) s₂‖ ≤
          A₂ * (1 + |Real.log t|) ^ l * t ^ (-(1 / 2 : ℝ)) := by
        simpa [A₂, hs₂] using
          norm_iteratedDeriv_burnolPhiHardyGammaMain_le l hs₂0 hs₂1 ht0
      have hY₂ : ‖burnolYTransformed lambda s₂ l t‖ ≤
          A₂ * (1 + |Real.log t|) ^ l * t ^ (-(1 / 2 : ℝ)) + C₂ := by
        calc
          ‖burnolYTransformed lambda s₂ l t‖ ≤
              ‖burnolYTransformed lambda s₂ l t -
                iteratedDeriv l (burnolPhiHardyGammaMain t) s₂‖ +
              ‖iteratedDeriv l (burnolPhiHardyGammaMain t) s₂‖ := by
            nth_rewrite 1 [show burnolYTransformed lambda s₂ l t =
                (burnolYTransformed lambda s₂ l t -
                  iteratedDeriv l (burnolPhiHardyGammaMain t) s₂) +
                iteratedDeriv l (burnolPhiHardyGammaMain t) s₂ by ring]
            exact norm_add_le _ _
          _ ≤ C₂ +
              A₂ * (1 + |Real.log t|) ^ l * t ^ (-(1 / 2 : ℝ)) :=
            add_le_add hE₂ hG₂
          _ = _ := by ring
      have hid :
          burnolYTransformed lambda s₁ k t *
                conj (burnolYTransformed lambda s₂ l t) -
              iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
                conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂) =
            (burnolYTransformed lambda s₁ k t -
                iteratedDeriv k (burnolPhiHardyGammaMain t) s₁) *
                conj (burnolYTransformed lambda s₂ l t) +
              iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
                conj (burnolYTransformed lambda s₂ l t -
                  iteratedDeriv l (burnolPhiHardyGammaMain t) s₂) := by
        simp only [map_sub]
        ring
      rw [hid]
      calc
        ‖(burnolYTransformed lambda s₁ k t -
                iteratedDeriv k (burnolPhiHardyGammaMain t) s₁) *
                conj (burnolYTransformed lambda s₂ l t) +
              iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
                conj (burnolYTransformed lambda s₂ l t -
                  iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)‖ ≤
            ‖burnolYTransformed lambda s₁ k t -
                iteratedDeriv k (burnolPhiHardyGammaMain t) s₁‖ *
                ‖burnolYTransformed lambda s₂ l t‖ +
              ‖iteratedDeriv k (burnolPhiHardyGammaMain t) s₁‖ *
                ‖burnolYTransformed lambda s₂ l t -
                  iteratedDeriv l (burnolPhiHardyGammaMain t) s₂‖ := by
          calc
            _ ≤ ‖(burnolYTransformed lambda s₁ k t -
                    iteratedDeriv k (burnolPhiHardyGammaMain t) s₁) *
                    conj (burnolYTransformed lambda s₂ l t)‖ +
                  ‖iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
                    conj (burnolYTransformed lambda s₂ l t -
                      iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)‖ :=
                norm_add_le _ _
            _ = _ := by
              rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
        _ ≤ C₁ *
              (A₂ * (1 + |Real.log t|) ^ l * t ^ (-(1 / 2 : ℝ)) + C₂) +
            A₁ * (1 + |Real.log t|) ^ k * t ^ (-(1 / 2 : ℝ)) * C₂ := by
          gcongr
        _ = burnolGramErrorSmallMajor s₁ k s₂ l t := by
          rfl
    · have hlt : t < lambda := lt_of_not_ge hlambdaT
      have htNotCutoff : t ∉ Icc lambda 1 := fun h => hlambdaT h.1
      rw [burnolYTransformed_eq_zero_of_lt hlt s₁ k,
        burnolYTransformed_eq_zero_of_lt hlt s₂ l,
        burnolGammaMainCutoff, Set.indicator_of_notMem htNotCutoff,
        burnolGammaMainCutoff, Set.indicator_of_notMem htNotCutoff]
      simp only [mul_zero, map_zero, sub_self, norm_zero]
      exact burnolGramErrorSmallMajor_nonneg s₁ k s₂ l ht0
  · have htLarge : t ∈ Ioi (1 : ℝ) := lt_of_not_ge ht1
    have htNotSmall : t ∉ Ioc (0 : ℝ) 1 := fun h => ht1 h.2
    have htNotCutoff : t ∉ Icc lambda 1 := fun h => ht1 h.2
    rw [burnolGramErrorMajor, Set.indicator_of_notMem htNotSmall,
      Set.indicator_of_mem htLarge, zero_add,
      burnolGammaMainCutoff, Set.indicator_of_notMem htNotCutoff,
      burnolGammaMainCutoff, Set.indicator_of_notMem htNotCutoff]
    simp only [map_zero, zero_mul, sub_zero, norm_mul, Complex.norm_conj]
    have hY₁ := norm_burnolYTransformed_le_large hlambda1.le
      s₁ k hs₁0 hs₁1 htLarge.le
    have hY₂ := norm_burnolYTransformed_le_large hlambda1.le
      s₂ l hs₂0 hs₂1 htLarge.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg htLarge.le
    have hY₁' : ‖burnolYTransformed lambda s₁ k t‖ ≤
        B₁ * (1 + Real.log t) ^ 2 / t := by
      simpa [B₁, abs_of_nonneg hlog0] using hY₁
    have hY₂' : ‖burnolYTransformed lambda s₂ l t‖ ≤
        B₂ * (1 + Real.log t) ^ 2 / t := by
      simpa [B₂, abs_of_nonneg hlog0] using hY₂
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
      ‖burnolYTransformed lambda s₁ k t‖ *
          ‖burnolYTransformed lambda s₂ l t‖ ≤
        (B₁ * (1 + Real.log t) ^ 2 / t) *
          (B₂ * (1 + Real.log t) ^ 2 / t) := by
        exact mul_le_mul hY₁' hY₂' (norm_nonneg _)
          (div_nonneg (mul_nonneg hB₁0 (pow_nonneg (by linarith) _)) ht0.le)
      _ = B₁ * B₂ * (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, hinvSq.symm]
        ring
      _ ≤ B₁ * B₂ * (8 * (1 + (Real.log t) ^ 4)) *
          t ^ (-2 : ℝ) := by
        gcongr
      _ = burnolGramErrorLargeMajor s₁ k s₂ l t := by
        dsimp only [burnolGramErrorLargeMajor, B₁, B₂]
        ring

theorem burnolGramErrorMajor_nonneg
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ burnolGramErrorMajor s₁ k s₂ l t := by
  by_cases ht1 : t ≤ 1
  · rw [burnolGramErrorMajor,
      Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩),
      Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from
        fun h => (not_lt_of_ge ht1) h), add_zero]
    exact burnolGramErrorSmallMajor_nonneg s₁ k s₂ l ht
  · have htLarge : t ∈ Ioi (1 : ℝ) := lt_of_not_ge ht1
    rw [burnolGramErrorMajor,
      Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from
        fun h => ht1 h.2),
      Set.indicator_of_mem htLarge, zero_add]
    exact burnolGramErrorLargeMajor_nonneg s₁ k s₂ l ht

theorem norm_integral_burnolGramPairingError_le
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    ‖∫ t : ℝ in Ioi (0 : ℝ),
      burnolYTransformed lambda s₁ k t *
          conj (burnolYTransformed lambda s₂ l t) -
        burnolGammaMainCutoff lambda s₁ k t *
          conj (burnolGammaMainCutoff lambda s₂ l t)‖ ≤
      ∫ t : ℝ in Ioi (0 : ℝ), burnolGramErrorMajor s₁ k s₂ l t := by
  exact norm_integral_le_of_norm_le
    (integrableOn_burnolGramErrorMajor s₁ k s₂ l)
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      norm_burnolYPairing_sub_gammaMainCutoffPairing_le
        hlambda0 hlambda1 hs₁ hs₂ k l ht)

theorem tendsto_normalized_burnolGramPairingError
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        (∫ t : ℝ in Ioi (0 : ℝ),
          burnolYTransformed lambda s₁ k t *
              conj (burnolYTransformed lambda s₂ l t) -
            burnolGammaMainCutoff lambda s₁ k t *
              conj (burnolGammaMainCutoff lambda s₂ l t)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let D : ℝ := ∫ t : ℝ in Ioi (0 : ℝ),
    burnolGramErrorMajor s₁ k s₂ l t
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact integral_nonneg_of_ae <|
      (ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
        burnolGramErrorMajor_nonneg s₁ k s₂ l ht
  have hfactor : Tendsto (fun lambda : ℝ =>
      ((burnolLogScale lambda) ^ (k + l + 1))⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [inv_pow, zero_pow (show k + l + 1 ≠ 0 by omega)] using
      tendsto_burnolLogScale_inv.pow (k + l + 1)
  have hmajor : Tendsto (fun lambda : ℝ =>
      ((burnolLogScale lambda) ^ (k + l + 1))⁻¹ * D)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa only [zero_mul] using hfactor.mul_const D
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have hbound : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ‖((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioi (0 : ℝ),
            burnolYTransformed lambda s₁ k t *
                conj (burnolYTransformed lambda s₂ l t) -
              burnolGammaMainCutoff lambda s₁ k t *
                conj (burnolGammaMainCutoff lambda s₂ l t))‖ ≤
        ((burnolLogScale lambda) ^ (k + l + 1))⁻¹ * D := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne] with
        lambda hlambda0 hlambda1
    have hscale0 : 0 ≤ ((burnolLogScale lambda) ^ (k + l + 1))⁻¹ :=
      inv_nonneg.mpr (pow_nonneg (burnolLogScale_pos hlambda0 hlambda1).le _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hscale0]
    exact mul_le_mul_of_nonneg_left
      (norm_integral_burnolGramPairingError_le
        hlambda0 hlambda1 hs₁ hs₂ k l) hscale0
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun lambda => norm_nonneg _)
    hbound hmajor

theorem integral_burnolGammaMainCutoffPairing_eq
    {lambda : ℝ} (hlambda0 : 0 < lambda)
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) :
    (∫ t : ℝ in Ioi (0 : ℝ),
      burnolGammaMainCutoff lambda s₁ k t *
        conj (burnolGammaMainCutoff lambda s₂ l t)) =
      ∫ t : ℝ in Ioc lambda 1,
        iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
          conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂) := by
  let F : ℝ → ℂ := fun t =>
    iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
      conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)
  have hfun : (fun t : ℝ =>
      burnolGammaMainCutoff lambda s₁ k t *
        conj (burnolGammaMainCutoff lambda s₂ l t)) =
      (Icc lambda 1).indicator F := by
    funext t
    by_cases ht : t ∈ Icc lambda 1
    · simp [burnolGammaMainCutoff, F, ht]
    · simp [burnolGammaMainCutoff, F, ht]
  rw [hfun, setIntegral_indicator measurableSet_Icc]
  have hset : Ioi (0 : ℝ) ∩ Icc lambda 1 = Icc lambda 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Icc]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hlambda0.trans_le h.1, h⟩
  rw [hset, integral_Icc_eq_integral_Ioc]

theorem inner_burnolYTransformedL2_eq_integral
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {s₁ s₂ : ℂ} (hs₁0 : 0 < s₁.re) (hs₁1 : s₁.re < 1)
    (hs₂0 : 0 < s₂.re) (hs₂1 : s₂.re < 1) (k l : ℕ) :
    inner ℂ (burnolYTransformedL2 lambda s₂ l)
        (burnolYTransformedL2 lambda s₁ k) =
      ∫ t : ℝ in Ioi (0 : ℝ),
        burnolYTransformed lambda s₁ k t *
          conj (burnolYTransformed lambda s₂ l t) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolYTransformedL2_coeFn hlambda0 hlambda1 s₁ k hs₁0 hs₁1,
    burnolYTransformedL2_coeFn hlambda0 hlambda1 s₂ l hs₂0 hs₂1] with
      t ht₁ ht₂
  rw [ht₁, ht₂, RCLike.inner_apply]

theorem gammaMainPairing_eq_expansion
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
        conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂) =
      ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (l + 1),
          (burnolVExpansionCoeff s₁ k i *
              conj (burnolVExpansionCoeff s₂ l j)) *
            (((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
              conj ((-(Real.log t : ℂ)) ^ (l - j) * (t : ℂ) ^ (-s₂))) := by
  rw [iteratedDeriv_burnolPhiHardyGammaMain_eq_sum k
      (by rw [hs₁]; norm_num) (by rw [hs₁]; norm_num) ht,
    iteratedDeriv_burnolPhiHardyGammaMain_eq_sum l
      (by rw [hs₂]; norm_num) (by rw [hs₂]; norm_num) ht]
  simp_rw [map_sum, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [burnolVExpansionCoeff, map_mul, Complex.conj_natCast]
  ring

theorem integrableOn_gammaMainPairing_Ioc
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    IntegrableOn (fun t : ℝ =>
      iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
        conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂))
      (Ioc lambda 1) := by
  have hsum : IntegrableOn (fun t : ℝ =>
      ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (l + 1),
          (burnolVExpansionCoeff s₁ k i *
              conj (burnolVExpansionCoeff s₂ l j)) *
            (((-(Real.log t : ℂ)) ^ (k - i) * (t : ℂ) ^ (-s₁)) *
              conj ((-(Real.log t : ℂ)) ^ (l - j) * (t : ℂ) ^ (-s₂))))
      (Ioc lambda 1) := by
    exact integrable_finsetSum (Finset.range (k + 1)) fun i hi =>
      integrable_finsetSum (Finset.range (l + 1)) fun j hj =>
        (integrableOn_criticalLogMonomialPair_Ioc
          hlambda0 hlambda1 s₁ s₂ (k - i) (l - j)).const_mul _
  change Integrable (fun t : ℝ =>
      iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
        conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂))
    (volume.restrict (Ioc lambda 1))
  exact hsum.congr <| (ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
    (gammaMainPairing_eq_expansion hs₁ hs₂ k l
      (hlambda0.trans ht.1)).symm

theorem integrableOn_burnolGammaMainCutoffPairing_Ioi
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    IntegrableOn (fun t : ℝ =>
      burnolGammaMainCutoff lambda s₁ k t *
        conj (burnolGammaMainCutoff lambda s₂ l t)) (Ioi (0 : ℝ)) := by
  let F : ℝ → ℂ := fun t =>
    iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
      conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)
  have hIoc : IntegrableOn F (Ioc lambda 1) :=
    integrableOn_gammaMainPairing_Ioc hlambda0 hlambda1 hs₁ hs₂ k l
  have hIcc : IntegrableOn F (Icc lambda 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (f := F)).mpr hIoc
  have hindicator : Integrable (fun t : ℝ =>
      (Icc lambda 1).indicator F t) :=
    hIcc.integrable_indicator measurableSet_Icc
  apply hindicator.integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases hmem : t ∈ Icc lambda 1
  · simp [burnolGammaMainCutoff, F, hmem]
  · simp [burnolGammaMainCutoff, F, hmem]

theorem integrableOn_burnolYPairing_Ioi
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {s₁ s₂ : ℂ} (hs₁0 : 0 < s₁.re) (hs₁1 : s₁.re < 1)
    (hs₂0 : 0 < s₂.re) (hs₂1 : s₂.re < 1) (k l : ℕ) :
    IntegrableOn (fun t : ℝ =>
      burnolYTransformed lambda s₁ k t *
        conj (burnolYTransformed lambda s₂ l t)) (Ioi (0 : ℝ)) := by
  have hinner := L2.integrable_inner (𝕜 := ℂ)
    (burnolYTransformedL2 lambda s₂ l)
    (burnolYTransformedL2 lambda s₁ k)
  apply hinner.congr
  filter_upwards [burnolYTransformedL2_coeFn hlambda0 hlambda1 s₁ k hs₁0 hs₁1,
    burnolYTransformedL2_coeFn hlambda0 hlambda1 s₂ l hs₂0 hs₂1] with
      t ht₁ ht₂
  rw [ht₁, ht₂, RCLike.inner_apply]

theorem inner_burnolYTransformedL2_eq_gammaMain_add_error
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    inner ℂ (burnolYTransformedL2 lambda s₂ l)
        (burnolYTransformedL2 lambda s₁ k) =
      (∫ t : ℝ in Ioc lambda 1,
        iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
          conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)) +
      ∫ t : ℝ in Ioi (0 : ℝ),
        burnolYTransformed lambda s₁ k t *
            conj (burnolYTransformed lambda s₂ l t) -
          burnolGammaMainCutoff lambda s₁ k t *
            conj (burnolGammaMainCutoff lambda s₂ l t) := by
  have hs₁0 : 0 < s₁.re := by rw [hs₁]; norm_num
  have hs₁1 : s₁.re < 1 := by rw [hs₁]; norm_num
  have hs₂0 : 0 < s₂.re := by rw [hs₂]; norm_num
  have hs₂1 : s₂.re < 1 := by rw [hs₂]; norm_num
  have hactual := integrableOn_burnolYPairing_Ioi hlambda0 hlambda1.le
    hs₁0 hs₁1 hs₂0 hs₂1 k l
  have hgamma := integrableOn_burnolGammaMainCutoffPairing_Ioi
    hlambda0 hlambda1 hs₁ hs₂ k l
  rw [inner_burnolYTransformedL2_eq_integral hlambda0 hlambda1.le
      hs₁0 hs₁1 hs₂0 hs₂1 k l,
    ← integral_burnolGammaMainCutoffPairing_eq hlambda0 s₁ k s₂ l,
    integral_sub hactual hgamma]
  ring

theorem tendsto_normalized_inner_burnolYTransformedL2
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        inner ℂ (burnolYTransformedL2 lambda s₂ l)
          (burnolYTransformedL2 lambda s₁ k))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) := by
  have hmain := tendsto_normalized_gammaMainPairing hs₁ hs₂ k l
  have herror := tendsto_normalized_burnolGramPairingError hs₁ hs₂ k l
  have hsum := hmain.add herror
  have hltOne : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have heq : (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        inner ℂ (burnolYTransformedL2 lambda s₂ l)
          (burnolYTransformedL2 lambda s₁ k)) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      fun lambda : ℝ =>
        ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
            (∫ t : ℝ in Ioc lambda 1,
              iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
                conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)) +
          ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
            (∫ t : ℝ in Ioi (0 : ℝ),
              burnolYTransformed lambda s₁ k t *
                  conj (burnolYTransformed lambda s₂ l t) -
                burnolGammaMainCutoff lambda s₁ k t *
                  conj (burnolGammaMainCutoff lambda s₂ l t)) := by
    filter_upwards [eventually_mem_nhdsWithin, hltOne] with
        lambda hlambda0 hlambda1
    rw [inner_burnolYTransformedL2_eq_gammaMain_add_error
      hlambda0 hlambda1 hs₁ hs₂ k l]
    ring
  have hsum' : Tendsto (fun lambda : ℝ =>
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioc lambda 1,
            iteratedDeriv k (burnolPhiHardyGammaMain t) s₁ *
              conj (iteratedDeriv l (burnolPhiHardyGammaMain t) s₂)) +
        ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
          (∫ t : ℝ in Ioi (0 : ℝ),
            burnolYTransformed lambda s₁ k t *
                conj (burnolYTransformed lambda s₂ l t) -
              burnolGammaMainCutoff lambda s₁ k t *
                conj (burnolGammaMainCutoff lambda s₂ l t)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) := by
    simpa only [add_zero] using hsum
  exact hsum'.congr' heq.symm

theorem burnolNormalization_mul
    {L : ℝ} (hL : 0 < L) (k l : ℕ) :
    L ^ (-(l : ℝ) - 1 / 2 : ℝ) * L ^ (-(k : ℝ) - 1 / 2 : ℝ) =
      (L ^ (k + l + 1))⁻¹ := by
  rw [← Real.rpow_add hL]
  have hexp : (-(l : ℝ) - 1 / 2) + (-(k : ℝ) - 1 / 2) =
      -((k + l + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_neg hL.le, Real.rpow_natCast]

theorem inner_burnolX_eq_normalized_transformed
    {lambda : ℝ} (hscale : 0 < burnolLogScale lambda)
    (s₁ : ℂ) (k : ℕ) (s₂ : ℂ) (l : ℕ) :
    inner ℂ (burnolX lambda s₂ l) (burnolX lambda s₁ k) =
      ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
        inner ℂ (burnolYTransformedL2 lambda s₂ l)
          (burnolYTransformedL2 lambda s₁ k) := by
  calc
    inner ℂ (burnolX lambda s₂ l) (burnolX lambda s₁ k) =
        inner ℂ (burnolAPhaseL2 (burnolX lambda s₂ l))
          (burnolAPhaseL2 (burnolX lambda s₁ k)) :=
      (burnolAPhaseL2.inner_map_map _ _).symm
    _ = inner ℂ
        (((((burnolLogScale lambda) ^ (-(l : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) •
          burnolYTransformedL2 lambda s₂ l))
        (((((burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) •
          burnolYTransformedL2 lambda s₁ k)) := by
      rw [burnolAPhaseL2_burnolX, burnolAPhaseL2_burnolX]
    _ = _ := by
      rw [inner_smul_left, inner_smul_right]
      simp only [Complex.conj_ofReal]
      calc
        (((burnolLogScale lambda) ^ (-(l : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) *
            ((((burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) *
              inner ℂ (burnolYTransformedL2 lambda s₂ l)
                (burnolYTransformedL2 lambda s₁ k)) =
          (((burnolLogScale lambda) ^ (-(l : ℝ) - 1 / 2 : ℝ) *
              (burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) *
            inner ℂ (burnolYTransformedL2 lambda s₂ l)
              (burnolYTransformedL2 lambda s₁ k) := by
            push_cast
            ring
        _ = _ := by rw [burnolNormalization_mul hscale k l]

theorem tendsto_inner_burnolX
    {s₁ s₂ : ℂ} (hs₁ : s₁.re = 1 / 2) (hs₂ : s₂.re = 1 / 2)
    (k l : ℕ) :
    Tendsto (fun lambda : ℝ =>
      inner ℂ (burnolX lambda s₂ l) (burnolX lambda s₁ k))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if s₁ = s₂ then
        ((((k + l + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) else 0)) := by
  have hbase := tendsto_normalized_inner_burnolYTransformedL2 hs₁ hs₂ k l
  have heq : (fun lambda : ℝ =>
      inner ℂ (burnolX lambda s₂ l) (burnolX lambda s₁ k)) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      fun lambda : ℝ =>
        ((((burnolLogScale lambda) ^ (k + l + 1))⁻¹ : ℝ) : ℂ) *
          inner ℂ (burnolYTransformedL2 lambda s₂ l)
            (burnolYTransformedL2 lambda s₁ k) := by
    filter_upwards [eventually_burnolLogScale_pos] with lambda hscale
    exact inner_burnolX_eq_normalized_transformed hscale s₁ k s₂ l
  exact hbase.congr' heq.symm

/-! ## The transformed target -/

/-- Burnol's normalization of the sinc function, continuously extended at zero. -/
def burnolSinc (t : ℝ) : ℂ :=
  ((2 * Real.sinc (2 * Real.pi * t) : ℝ) : ℂ)

theorem continuous_burnolSinc : Continuous burnolSinc := by
  unfold burnolSinc
  fun_prop

theorem burnolSinc_eq_ratio {t : ℝ} (ht : t ≠ 0) :
    burnolSinc t =
      (Real.sin (2 * Real.pi * t) : ℂ) / (Real.pi * t : ℝ) := by
  rw [burnolSinc, Real.sinc_of_ne_zero]
  · push_cast
    field_simp [Real.pi_ne_zero, ht]
  · exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht

theorem norm_burnolSinc_le_two (t : ℝ) :
    ‖burnolSinc t‖ ≤ 2 := by
  rw [burnolSinc, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num
  exact Real.abs_sinc_le_one _

theorem norm_burnolSinc_le_inv {t : ℝ} (ht : 1 ≤ t) :
    ‖burnolSinc t‖ ≤ t⁻¹ := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hbase :
      ‖burnolSinc t‖ ≤ (Real.pi * t)⁻¹ := by
    rw [burnolSinc_eq_ratio ht0.ne']
    simpa only [burnolPhiBoundaryTerm_zero] using
      norm_burnolPhiBoundaryTerm_le 0 ht0
  exact hbase.trans <| inv_anti₀ ht0 <| by
    nlinarith [Real.pi_gt_three]

theorem norm_burnolSinc_sub_two_le_sq
    {t : ℝ} (ht : 0 ≤ t) (hsmall : 2 * Real.pi * t ≤ 1) :
    ‖burnolSinc t - (2 : ℂ)‖ ≤ 8 * Real.pi ^ 2 * t ^ 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [burnolSinc]
  let x : ℝ := 2 * Real.pi * t
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by simpa only [x] using hsmall
  have hxabs : |x| ≤ 1 := by simpa [abs_of_pos hx0] using hx1
  have hTaylor :
      |Real.sin x - (x - x ^ 3 / 6)| ≤ x ^ 4 * (5 / 96) := by
    simpa [abs_of_pos hx0] using Real.sin_bound hxabs
  have hxpow : x ^ 4 ≤ x ^ 3 := by
    rw [show x ^ 4 = x ^ 3 * x by ring]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0.le 3)
  have hsin : |Real.sin x - x| ≤ x ^ 3 := by
    calc
      |Real.sin x - x| =
          |(Real.sin x - (x - x ^ 3 / 6)) - x ^ 3 / 6| := by
            congr 1
            ring
      _ ≤ |Real.sin x - (x - x ^ 3 / 6)| + |x ^ 3 / 6| := abs_sub _ _
      _ ≤ x ^ 4 * (5 / 96) + x ^ 3 / 6 := by
        gcongr
        rw [abs_of_nonneg]
        positivity
      _ ≤ x ^ 3 * (5 / 96) + x ^ 3 / 6 := by
        gcongr
      _ ≤ x ^ 3 := by
        nlinarith [pow_nonneg hx0.le 3]
  rw [burnolSinc_eq_ratio ht.ne']
  have hcast :
      (Real.sin (2 * Real.pi * t) : ℂ) / (Real.pi * t : ℝ) - 2 =
        ((Real.sin (2 * Real.pi * t) / (Real.pi * t) - 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_div]
    norm_num
  have hnorm :
      ‖(Real.sin (2 * Real.pi * t) : ℂ) / (Real.pi * t : ℝ) - 2‖ =
        |Real.sin x / (Real.pi * t) - 2| := by
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have hden : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have heq :
      Real.sin x / (Real.pi * t) - 2 =
        (Real.sin x - x) / (Real.pi * t) := by
    dsimp [x]
    field_simp
  rw [heq, abs_div, abs_of_pos hden]
  calc
    |Real.sin x - x| / (Real.pi * t) ≤ x ^ 3 / (Real.pi * t) :=
      div_le_div_of_nonneg_right hsin hden.le
    _ = 8 * Real.pi ^ 2 * t ^ 2 := by
      dsimp [x]
      field_simp
      ring

theorem integrableOn_burnolSinc_Ioc_zero (T : ℝ) :
    IntegrableOn burnolSinc (Ioc (0 : ℝ) T) := by
  exact continuous_burnolSinc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem burnolHardyAverage_sinc_sub_two
    {t : ℝ} (ht : 0 < t) :
    burnolHardyAverage (fun u => burnolSinc u - (2 : ℂ)) t =
      burnolHardyAverage burnolSinc t - 2 := by
  rw [burnolHardyAverage, burnolHardyAverage,
    integral_sub (integrableOn_burnolSinc_Ioc_zero t)
      (integrableOn_const measure_Ioc_lt_top.ne)]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [integral_const, measureReal_restrict_apply_univ]
  simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal ht.le,
    sub_zero, Complex.real_smul]
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ htC, one_mul]

/-- The source representative `sinc - M sinc` for the second phase applied to `chi1`. -/
def burnolChiOnePhase (t : ℝ) : ℂ :=
  burnolSinc t - burnolHardyAverage burnolSinc t

theorem continuousOn_burnolChiOnePhase_Ioi :
    ContinuousOn burnolChiOnePhase (Ioi (0 : ℝ)) := by
  exact continuous_burnolSinc.continuousOn.sub
    (continuousOn_burnolHardyAverage_Ioi integrableOn_burnolSinc_Ioc_zero)

theorem aestronglyMeasurable_burnolChiOnePhase_Ioi :
    AEStronglyMeasurable burnolChiOnePhase
      (volume.restrict (Ioi (0 : ℝ))) :=
  continuousOn_burnolChiOnePhase_Ioi.aestronglyMeasurable
    (μ := volume) measurableSet_Ioi

theorem norm_burnolChiOnePhase_le_four {t : ℝ} (ht : 0 < t) :
    ‖burnolChiOnePhase t‖ ≤ 4 := by
  have havg : ‖burnolHardyAverage burnolSinc t‖ ≤ 2 :=
    norm_burnolHardyAverage_le_of_norm_le ht fun u _ =>
      norm_burnolSinc_le_two u
  rw [burnolChiOnePhase]
  exact (norm_sub_le _ _).trans <| by
    linarith [norm_burnolSinc_le_two t]

theorem norm_burnolChiOnePhase_le_sq
    {t : ℝ} (ht : 0 < t) (hsmall : 2 * Real.pi * t ≤ 1) :
    ‖burnolChiOnePhase t‖ ≤ 16 * Real.pi ^ 2 * t ^ 2 := by
  let C : ℝ := 8 * Real.pi ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsinc : ‖burnolSinc t - (2 : ℂ)‖ ≤ C * t ^ 2 := by
    simpa only [C] using norm_burnolSinc_sub_two_le_sq ht.le hsmall
  have havg :
      ‖burnolHardyAverage (fun u => burnolSinc u - (2 : ℂ)) t‖ ≤
        C * t ^ 2 := by
    apply norm_burnolHardyAverage_le_of_norm_le ht
    intro u hu
    calc
      ‖burnolSinc u - (2 : ℂ)‖ ≤ C * u ^ 2 := by
        apply norm_burnolSinc_sub_two_le_sq hu.1.le
        exact (mul_le_mul_of_nonneg_left hu.2 (by positivity)).trans hsmall
      _ ≤ C * t ^ 2 := by
        exact mul_le_mul_of_nonneg_left
          ((sq_le_sq₀ hu.1.le ht.le).2 hu.2) hC
  rw [burnolChiOnePhase]
  calc
    ‖burnolSinc t - burnolHardyAverage burnolSinc t‖ =
        ‖(burnolSinc t - 2) - (burnolHardyAverage burnolSinc t - 2)‖ := by
          congr 1
          ring
    _ = ‖(burnolSinc t - 2) -
        burnolHardyAverage (fun u => burnolSinc u - (2 : ℂ)) t‖ := by
          rw [burnolHardyAverage_sinc_sub_two ht]
    _ ≤ ‖burnolSinc t - 2‖ +
        ‖burnolHardyAverage (fun u => burnolSinc u - (2 : ℂ)) t‖ :=
          norm_sub_le _ _
    _ ≤ C * t ^ 2 + C * t ^ 2 := add_le_add hsinc havg
    _ = 16 * Real.pi ^ 2 * t ^ 2 := by
      dsimp [C]
      ring

theorem burnolChiOnePhase_isBigO_sq :
    burnolChiOnePhase =O[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨16 * Real.pi ^ 2, ?_⟩
  have hcut : 0 < (2 * Real.pi)⁻¹ := by positivity
  have hlt :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), t < (2 * Real.pi)⁻¹ :=
    (eventually_lt_nhds hcut).filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hlt] with t ht htcut
  have hsmall : 2 * Real.pi * t ≤ 1 := by
    calc
      2 * Real.pi * t ≤ 2 * Real.pi * (2 * Real.pi)⁻¹ :=
        mul_le_mul_of_nonneg_left htcut.le (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] using
    norm_burnolChiOnePhase_le_sq ht hsmall

def burnolChiOnePhaseLargeCoeff : ℝ :=
  ‖∫ u : ℝ in Ioc 0 1, burnolSinc u‖ + 2

theorem burnolChiOnePhaseLargeCoeff_nonneg :
    0 ≤ burnolChiOnePhaseLargeCoeff := by
  unfold burnolChiOnePhaseLargeCoeff
  positivity

theorem norm_burnolChiOnePhase_le_large {t : ℝ} (ht : 1 ≤ t) :
    ‖burnolChiOnePhase t‖ ≤
      burnolChiOnePhaseLargeCoeff * (1 + Real.log t) ^ 2 / t := by
  let L : ℝ := ‖∫ u : ℝ in Ioc 0 1, burnolSinc u‖
  have hL : 0 ≤ L := norm_nonneg _
  have havg : ‖burnolHardyAverage burnolSinc t‖ ≤
      (L + 1) * (1 + Real.log t) / t := by
    simpa only [pow_zero, mul_one, Nat.reduceAdd, pow_one] using
      (norm_burnolHardyAverage_le_large
        (f := burnolSinc) 0 zero_le_one hL ht
        (integrableOn_burnolSinc_Ioc_zero t) (le_refl _)
        (fun u hu => by
          simpa only [pow_zero, mul_one, one_div] using
            norm_burnolSinc_le_inv hu))
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht
  have hbase : 1 ≤ 1 + Real.log t := by linarith
  have hbase0 : 0 ≤ 1 + Real.log t := by linarith
  have hbaseSq : 1 + Real.log t ≤ (1 + Real.log t) ^ 2 := by
    rw [pow_two]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hbase hbase0
  have hsinc : ‖burnolSinc t‖ ≤ (1 + Real.log t) / t := by
    calc
      ‖burnolSinc t‖ ≤ t⁻¹ := norm_burnolSinc_le_inv ht
      _ = 1 / t := by rw [one_div]
      _ ≤ (1 + Real.log t) / t :=
        div_le_div_of_nonneg_right hbase ht0.le
  rw [burnolChiOnePhase]
  calc
    ‖burnolSinc t - burnolHardyAverage burnolSinc t‖ ≤
        ‖burnolSinc t‖ + ‖burnolHardyAverage burnolSinc t‖ := norm_sub_le _ _
    _ ≤ (1 + Real.log t) / t + (L + 1) * (1 + Real.log t) / t :=
      add_le_add hsinc havg
    _ = (L + 2) * (1 + Real.log t) / t := by ring
    _ ≤ (L + 2) * (1 + Real.log t) ^ 2 / t := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbaseSq (by linarith)) ht0.le
    _ = burnolChiOnePhaseLargeCoeff * (1 + Real.log t) ^ 2 / t := by
      rfl

theorem burnolChiOnePhase_memLp :
    MemLp burnolChiOnePhase (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  let C : ℝ := burnolChiOnePhaseLargeCoeff
  have hmeas := aestronglyMeasurable_burnolChiOnePhase_Ioi
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  change IntegrableOn (fun t : ℝ => ‖burnolChiOnePhase t‖ ^ 2) (Ioi (0 : ℝ))
  have hsmallMajor : IntegrableOn (fun _ : ℝ => (16 : ℝ)) (Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hsmall : IntegrableOn (fun t : ℝ => ‖burnolChiOnePhase t‖ ^ 2)
      (Ioc (0 : ℝ) 1) := by
    apply Integrable.mono' hsmallMajor
      ((hmeas.mono_set Ioc_subset_Ioi_self).norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_burnolChiOnePhase_le_four ht.1,
      norm_nonneg (burnolChiOnePhase t)]
  have hlargeMajor : IntegrableOn
      (fun t : ℝ => 8 * C ^ 2 *
        (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)))
      (Ioi (1 : ℝ)) :=
    integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * C ^ 2)
  have hlarge : IntegrableOn (fun t : ℝ => ‖burnolChiOnePhase t‖ ^ 2)
      (Ioi (1 : ℝ)) := by
    apply Integrable.mono' hlargeMajor
      ((hmeas.mono_set (Ioi_subset_Ioi zero_le_one)).norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _)]
    have ht1 : 1 ≤ t := ht.le
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hbound := norm_burnolChiOnePhase_le_large ht1
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
      ‖burnolChiOnePhase t‖ ^ 2 ≤
          (C * (1 + Real.log t) ^ 2 / t) ^ 2 := by
        simpa only [C] using hboundSq
      _ = C ^ 2 * (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, mul_pow, mul_pow, hinvSq]
        ring
      _ ≤ C ^ 2 * (8 * (1 + (Real.log t) ^ 4)) * t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hadd (sq_nonneg C))
          (Real.rpow_nonneg ht0.le _)
      _ = 8 * C ^ 2 *
          (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ)) := by ring
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact hsmall.union hlarge

/-- The explicit transformed target as an `L2(0,infinity)` element. -/
def burnolChiOnePhaseL2 : positiveHalfLineComplexL2 :=
  burnolChiOnePhase_memLp.toLp burnolChiOnePhase

theorem burnolChiOnePhaseL2_coeFn :
    burnolChiOnePhaseL2 =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolChiOnePhase :=
  MemLp.coeFn_toLp burnolChiOnePhase_memLp

theorem burnolPhi_zero_zero_eq_sinc {t : ℝ} (ht : 0 < t) :
    burnolPhi 0 0 t = burnolSinc t := by
  rw [burnolPhi_zero, burnolSinc_eq_ratio ht.ne']
  simp

theorem mellinConvergent_burnolSinc
    (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    MellinConvergent burnolSinc z := by
  have hphi := mellinConvergent_burnolPhi 0 0 z hz0 hz1 (by simpa using hz0)
  rw [MellinConvergent] at hphi ⊢
  apply hphi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change (t : ℂ) ^ (z - 1) • burnolPhi 0 0 t =
    (t : ℂ) ^ (z - 1) • burnolSinc t
  rw [burnolPhi_zero_zero_eq_sinc ht]

theorem mellin_burnolSinc
    (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    mellin burnolSinc z = burnolUSpectral z / z := by
  calc
    mellin burnolSinc z = mellin (burnolPhi 0 0) z := by
      rw [mellin, mellin]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t : ℂ) ^ (z - 1) • burnolSinc t =
        (t : ℂ) ^ (z - 1) • burnolPhi 0 0 t
      rw [burnolPhi_zero_zero_eq_sinc ht]
    _ = burnolUSpectral z / z := by
      simpa using mellin_burnolPhi_eq_USpectral_mul_pole
        0 0 z hz0 hz1 (by simpa using hz0)

theorem mellinConvergent_burnolChiOnePhase
    (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    MellinConvergent burnolChiOnePhase z := by
  have hsinc := mellinConvergent_burnolSinc z hz0 hz1
  have havg := mellinConvergent_burnolHardyAverage
    continuous_burnolSinc.aestronglyMeasurable hsinc hz1
  have hsub := hasMellin_sub hsinc havg
  change MellinConvergent
    (fun t => burnolSinc t - burnolHardyAverage burnolSinc t) z
  exact hsub.1

theorem mellin_burnolChiOnePhase
    (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    mellin burnolChiOnePhase z = burnolUSpectral z / (z - 1) := by
  have hsinc := mellinConvergent_burnolSinc z hz0 hz1
  have hmeas : AEStronglyMeasurable burnolSinc
      (volume.restrict (Ioi (0 : ℝ))) :=
    continuous_burnolSinc.aestronglyMeasurable
  have havg := mellinConvergent_burnolHardyAverage hmeas hsinc hz1
  have hsub := hasMellin_sub hsinc havg
  have hz0' : z ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hz0
    exact lt_irrefl 0 hz0
  have hz1' : 1 - z ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hzm1 : z - 1 ≠ 0 := sub_ne_zero.mpr <| by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.one_re] at hre
    linarith
  calc
    mellin burnolChiOnePhase z =
        mellin burnolSinc z - mellin (burnolHardyAverage burnolSinc) z := by
      change mellin (fun t =>
        burnolSinc t - burnolHardyAverage burnolSinc t) z = _
      exact hsub.2
    _ = burnolUSpectral z / z - (1 - z)⁻¹ * (burnolUSpectral z / z) := by
      rw [mellin_burnolHardyAverage hmeas hsinc hz1,
        mellin_burnolSinc z hz0 hz1]
    _ = burnolUSpectral z / (z - 1) := by
      field_simp [hz0', hz1', hzm1]
      ring

def burnolChiOnePhaseWeightedLog (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) * burnolChiOnePhase (Real.exp (-u))

theorem burnolChiOnePhaseWeightedLog_ae_weightedLogForwardFun :
    burnolChiOnePhaseWeightedLog =ᵐ[volume]
      weightedLogForwardFun burnolChiOnePhaseL2 := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq burnolChiOnePhaseL2_coeFn
  filter_upwards [hsource] with u hu
  simp only [burnolChiOnePhaseWeightedLog, weightedLogForwardFun, expNeg]
  have hpoint : burnolChiOnePhaseL2 (Real.exp (-u)) =
      burnolChiOnePhase (Real.exp (-u)) := by
    simpa only [Function.comp_apply, expNeg] using hu
  rw [hpoint]

theorem burnolChiOnePhaseWeightedLog_memLp :
    MemLp burnolChiOnePhaseWeightedLog (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp burnolChiOnePhaseL2).ae_eq
    burnolChiOnePhaseWeightedLog_ae_weightedLogForwardFun.symm

theorem burnolChiOnePhaseWeightedLog_toLp :
    burnolChiOnePhaseWeightedLog_memLp.toLp burnolChiOnePhaseWeightedLog =
      weightedLogPullback burnolChiOnePhaseL2 := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr burnolChiOnePhaseWeightedLog_memLp
    (weightedLogForwardFun_memLp burnolChiOnePhaseL2)
    burnolChiOnePhaseWeightedLog_ae_weightedLogForwardFun

theorem burnolChiOnePhaseWeightedLog_integrable :
    Integrable burnolChiOnePhaseWeightedLog := by
  have hM := mellinConvergent_burnolChiOnePhase
    (1 / 2 : ℂ) (by norm_num) (by norm_num)
  exact integrable_weightedLog_of_mellinConvergent hM

def burnolChiOnePhaseTransform (xi : ℝ) : ℂ :=
  burnolVSpectral (burnolCriticalLineAtFrequency xi) * burnolChiOneTransform xi

theorem burnolChiOnePhaseTransform_eq_mellin (xi : ℝ) :
    burnolChiOnePhaseTransform xi =
      burnolUSpectral (burnolCriticalLineAtFrequency xi) /
        (burnolCriticalLineAtFrequency xi - 1) := by
  have hs0 := burnolCriticalLineAtFrequency_ne_zero xi
  have hs1 : 1 - burnolCriticalLineAtFrequency xi ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [burnolCriticalLineAtFrequency] at hre
  have hsm1 : burnolCriticalLineAtFrequency xi - 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [burnolCriticalLineAtFrequency] at hre
  rw [burnolChiOnePhaseTransform, burnolChiOneTransform,
    burnolVSpectral]
  field_simp [hs0, hs1, hsm1]
  ring

theorem fourier_burnolChiOnePhaseWeightedLog (xi : ℝ) :
    𝓕 burnolChiOnePhaseWeightedLog xi = burnolChiOnePhaseTransform xi := by
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
  have hFourier := mellin_criticalLine_eq_fourier burnolChiOnePhase tau
  rw [hs, mellin_burnolChiOnePhase s hs0 hs1] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : ℝ =>
    (Real.exp (-u / 2) : ℂ) * burnolChiOnePhase (Real.exp (-u))) xi = _
  rw [← hFourier]
  exact (burnolChiOnePhaseTransform_eq_mellin xi).symm

theorem ae_burnolChiOnePhaseTransform_eq_phase_mul :
    burnolChiOnePhaseTransform =ᵐ[volume]
      fun xi : ℝ => burnolAPhaseMultiplier xi * burnolChiOneTransform xi := by
  filter_upwards [ae_burnolVSpectral_critical_eq_APhaseMultiplier] with xi hphase
  rw [burnolChiOnePhaseTransform, hphase]

theorem burnolChiOnePhaseTransform_memLp :
    MemLp burnolChiOnePhaseTransform (2 : ℝ≥0∞) volume := by
  have hproduct : MemLp
      (fun xi : ℝ => burnolAPhaseMultiplier xi • burnolChiOneTransform xi)
      (2 : ℝ≥0∞) volume :=
    burnolChiOneTransform_memLp.smul burnolAPhaseMultiplier_memLp_top
  exact hproduct.ae_eq <| by
    filter_upwards [ae_burnolChiOnePhaseTransform_eq_phase_mul] with xi hxi
    simpa only [smul_eq_mul] using hxi.symm

theorem baezDuarteFourierMellinL2_burnolChiOnePhaseL2 :
    baezDuarteFourierMellinL2 burnolChiOnePhaseL2 =
      burnolChiOnePhaseTransform_memLp.toLp burnolChiOnePhaseTransform := by
  have hFourier2 : MemLp (𝓕 burnolChiOnePhaseWeightedLog)
      (2 : ℝ≥0∞) volume :=
    burnolChiOnePhaseTransform_memLp.ae_eq
      (ae_of_all volume fun xi => (fourier_burnolChiOnePhaseWeightedLog xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    burnolChiOnePhaseWeightedLog_integrable
    burnolChiOnePhaseWeightedLog_memLp hFourier2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← burnolChiOnePhaseWeightedLog_toLp]
  calc
    _ = hFourier2.toLp (𝓕 burnolChiOnePhaseWeightedLog) := hcompat
    _ = burnolChiOnePhaseTransform_memLp.toLp burnolChiOnePhaseTransform :=
      MemLp.toLp_congr hFourier2 burnolChiOnePhaseTransform_memLp
        (ae_of_all volume fourier_burnolChiOnePhaseWeightedLog)

theorem burnolAPhaseFrequencyL2_chiOneTransform :
    burnolAPhaseFrequencyL2
        (burnolChiOneTransform_memLp.toLp burnolChiOneTransform) =
      burnolChiOnePhaseTransform_memLp.toLp burnolChiOnePhaseTransform := by
  rw [burnolAPhaseFrequencyL2_apply]
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolAPhaseMultiplierLInf
      (burnolChiOneTransform_memLp.toLp burnolChiOneTransform),
    burnolAPhaseMultiplierLInf_coeFn,
    MemLp.coeFn_toLp burnolChiOneTransform_memLp,
    MemLp.coeFn_toLp burnolChiOnePhaseTransform_memLp,
    ae_burnolChiOnePhaseTransform_eq_phase_mul] with
      xi hout hphase hchi htarget hrelation
  rw [hout]
  change burnolAPhaseMultiplierLInf xi *
      (burnolChiOneTransform_memLp.toLp burnolChiOneTransform) xi =
    (burnolChiOnePhaseTransform_memLp.toLp burnolChiOnePhaseTransform) xi
  rw [hphase, hchi, htarget, hrelation]

theorem burnolAPhaseL2_chiOne :
    burnolAPhaseL2 burnolChiOneL2 = burnolChiOnePhaseL2 := by
  apply baezDuarteFourierMellinL2.injective
  rw [baezDuarteFourierMellinL2_burnolAPhaseL2,
    baezDuarteFourierMellinL2_chiOne_eq,
    burnolAPhaseFrequencyL2_chiOneTransform,
    baezDuarteFourierMellinL2_burnolChiOnePhaseL2]

theorem inner_burnolPsiL2_zero_chiOne
    (w : ℂ) (hwHalf : w.re < 1 / 2) :
    inner ℂ (burnolPsiL2 w 0) burnolChiOneL2 =
      let z := 1 - conj w
      (z - 1) / z ^ 2 := by
  let z : ℂ := 1 - conj w
  have hz0 : 0 < z.re := by
    dsimp only [z]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hM := hasMellin_burnolChiOne z hz0
  rw [MeasureTheory.L2.inner_def, ← hM.2, mellin]
  apply integral_congr_ae
  filter_upwards [burnolPsiL2_coeFn w 0 hwHalf,
    burnolChiOneL2_coeFn, ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi (0 : ℝ))).ae_ne (1 : ℝ)] with
      t hpsi hchi ht htOne
  rw [hpsi, hchi, RCLike.inner_apply']
  change conj (burnolPsi w 0 t) * (burnolChiOne t : ℂ) =
    (t : ℂ) ^ (z - 1) * (burnolChiOne t : ℂ)
  by_cases ht1 : t < 1
  · have htMem : t ∈ Ioo (0 : ℝ) 1 := ⟨ht, ht1⟩
    rw [burnolPsi, Set.indicator_of_mem htMem]
    simp only [pow_zero, one_mul]
    have harg : ((t : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ht.le]
      exact Real.pi_pos.ne
    have hconj : conj ((t : ℂ) ^ (-w)) =
        (t : ℂ) ^ (-conj w) := by
      simpa using (Complex.cpow_conj (t : ℂ) (-w) harg).symm
    rw [hconj]
    congr 1
    dsimp only [z]
    ring
  · have htGt : 1 < t := lt_of_le_of_ne (not_lt.mp ht1) (Ne.symm htOne)
    have htNot : t ∉ Ioo (0 : ℝ) 1 := fun h => (not_lt_of_ge htGt.le) h.2
    rw [burnolPsi, Set.indicator_of_notMem htNot,
      burnolChiOne_eq_zero_of_not_mem]
    · simp
    · exact fun h => (not_le_of_gt htGt) h.2

theorem tendsto_inner_burnolPsiL2_zero_chiOne
    {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun w : ℂ => inner ℂ (burnolPsiL2 w 0) burnolChiOneL2)
      (nhdsWithin s {w : ℂ | 0 < w.re ∧ w.re < 1 / 2})
      (nhds ((s - 1) / s ^ 2)) := by
  let l := nhdsWithin s {w : ℂ | 0 < w.re ∧ w.re < 1 / 2}
  let F : ℂ → ℂ := fun w =>
    let z := 1 - conj w
    (z - 1) / z ^ 2
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hs
    norm_num at hs
  have hF : ContinuousAt F s := by
    have hz0 : 1 - conj s ≠ 0 := by
      rw [conj_eq_one_sub_of_re_eq_half hs]
      have heq : (1 : ℂ) - (1 - s) = s := by ring
      simpa only [heq] using hs0
    have hzcont : ContinuousAt (fun w : ℂ => 1 - conj w) s :=
      continuousAt_const.sub Complex.continuous_conj.continuousAt
    dsimp only [F]
    exact (hzcont.sub continuousAt_const).div (hzcont.pow 2)
      (pow_ne_zero 2 hz0)
  have hFs : F s = (s - 1) / s ^ 2 := by
    dsimp only [F]
    rw [conj_eq_one_sub_of_re_eq_half hs]
    ring
  have heq : (fun w : ℂ =>
      inner ℂ (burnolPsiL2 w 0) burnolChiOneL2) =ᶠ[l] F := by
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    exact inner_burnolPsiL2_zero_chiOne w hw.2
  rw [← hFs]
  exact hF.tendsto.mono_left inf_le_left |>.congr' heq.symm

def burnolTargetPairingIntegrand
    (lambda : ℝ) (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  burnolChiOnePhase t * conj (burnolYTransformed lambda s k t)

def burnolTargetPairingSmallMajor (s : ℂ) (k : ℕ) (t : ℝ) : ℝ :=
  4 * (burnolVMainDerivCoeffBound s k *
      (1 + |Real.log t|) ^ k * t ^ (-(1 / 2 : ℝ)) +
    4 * burnolPhiSeriesBound k)

def burnolTargetPairingLargeMajor (s : ℂ) (k : ℕ) (t : ℝ) : ℝ :=
  8 * burnolChiOnePhaseLargeCoeff *
    burnolPhiHardySquareLargeCoeff s k *
      (t ^ (-2 : ℝ) + (Real.log t) ^ 4 * t ^ (-2 : ℝ))

def burnolTargetPairingMajor (s : ℂ) (k : ℕ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (burnolTargetPairingSmallMajor s k) t +
    (Ioi (1 : ℝ)).indicator (burnolTargetPairingLargeMajor s k) t

theorem integrableOn_burnolTargetPairingMajor (s : ℂ) (k : ℕ) :
    IntegrableOn (burnolTargetPairingMajor s k) (Ioi (0 : ℝ)) := by
  let A := burnolVMainDerivCoeffBound s k
  let C := 4 * burnolPhiSeriesBound k
  let Q := burnolChiOnePhaseLargeCoeff
  let B := burnolPhiHardySquareLargeCoeff s k
  have hweight := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    k (a := -(1 / 2 : ℝ)) (by norm_num)
  have hsmallOn : IntegrableOn
      (burnolTargetPairingSmallMajor s k) (Ioc (0 : ℝ) 1) := by
    have hmain := hweight.const_mul (4 * A)
    have hconst : IntegrableOn (fun _ : ℝ => 4 * C) (Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    exact (hmain.add hconst).congr <| ae_of_all _ fun t => by
      dsimp only [burnolTargetPairingSmallMajor, A, C]
      simp only [Pi.add_apply]
      ring
  have hlargeOn : IntegrableOn
      (burnolTargetPairingLargeMajor s k) (Ioi (1 : ℝ)) := by
    exact (integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * Q * B)).congr <| ae_of_all _ fun t => by
        dsimp only [burnolTargetPairingLargeMajor, Q, B]
  have hsmall := hsmallOn.integrable_indicator measurableSet_Ioc
  have hlarge := hlargeOn.integrable_indicator measurableSet_Ioi
  exact (hsmall.add hlarge).integrableOn.congr
    (ae_of_all _ fun _ => rfl)

theorem burnolTargetPairingSmallMajor_nonneg
    (s : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ burnolTargetPairingSmallMajor s k t := by
  have hA := burnolVMainDerivCoeffBound_nonneg s k
  have hC := burnolPhiSeriesBound_nonneg k
  have htPow := Real.rpow_nonneg ht.le (-(1 / 2 : ℝ))
  unfold burnolTargetPairingSmallMajor
  positivity

theorem burnolTargetPairingLargeMajor_nonneg
    (s : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ burnolTargetPairingLargeMajor s k t := by
  have hQ := burnolChiOnePhaseLargeCoeff_nonneg
  have hB := burnolPhiHardySquareLargeCoeff_nonneg s k
  have htPow := Real.rpow_nonneg ht.le (-2 : ℝ)
  unfold burnolTargetPairingLargeMajor
  positivity

theorem burnolTargetPairingMajor_nonneg
    (s : ℂ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ burnolTargetPairingMajor s k t := by
  by_cases ht1 : t ≤ 1
  · rw [burnolTargetPairingMajor,
      Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩),
      Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from
        fun h => (not_lt_of_ge ht1) h), add_zero]
    exact burnolTargetPairingSmallMajor_nonneg s k ht
  · have htLarge : t ∈ Ioi (1 : ℝ) := lt_of_not_ge ht1
    rw [burnolTargetPairingMajor,
      Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from
        fun h => ht1 h.2), Set.indicator_of_mem htLarge, zero_add]
    exact burnolTargetPairingLargeMajor_nonneg s k ht

theorem norm_burnolTargetPairingIntegrand_le
    {lambda : ℝ} (hlambda1 : lambda ≤ 1)
    {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ)
    {t : ℝ} (ht : 0 < t) :
    ‖burnolTargetPairingIntegrand lambda s k t‖ ≤
      burnolTargetPairingMajor s k t := by
  let A := burnolVMainDerivCoeffBound s k
  let C := 4 * burnolPhiSeriesBound k
  let Q := burnolChiOnePhaseLargeCoeff
  let B := burnolPhiHardySquareLargeCoeff s k
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  have hA0 : 0 ≤ A := burnolVMainDerivCoeffBound_nonneg s k
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num) (burnolPhiSeriesBound_nonneg k)
  have hQ0 : 0 ≤ Q := burnolChiOnePhaseLargeCoeff_nonneg
  have hB0 : 0 ≤ B := burnolPhiHardySquareLargeCoeff_nonneg s k
  rw [burnolTargetPairingIntegrand, norm_mul, Complex.norm_conj]
  by_cases ht1 : t ≤ 1
  · rw [burnolTargetPairingMajor,
      Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩),
      Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from
        fun h => (not_lt_of_ge ht1) h), add_zero]
    by_cases hlambdaT : lambda ≤ t
    · have herror := norm_burnolYTransformed_sub_gammaMain_le
        hlambdaT s k hs0 hs1 ht ht1
      have hmain := norm_iteratedDeriv_burnolPhiHardyGammaMain_le
        k hs0 hs1 ht
      have hY : ‖burnolYTransformed lambda s k t‖ ≤
          A * (1 + |Real.log t|) ^ k * t ^ (-(1 / 2 : ℝ)) + C := by
        calc
          ‖burnolYTransformed lambda s k t‖ ≤
              ‖burnolYTransformed lambda s k t -
                iteratedDeriv k (burnolPhiHardyGammaMain t) s‖ +
              ‖iteratedDeriv k (burnolPhiHardyGammaMain t) s‖ := by
            nth_rewrite 1 [show burnolYTransformed lambda s k t =
                (burnolYTransformed lambda s k t -
                  iteratedDeriv k (burnolPhiHardyGammaMain t) s) +
                iteratedDeriv k (burnolPhiHardyGammaMain t) s by ring]
            exact norm_add_le _ _
          _ ≤ C + A * (1 + |Real.log t|) ^ k * t ^ (-(1 / 2 : ℝ)) := by
            simpa only [A, C, hs] using add_le_add herror hmain
          _ = _ := by ring
      calc
        ‖burnolChiOnePhase t‖ * ‖burnolYTransformed lambda s k t‖ ≤
            4 * (A * (1 + |Real.log t|) ^ k *
              t ^ (-(1 / 2 : ℝ)) + C) := by
          exact mul_le_mul (norm_burnolChiOnePhase_le_four ht) hY
            (norm_nonneg _) (by positivity)
        _ = burnolTargetPairingSmallMajor s k t := by
          rfl
    · have hlt : t < lambda := lt_of_not_ge hlambdaT
      rw [burnolYTransformed_eq_zero_of_lt hlt s k, norm_zero, mul_zero]
      exact burnolTargetPairingSmallMajor_nonneg s k ht
  · have htLarge : t ∈ Ioi (1 : ℝ) := lt_of_not_ge ht1
    rw [burnolTargetPairingMajor,
      Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from
        fun h => ht1 h.2), Set.indicator_of_mem htLarge, zero_add]
    have hq := norm_burnolChiOnePhase_le_large htLarge.le
    have hY := norm_burnolYTransformed_le_large hlambda1
      s k hs0 hs1 htLarge.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg htLarge.le
    have hadd : (1 + Real.log t) ^ 4 ≤
        8 * (1 + (Real.log t) ^ 4) := by
      have h := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hlog0 4
      norm_num at h
      exact h
    have hinvSq : t⁻¹ ^ 2 = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht.le]
      exact (inv_pow t 2).trans
        (congrArg Inv.inv (Real.rpow_natCast t 2).symm)
    calc
      ‖burnolChiOnePhase t‖ * ‖burnolYTransformed lambda s k t‖ ≤
          (Q * (1 + Real.log t) ^ 2 / t) *
            (B * (1 + Real.log t) ^ 2 / t) := by
        exact mul_le_mul (by simpa only [Q] using hq)
          (by simpa only [B, abs_of_nonneg hlog0] using hY)
          (norm_nonneg _) (by positivity)
      _ = Q * B * (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, hinvSq.symm]
        ring
      _ ≤ Q * B * (8 * (1 + (Real.log t) ^ 4)) * t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hadd (mul_nonneg hQ0 hB0))
          (Real.rpow_nonneg ht.le _)
      _ = burnolTargetPairingLargeMajor s k t := by
        dsimp only [burnolTargetPairingLargeMajor, Q, B]
        ring

theorem tendsto_integral_burnolTargetPairingIntegrand
    {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand lambda s k t)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 s k t)) := by
  let l := nhdsWithin (0 : ℝ) (Ioi 0)
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  have hlambda : ∀ᶠ lambda : ℝ in l, 0 < lambda ∧ lambda ≤ 1 := by
    have hlt : ∀ᶠ lambda : ℝ in l, lambda < 1 :=
      (eventually_lt_nhds one_pos).filter_mono inf_le_left
    filter_upwards [eventually_mem_nhdsWithin, hlt] with lambda h0 h1
    exact ⟨h0, h1.le⟩
  have hqconj : AEStronglyMeasurable (fun t : ℝ => conj (burnolChiOnePhase t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      aestronglyMeasurable_burnolChiOnePhase_Ioi
  have hmeas : ∀ᶠ lambda : ℝ in l,
      AEStronglyMeasurable (burnolTargetPairingIntegrand lambda s k)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hlambda] with lambda hlambda
    exact aestronglyMeasurable_burnolChiOnePhase_Ioi.mul <|
      Complex.continuous_conj.comp_aestronglyMeasurable
        (burnolYTransformed_memLp hlambda.1 hlambda.2 s k hs0 hs1).1
  have hbound : ∀ᶠ lambda : ℝ in l,
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ‖burnolTargetPairingIntegrand lambda s k t‖ ≤
          burnolTargetPairingMajor s k t := by
    filter_upwards [hlambda] with lambda hlambda
    exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      norm_burnolTargetPairingIntegrand_le hlambda.2 hs k ht
  have hpointwise : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun lambda : ℝ => burnolTargetPairingIntegrand lambda s k t)
        l (nhds (burnolTargetPairingIntegrand 0 s k t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hlt : ∀ᶠ lambda : ℝ in l, lambda < t :=
      (eventually_lt_nhds ht).filter_mono inf_le_left
    apply tendsto_const_nhds.congr'
    filter_upwards [hlt] with lambda hlambdaT
    have ht0 : t ∈ Ici (0 : ℝ) := by
      change 0 ≤ t
      exact ht.le
    unfold burnolTargetPairingIntegrand burnolYTransformed
    rw [Set.indicator_of_mem (show t ∈ Ici lambda from hlambdaT.le),
      Set.indicator_of_mem ht0]
  exact tendsto_integral_filter_of_dominated_convergence
    (burnolTargetPairingMajor s k) hmeas hbound
    (integrableOn_burnolTargetPairingMajor s k) hpointwise

theorem inner_burnolY_chiOne_eq_integral
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) :
    inner ℂ (burnolY lambda s k) burnolChiOneL2 =
      ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand lambda s k t := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  calc
    inner ℂ (burnolY lambda s k) burnolChiOneL2 =
        inner ℂ (burnolAPhaseL2 (burnolY lambda s k))
          (burnolAPhaseL2 burnolChiOneL2) :=
      (burnolAPhaseL2.inner_map_map (burnolY lambda s k) burnolChiOneL2).symm
    _ = inner ℂ (burnolYTransformedL2 lambda s k) burnolChiOnePhaseL2 := by
      rw [burnolAPhaseL2_burnolY, burnolAPhaseL2_chiOne]
    _ = ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand lambda s k t := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [burnolYTransformedL2_coeFn hlambda0 hlambda1 s k hs0 hs1,
        burnolChiOnePhaseL2_coeFn] with t hY hq
      rw [hY, hq, RCLike.inner_apply']
      unfold burnolTargetPairingIntegrand
      ring

def burnolLeftApproach (s : ℂ) (n : ℕ) : ℂ :=
  s - Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)

theorem tendsto_burnolLeftApproach (s : ℂ) :
    Tendsto (burnolLeftApproach s) atTop (nhds s) := by
  have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (nhds 0) := by
    have hbase := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 1)
    apply hbase.congr'
    exact Eventually.of_forall fun n => by
      simp [Function.comp_apply]
  have hcast : Tendsto (fun n : ℕ =>
      Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (nhds 0) := by
    have hbase := Complex.continuous_ofReal.continuousAt.tendsto.comp hinv
    apply hbase.congr'
    exact Eventually.of_forall fun n => by
      simp [Function.comp_apply]
  have hsconst : Tendsto (fun _ : ℕ => s) atTop (nhds s) :=
    tendsto_const_nhds
  have hsub := hsconst.sub hcast
  have hsub' : Tendsto (fun n : ℕ =>
      s - Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (nhds s) := by
    simpa only [sub_zero] using hsub
  change Tendsto (fun n : ℕ =>
    s - Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (nhds s)
  exact hsub'

theorem eventually_burnolLeftApproach_mem
    {s : ℂ} (hs : s.re = 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      0 < (burnolLeftApproach s n).re ∧
        (burnolLeftApproach s n).re < 1 / 2 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnthree : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have hinvpos : 0 < (((n + 1 : ℕ) : ℝ)⁻¹) := inv_pos.mpr hnpos
  have hinvthird : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (3 : ℝ)⁻¹ :=
    inv_anti₀ (by norm_num) hnthree
  norm_num only [Nat.cast_add, Nat.cast_one] at hinvpos hinvthird
  rw [burnolLeftApproach, Complex.sub_re]
  have hre :
      (Complex.ofReal (((n + 1 : ℕ) : ℝ)⁻¹)).re =
        (((n + 1 : ℕ) : ℝ)⁻¹) := rfl
  rw [hre]
  rw [hs]
  constructor <;> norm_num <;> linarith

def burnolTargetParameterMajor (CV CL : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator
      (fun u : ℝ => 4 * (CV * u ^ (-(3 / 4 : ℝ)) +
        4 * burnolPhiSeriesBound 0)) t +
    (Ioi (1 : ℝ)).indicator
      (fun u : ℝ => 8 * burnolChiOnePhaseLargeCoeff * CL *
        (u ^ (-2 : ℝ) + (Real.log u) ^ 4 * u ^ (-2 : ℝ))) t

theorem integrableOn_burnolTargetParameterMajor (CV CL : ℝ) :
    IntegrableOn (burnolTargetParameterMajor CV CL) (Ioi (0 : ℝ)) := by
  have hsmallWeight := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc
    0 (a := -(3 / 4 : ℝ)) (by norm_num)
  have hsmallOn : IntegrableOn
      (fun u : ℝ => 4 * (CV * u ^ (-(3 / 4 : ℝ)) +
        4 * burnolPhiSeriesBound 0)) (Ioc (0 : ℝ) 1) := by
    have hmain := hsmallWeight.const_mul (4 * CV)
    have hconst : IntegrableOn
        (fun _ : ℝ => 16 * burnolPhiSeriesBound 0) (Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    exact (hmain.add hconst).congr <| ae_of_all _ fun t => by
      simp only [pow_zero, one_mul, Pi.add_apply]
      ring
  have hlargeOn : IntegrableOn
      (fun u : ℝ => 8 * burnolChiOnePhaseLargeCoeff * CL *
        (u ^ (-2 : ℝ) + (Real.log u) ^ 4 * u ^ (-2 : ℝ)))
      (Ioi (1 : ℝ)) :=
    integrableOn_one_add_log_pow_four_mul_rpow_neg_two_Ioi.const_mul
      (8 * burnolChiOnePhaseLargeCoeff * CL)
  have hsmall := hsmallOn.integrable_indicator measurableSet_Ioc
  have hlarge := hlargeOn.integrable_indicator measurableSet_Ioi
  exact (hsmall.add hlarge).integrableOn.congr <|
    ae_of_all _ fun _ => rfl

theorem norm_burnolTargetPairingIntegrand_zero_le_parameterMajor
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1)
    (hwUpper : w.re ≤ 3 / 4)
    {CV CL : ℝ} (hCV0 : 0 ≤ CV) (hCL0 : 0 ≤ CL)
    (hCV : burnolVMainDerivCoeffBound w 0 ≤ CV)
    (hCL : burnolPhiHardySquareLargeCoeff w 0 ≤ CL)
    {t : ℝ} (ht : 0 < t) :
    ‖burnolTargetPairingIntegrand 0 w 0 t‖ ≤
      burnolTargetParameterMajor CV CL t := by
  have hQ0 := burnolChiOnePhaseLargeCoeff_nonneg
  rw [burnolTargetPairingIntegrand, norm_mul, Complex.norm_conj]
  by_cases ht1 : t ≤ 1
  · rw [burnolTargetParameterMajor,
      Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, ht1⟩),
      Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from
        fun h => (not_lt_of_ge ht1) h), add_zero]
    have herror := norm_burnolYTransformed_sub_gammaMain_le
      ht.le w 0 hw0 hw1 ht ht1
    have hmain := norm_iteratedDeriv_burnolPhiHardyGammaMain_le
      0 hw0 hw1 ht
    have hpow : t ^ (-w.re) ≤ t ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
    have hY : ‖burnolYTransformed 0 w 0 t‖ ≤
        CV * t ^ (-(3 / 4 : ℝ)) + 4 * burnolPhiSeriesBound 0 := by
      calc
        ‖burnolYTransformed 0 w 0 t‖ ≤
            ‖burnolYTransformed 0 w 0 t -
              iteratedDeriv 0 (burnolPhiHardyGammaMain t) w‖ +
            ‖iteratedDeriv 0 (burnolPhiHardyGammaMain t) w‖ := by
          nth_rewrite 1 [show burnolYTransformed 0 w 0 t =
              (burnolYTransformed 0 w 0 t -
                iteratedDeriv 0 (burnolPhiHardyGammaMain t) w) +
              iteratedDeriv 0 (burnolPhiHardyGammaMain t) w by ring]
          exact norm_add_le _ _
        _ ≤ 4 * burnolPhiSeriesBound 0 +
            burnolVMainDerivCoeffBound w 0 * t ^ (-w.re) := by
          simpa only [pow_zero, mul_one] using add_le_add herror hmain
        _ ≤ 4 * burnolPhiSeriesBound 0 + CV * t ^ (-(3 / 4 : ℝ)) := by
          gcongr
        _ = _ := by ring
    calc
      ‖burnolChiOnePhase t‖ * ‖burnolYTransformed 0 w 0 t‖ ≤
          4 * (CV * t ^ (-(3 / 4 : ℝ)) +
            4 * burnolPhiSeriesBound 0) := by
        exact mul_le_mul (norm_burnolChiOnePhase_le_four ht) hY
          (norm_nonneg _) (by positivity)
      _ = _ := rfl
  · have htLarge : t ∈ Ioi (1 : ℝ) := lt_of_not_ge ht1
    rw [burnolTargetParameterMajor,
      Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from
        fun h => ht1 h.2), Set.indicator_of_mem htLarge, zero_add]
    have hq := norm_burnolChiOnePhase_le_large htLarge.le
    have hYbase := norm_burnolYTransformed_le_large
      (show (0 : ℝ) ≤ 1 by norm_num) w 0 hw0 hw1 htLarge.le
    have hlog0 : 0 ≤ Real.log t := Real.log_nonneg htLarge.le
    have hY : ‖burnolYTransformed 0 w 0 t‖ ≤
        CL * (1 + Real.log t) ^ 2 / t := by
      have hYbase' : ‖burnolYTransformed 0 w 0 t‖ ≤
          burnolPhiHardySquareLargeCoeff w 0 *
            (1 + Real.log t) ^ 2 / t := by
        simpa only [abs_of_nonneg hlog0] using hYbase
      exact hYbase'.trans <| div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCL (pow_nonneg (by linarith) 2)) ht.le
    have hadd : (1 + Real.log t) ^ 4 ≤
        8 * (1 + (Real.log t) ^ 4) := by
      have h := add_pow_le (by norm_num : (0 : ℝ) ≤ 1) hlog0 4
      norm_num at h
      exact h
    have hinvSq : t⁻¹ ^ 2 = t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg ht.le]
      exact (inv_pow t 2).trans
        (congrArg Inv.inv (Real.rpow_natCast t 2).symm)
    calc
      ‖burnolChiOnePhase t‖ * ‖burnolYTransformed 0 w 0 t‖ ≤
          (burnolChiOnePhaseLargeCoeff * (1 + Real.log t) ^ 2 / t) *
            (CL * (1 + Real.log t) ^ 2 / t) := by
        exact mul_le_mul hq hY (norm_nonneg _) (by positivity)
      _ = burnolChiOnePhaseLargeCoeff * CL *
          (1 + Real.log t) ^ 4 * t ^ (-2 : ℝ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, hinvSq.symm]
        ring
      _ ≤ burnolChiOnePhaseLargeCoeff * CL *
          (8 * (1 + (Real.log t) ^ 4)) * t ^ (-2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hadd (mul_nonneg hQ0 hCL0))
          (Real.rpow_nonneg ht.le _)
      _ = _ := by ring

theorem integral_burnolTargetPairing_zero_eq_inner_source
    (w : ℂ) (hw0 : 0 < w.re) (hwHalf : w.re < 1 / 2) :
    (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 w 0 t) =
      inner ℂ (burnolPsiL2 w 0) burnolChiOneL2 := by
  have hw1 : w.re < 1 := hwHalf.trans (by norm_num)
  calc
    (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 w 0 t) =
        inner ℂ (burnolHardySquarePhiL2 w 0) burnolChiOnePhaseL2 := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [burnolHardySquarePhiL2_coeFn w 0 hw0 hwHalf,
        burnolChiOnePhaseL2_coeFn, ae_restrict_mem measurableSet_Ioi] with
          t hY hq ht
      have ht0 : t ∈ Ici (0 : ℝ) := by
        change 0 ≤ t
        exact ht.le
      rw [hY, hq, RCLike.inner_apply']
      unfold burnolTargetPairingIntegrand burnolYTransformed
      rw [Set.indicator_of_mem ht0]
      ring
    _ = inner ℂ (burnolAPhaseL2 (burnolPsiL2 w 0))
        (burnolAPhaseL2 burnolChiOneL2) := by
      rw [burnolAPhaseL2_burnolPsiL2_eq_hardySquare w 0 hw0 hwHalf,
        burnolAPhaseL2_chiOne]
    _ = inner ℂ (burnolPsiL2 w 0) burnolChiOneL2 :=
      burnolAPhaseL2.inner_map_map (burnolPsiL2 w 0) burnolChiOneL2

theorem tendsto_integral_burnolTargetPairing_leftApproach
    {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun n : ℕ =>
      ∫ t : ℝ in Ioi 0,
        burnolTargetPairingIntegrand 0 (burnolLeftApproach s n) 0 t)
      atTop
      (nhds (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 s 0 t)) := by
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s.re < 1 := by rw [hs]; norm_num
  let W := burnolLeftApproach s
  have hW : Tendsto W atTop (nhds s) := tendsto_burnolLeftApproach s
  obtain ⟨CV, hCV0, hCV⟩ :=
    eventually_burnolVMainDerivCoeffBound_le s 0 hs0 hs1
  obtain ⟨CL, hCL0, hCL⟩ :=
    eventually_burnolPhiHardySquareLargeCoeff_le s 0 hs0 hs1
  have hmem := eventually_burnolLeftApproach_mem hs
  have hupper : ∀ᶠ n : ℕ in atTop, (W n).re ≤ 3 / 4 := by
    have hnhds : {w : ℂ | w.re < 3 / 4} ∈ nhds s := by
      apply (isOpen_lt Complex.continuous_re continuous_const).mem_nhds
      change s.re < 3 / 4
      rw [hs]
      norm_num
    exact (hW.eventually hnhds).mono fun _ h => h.le
  have hCV' := hW.eventually hCV
  have hCL' := hW.eventually hCL
  have hnear : ∀ᶠ n : ℕ in atTop,
      0 < (W n).re ∧ (W n).re < 1 ∧ (W n).re ≤ 3 / 4 ∧
        burnolVMainDerivCoeffBound (W n) 0 ≤ CV ∧
        burnolPhiHardySquareLargeCoeff (W n) 0 ≤ CL := by
    filter_upwards [hmem, hupper, hCV', hCL'] with n hn hu hcv hcl
    exact ⟨hn.1, hn.2.trans (by norm_num), hu, hcv.2, hcl.2⟩
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable
        (burnolTargetPairingIntegrand 0 (W n) 0)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hnear] with n hn
    exact aestronglyMeasurable_burnolChiOnePhase_Ioi.mul <|
      Complex.continuous_conj.comp_aestronglyMeasurable
        (aestronglyMeasurable_burnolYTransformed 0 (W n) 0 hn.1 hn.2.1)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ‖burnolTargetPairingIntegrand 0 (W n) 0 t‖ ≤
          burnolTargetParameterMajor CV CL t := by
    filter_upwards [hnear] with n hn
    exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
      norm_burnolTargetPairingIntegrand_zero_le_parameterMajor
        hn.1 hn.2.1 hn.2.2.1 hCV0 hCL0 hn.2.2.2.1 hn.2.2.2.2 ht
  have hpointwise : ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n : ℕ => burnolTargetPairingIntegrand 0 (W n) 0 t)
        atTop (nhds (burnolTargetPairingIntegrand 0 s 0 t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hy := (continuousAt_burnolYTransformed_parameter
      0 s 0 hs0 hs1 ht).tendsto.comp hW
    have hyConj : Tendsto (fun n : ℕ =>
        conj (burnolYTransformed 0 (W n) 0 t)) atTop
        (nhds (conj (burnolYTransformed 0 s 0 t))) := by
      have hbase := Complex.continuous_conj.continuousAt.tendsto.comp hy
      apply hbase.congr'
      exact Eventually.of_forall fun n => by
        simp [Function.comp_apply]
    simpa only [burnolTargetPairingIntegrand] using
      tendsto_const_nhds.mul hyConj
  exact tendsto_integral_filter_of_dominated_convergence
    (burnolTargetParameterMajor CV CL) hmeas hbound
    (integrableOn_burnolTargetParameterMajor CV CL) hpointwise

theorem integral_burnolTargetPairing_zero_zero
    {s : ℂ} (hs : s.re = 1 / 2) :
    (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 s 0 t) =
      (s - 1) / s ^ 2 := by
  let W := burnolLeftApproach s
  have hmem := eventually_burnolLeftApproach_mem hs
  have hwithin : Tendsto W atTop
      (nhdsWithin s {w : ℂ | 0 < w.re ∧ w.re < 1 / 2}) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_burnolLeftApproach s, hmem⟩
  have hsource := (tendsto_inner_burnolPsiL2_zero_chiOne hs).comp hwithin
  have heq : (fun n : ℕ =>
      ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 (W n) 0 t) =ᶠ[atTop]
        fun n : ℕ => inner ℂ (burnolPsiL2 (W n) 0) burnolChiOneL2 := by
    filter_upwards [hmem] with n hn
    exact integral_burnolTargetPairing_zero_eq_inner_source (W n) hn.1 hn.2
  have hvalue : Tendsto (fun n : ℕ =>
      ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 (W n) 0 t)
      atTop (nhds ((s - 1) / s ^ 2)) :=
    hsource.congr' heq.symm
  have hphysical : Tendsto (fun n : ℕ =>
      ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 (W n) 0 t)
      atTop
      (nhds (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 s 0 t)) := by
    simpa only [W] using tendsto_integral_burnolTargetPairing_leftApproach hs
  exact tendsto_nhds_unique hphysical hvalue

theorem tendsto_inner_burnolY_chiOne
    {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) :
    Tendsto (fun lambda : ℝ => inner ℂ (burnolY lambda s k) burnolChiOneL2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand 0 s k t)) := by
  let l := nhdsWithin (0 : ℝ) (Ioi 0)
  have hlt : ∀ᶠ lambda : ℝ in l, lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  have heq : (fun lambda : ℝ =>
      inner ℂ (burnolY lambda s k) burnolChiOneL2) =ᶠ[l]
        fun lambda : ℝ =>
          ∫ t : ℝ in Ioi 0, burnolTargetPairingIntegrand lambda s k t := by
    filter_upwards [eventually_mem_nhdsWithin, hlt] with lambda h0 h1
    exact inner_burnolY_chiOne_eq_integral h0 h1.le hs k
  exact (tendsto_integral_burnolTargetPairingIntegrand hs k).congr' heq.symm

theorem tendsto_inner_burnolY_zero_chiOne
    {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun lambda : ℝ => inner ℂ (burnolY lambda s 0) burnolChiOneL2)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((s - 1) / s ^ 2)) := by
  simpa only [integral_burnolTargetPairing_zero_zero hs] using
    tendsto_inner_burnolY_chiOne hs 0

theorem sqrtLogScale_mul_inner_burnolX_chiOne_eq
    {lambda : ℝ} (hscale : 0 < burnolLogScale lambda)
    (s : ℂ) (k : ℕ) :
    ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
        inner ℂ (burnolX lambda s k) burnolChiOneL2 =
      (((burnolLogScale lambda) ^ (-(k : ℝ)) : ℝ) : ℂ) *
        inner ℂ (burnolY lambda s k) burnolChiOneL2 := by
  rw [burnolX, inner_smul_left]
  simp only [Complex.conj_ofReal]
  have hscalar : Real.sqrt (burnolLogScale lambda) *
      (burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) =
        (burnolLogScale lambda) ^ (-(k : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hscale]
    congr 1
    ring
  calc
    ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
        ((((burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) *
          inner ℂ (burnolY lambda s k) burnolChiOneL2) =
      ((Real.sqrt (burnolLogScale lambda) *
          (burnolLogScale lambda) ^ (-(k : ℝ) - 1 / 2 : ℝ) : ℝ) : ℂ) *
        inner ℂ (burnolY lambda s k) burnolChiOneL2 := by
          push_cast
          ring
    _ = _ := by rw [hscalar]

theorem tendsto_sqrtLog_inner_chiOne_burnolX
    {s : ℂ} (hs : s.re = 1 / 2) (k : ℕ) :
    Tendsto (fun lambda : ℝ =>
      ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
        inner ℂ (burnolX lambda s k) burnolChiOneL2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (if k = 0 then (s - 1) / s ^ 2 else 0)) := by
  let l := nhdsWithin (0 : ℝ) (Ioi 0)
  have heq : (fun lambda : ℝ =>
      ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
        inner ℂ (burnolX lambda s k) burnolChiOneL2) =ᶠ[l]
      fun lambda : ℝ =>
        (((burnolLogScale lambda) ^ (-(k : ℝ)) : ℝ) : ℂ) *
          inner ℂ (burnolY lambda s k) burnolChiOneL2 := by
    filter_upwards [eventually_burnolLogScale_pos] with lambda hscale
    exact sqrtLogScale_mul_inner_burnolX_chiOne_eq hscale s k
  cases k with
  | zero =>
      have heq0 := heq
      simp only [Nat.cast_zero] at heq0
      have hbase := tendsto_inner_burnolY_zero_chiOne hs
      have hprod : Tendsto (fun lambda : ℝ =>
          (((burnolLogScale lambda) ^ (-(0 : ℝ)) : ℝ) : ℂ) *
            inner ℂ (burnolY lambda s 0) burnolChiOneL2)
          l (nhds ((s - 1) / s ^ 2)) := by
        simpa using hbase
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero,
        Complex.ofReal_one, one_mul, ite_true] using hprod.congr' heq0.symm
  | succ n =>
      have hfactorReal : Tendsto (fun lambda : ℝ =>
          (burnolLogScale lambda) ^ (-((n + 1 : ℕ) : ℝ)))
          l (nhds 0) :=
        tendsto_burnolLogScale_rpow_neg (by positivity)
      have hfactor : Tendsto (fun lambda : ℝ =>
          (((burnolLogScale lambda) ^ (-((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ))
          l (nhds 0) := by
        have hbase := Complex.continuous_ofReal.continuousAt.tendsto.comp hfactorReal
        apply hbase.congr'
        exact Eventually.of_forall fun lambda => by
          simp [Function.comp_apply]
      have hinner := tendsto_inner_burnolY_chiOne hs (n + 1)
      have hprod := hfactor.mul hinner
      simpa only [Nat.cast_succ, Nat.succ_eq_add_one,
        Nat.succ_ne_zero, ite_false, zero_mul] using
        hprod.congr' heq.symm

/-! ## Finite matrix limits -/

def burnolHilbertMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ((((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ)⁻¹ : ℝ)

/-- The nonnegative row nodes in the Cauchy presentation of the Hilbert matrix. -/
def burnolHilbertRowNode {m : ℕ} (i : Fin m) : ℂ :=
  ((i : ℕ) : ℂ)

/-- The negative pole nodes in the Cauchy presentation of the Hilbert matrix. -/
def burnolHilbertPoleNode {m : ℕ} (j : Fin m) : ℂ :=
  -(((j : ℕ) + 1 : ℕ) : ℂ)

theorem burnolHilbertRowNode_injective (m : ℕ) :
    Function.Injective (@burnolHilbertRowNode m) := by
  intro i j hij
  apply Fin.ext
  change (((i : ℕ) : ℂ) = ((j : ℕ) : ℂ)) at hij
  exact_mod_cast hij

theorem burnolHilbertPoleNode_injective (m : ℕ) :
    Function.Injective (@burnolHilbertPoleNode m) := by
  intro i j hij
  apply Fin.ext
  change (-(((i : ℕ) + 1 : ℕ) : ℂ) = -(((j : ℕ) + 1 : ℕ) : ℂ)) at hij
  have hadd : ((i : ℕ) + 1 : ℕ) = (j : ℕ) + 1 := by
    exact_mod_cast neg_inj.mp hij
  exact Nat.add_right_cancel hadd

theorem burnolHilbertRowNode_ne_poleNode {m : ℕ} (i j : Fin m) :
    burnolHilbertRowNode i ≠ burnolHilbertPoleNode j := by
  intro hij
  have hre := congrArg Complex.re hij
  simp only [burnolHilbertRowNode, burnolHilbertPoleNode, Complex.natCast_re,
    Complex.neg_re] at hre
  have hnonneg : 0 ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpos : 0 < (((j : ℕ) + 1 : ℕ) : ℝ) := by positivity
  linarith

theorem burnolHilbertMatrix_apply_cauchy {m : ℕ} (i j : Fin m) :
    burnolHilbertMatrix m i j =
      (burnolHilbertRowNode i - burnolHilbertPoleNode j)⁻¹ := by
  simp only [burnolHilbertMatrix, burnolHilbertRowNode, burnolHilbertPoleNode,
    sub_neg_eq_add]
  push_cast
  congr 1
  ring

/-- The pole-node polynomial used in the Cauchy inverse calculation. -/
def burnolHilbertPoleNodal (m : ℕ) : Polynomial ℂ :=
  Lagrange.nodal Finset.univ (@burnolHilbertPoleNode m)

/-- The row-node interpolant which is zero except at the selected row. -/
def burnolHilbertRowPolynomial (m : ℕ) (r : Fin m) : Polynomial ℂ :=
  Lagrange.interpolate Finset.univ (@burnolHilbertRowNode m) fun i =>
    if i = r then (burnolHilbertPoleNodal m).eval (burnolHilbertRowNode r) else 0

/-- The Cauchy inverse candidate obtained from the pole-node barycentric weights. -/
def burnolHilbertInverseCandidate (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun j r =>
    Lagrange.nodalWeight Finset.univ (@burnolHilbertPoleNode m) j *
      (burnolHilbertRowPolynomial m r).eval (burnolHilbertPoleNode j)

theorem eval_burnolHilbertRowPolynomial (m : ℕ) (i r : Fin m) :
    (burnolHilbertRowPolynomial m r).eval (burnolHilbertRowNode i) =
      if i = r then
        (burnolHilbertPoleNodal m).eval (burnolHilbertRowNode r) else 0 := by
  exact Lagrange.eval_interpolate_at_node _
    (burnolHilbertRowNode_injective m).injOn (Finset.mem_univ i)

theorem degree_burnolHilbertRowPolynomial_lt (m : ℕ) (r : Fin m) :
    (burnolHilbertRowPolynomial m r).degree < m := by
  simpa [burnolHilbertRowPolynomial] using
    Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin m)))
      (v := @burnolHilbertRowNode m)
      (r := fun i => if i = r then
        (burnolHilbertPoleNodal m).eval (burnolHilbertRowNode r) else 0)
      (burnolHilbertRowNode_injective m).injOn

theorem eval_burnolHilbertPoleNodal_row_ne_zero
    {m : ℕ} (i : Fin m) :
    (burnolHilbertPoleNodal m).eval (burnolHilbertRowNode i) ≠ 0 := by
  exact Lagrange.eval_nodal_not_at_node fun j _ =>
    burnolHilbertRowNode_ne_poleNode i j

theorem burnolHilbert_barycentric_sum (m : ℕ) (i r : Fin m) :
    (∑ j : Fin m,
      Lagrange.nodalWeight Finset.univ (@burnolHilbertPoleNode m) j *
        (burnolHilbertRowNode i - burnolHilbertPoleNode j)⁻¹ *
          (burnolHilbertRowPolynomial m r).eval (burnolHilbertPoleNode j)) =
      if i = r then 1 else 0 := by
  have hdegree : (burnolHilbertRowPolynomial m r).degree <
      (Finset.univ : Finset (Fin m)).card := by
    simpa using degree_burnolHilbertRowPolynomial_lt m r
  have hinterpolate : burnolHilbertRowPolynomial m r =
      Lagrange.interpolate Finset.univ (@burnolHilbertPoleNode m) fun j =>
        (burnolHilbertRowPolynomial m r).eval (burnolHilbertPoleNode j) :=
    Lagrange.eq_interpolate (burnolHilbertPoleNode_injective m).injOn hdegree
  have hbarycentric := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin m)))
    (v := @burnolHilbertPoleNode m)
    (x := burnolHilbertRowNode i)
    (fun j => (burnolHilbertRowPolynomial m r).eval (burnolHilbertPoleNode j))
    (fun j _ => burnolHilbertRowNode_ne_poleNode i j)
  rw [← hinterpolate] at hbarycentric
  have hnodal : (burnolHilbertPoleNodal m).eval (burnolHilbertRowNode i) ≠ 0 :=
    eval_burnolHilbertPoleNodal_row_ne_zero i
  have hsum :
      (∑ j : Fin m,
        Lagrange.nodalWeight Finset.univ (@burnolHilbertPoleNode m) j *
          (burnolHilbertRowNode i - burnolHilbertPoleNode j)⁻¹ *
            (burnolHilbertRowPolynomial m r).eval (burnolHilbertPoleNode j)) =
        (burnolHilbertRowPolynomial m r).eval (burnolHilbertRowNode i) /
          (burnolHilbertPoleNodal m).eval (burnolHilbertRowNode i) := by
    apply (eq_div_iff hnodal).2
    rw [mul_comm]
    simpa [burnolHilbertPoleNodal] using hbarycentric.symm
  rw [hsum, eval_burnolHilbertRowPolynomial]
  by_cases hir : i = r
  · subst r
    simpa using div_self (eval_burnolHilbertPoleNodal_row_ne_zero i)
  · simp [hir]

theorem burnolHilbertMatrix_mul_inverseCandidate (m : ℕ) :
    burnolHilbertMatrix m * burnolHilbertInverseCandidate m = 1 := by
  ext i r
  rw [Matrix.mul_apply]
  calc
    (∑ j : Fin m,
        burnolHilbertMatrix m i j * burnolHilbertInverseCandidate m j r) =
        ∑ j : Fin m,
          Lagrange.nodalWeight Finset.univ (@burnolHilbertPoleNode m) j *
            (burnolHilbertRowNode i - burnolHilbertPoleNode j)⁻¹ *
              (burnolHilbertRowPolynomial m r).eval (burnolHilbertPoleNode j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [burnolHilbertMatrix_apply_cauchy, burnolHilbertInverseCandidate]
      ring
    _ = if i = r then 1 else 0 := burnolHilbert_barycentric_sum m i r
    _ = (1 : Matrix (Fin m) (Fin m) ℂ) i r := by
      simp only [Matrix.one_apply]

theorem burnolHilbertMatrix_det_ne_zero (m : ℕ) :
    (burnolHilbertMatrix m).det ≠ 0 := by
  intro hdet
  have h := congrArg Matrix.det (burnolHilbertMatrix_mul_inverseCandidate m)
  rw [Matrix.det_mul, hdet, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

theorem burnolHilbertMatrix_isUnit_det (m : ℕ) :
    IsUnit (burnolHilbertMatrix m).det :=
  isUnit_iff_ne_zero.mpr (burnolHilbertMatrix_det_ne_zero m)

theorem burnolHilbertMatrix_inv_eq_inverseCandidate (m : ℕ) :
    (burnolHilbertMatrix m)⁻¹ = burnolHilbertInverseCandidate m := by
  have hunit : IsUnit (burnolHilbertMatrix m).det :=
    isUnit_iff_ne_zero.mpr (burnolHilbertMatrix_det_ne_zero m)
  calc
    (burnolHilbertMatrix m)⁻¹ = (burnolHilbertMatrix m)⁻¹ * 1 := by rw [mul_one]
    _ = (burnolHilbertMatrix m)⁻¹ *
        (burnolHilbertMatrix m * burnolHilbertInverseCandidate m) := by
      rw [burnolHilbertMatrix_mul_inverseCandidate]
    _ = ((burnolHilbertMatrix m)⁻¹ * burnolHilbertMatrix m) *
        burnolHilbertInverseCandidate m := by rw [Matrix.mul_assoc]
    _ = burnolHilbertInverseCandidate m := by
      rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]

theorem eval_burnolHilbertPoleNodal_zero (n : ℕ) :
    (burnolHilbertPoleNodal (n + 1)).eval
        (burnolHilbertRowNode (0 : Fin (n + 1))) = ((n + 1).factorial : ℂ) := by
  rw [burnolHilbertPoleNodal, Lagrange.eval_nodal]
  simp only [burnolHilbertRowNode, burnolHilbertPoleNode,
    Fin.val_zero, Nat.cast_zero, zero_sub, neg_neg]
  rw [Fin.prod_univ_eq_prod_range (fun i => (((i + 1 : ℕ) : ℕ) : ℂ)) (n + 1)]
  norm_cast
  exact Finset.prod_range_add_one_eq_factorial (n + 1)

theorem burnolHilbertPoleWeight_zero (n : ℕ) :
    Lagrange.nodalWeight Finset.univ (@burnolHilbertPoleNode (n + 1))
        (0 : Fin (n + 1)) = ((n.factorial : ℂ))⁻¹ := by
  rw [Lagrange.nodalWeight]
  have herase : (Finset.univ : Finset (Fin (n + 1))).erase 0 = Finset.Ioi 0 := by
    ext j
    simp
  rw [herase, Fin.Ioi_zero_eq_map, Finset.prod_map]
  change (∏ j : Fin n,
      (burnolHilbertPoleNode (0 : Fin (n + 1)) -
        burnolHilbertPoleNode j.succ)⁻¹) = ((n.factorial : ℂ))⁻¹
  calc
    _ = ∏ j : Fin n, ((((j : ℕ) + 1 : ℕ) : ℂ))⁻¹ := by
      apply Finset.prod_congr rfl
      intro j _
      congr 1
      simp only [burnolHilbertPoleNode, Fin.val_zero, Fin.val_succ]
      push_cast
      ring
    _ = ((n.factorial : ℂ))⁻¹ := by
      rw [Finset.prod_inv_distrib]
      congr 1
      rw [Fin.prod_univ_eq_prod_range (fun i => (((i + 1 : ℕ) : ℕ) : ℂ)) n]
      norm_cast
      exact Finset.prod_range_add_one_eq_factorial n

theorem prod_range_burnolHilbert_ratio (n : ℕ) :
    (∏ j ∈ Finset.range n,
      ((((j + 2 : ℕ) : ℕ) : ℂ) / (((j + 1 : ℕ) : ℕ) : ℂ))) =
        ((n + 1 : ℕ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      have hne : (((n + 1 : ℕ) : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      field_simp

theorem eval_burnolHilbertRowBasis_zero (n : ℕ) :
    (Lagrange.basis (Finset.univ : Finset (Fin (n + 1)))
      (@burnolHilbertRowNode (n + 1)) (0 : Fin (n + 1))).eval
        (burnolHilbertPoleNode (0 : Fin (n + 1))) = ((n + 1 : ℕ) : ℂ) := by
  rw [Lagrange.basis, Polynomial.eval_prod]
  have herase : (Finset.univ : Finset (Fin (n + 1))).erase 0 = Finset.Ioi 0 := by
    ext j
    simp
  rw [herase, Fin.Ioi_zero_eq_map, Finset.prod_map]
  change (∏ j : Fin n,
      (Lagrange.basisDivisor
        (burnolHilbertRowNode (0 : Fin (n + 1)))
        (burnolHilbertRowNode j.succ)).eval
          (burnolHilbertPoleNode (0 : Fin (n + 1)))) = ((n + 1 : ℕ) : ℂ)
  calc
    _ = ∏ j : Fin n,
        ((((j : ℕ) + 2 : ℕ) : ℂ) / (((j : ℕ) + 1 : ℕ) : ℂ)) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [Lagrange.basisDivisor]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_X, burnolHilbertRowNode, burnolHilbertPoleNode,
        Fin.val_zero, Fin.val_succ, Nat.cast_zero]
      push_cast
      rw [show ((0 : ℂ) - (↑(j : ℕ) + 1)) = -(↑(j : ℕ) + 1) by ring,
        inv_neg]
      ring
    _ = ((n + 1 : ℕ) : ℂ) := by
      rw [Fin.prod_univ_eq_prod_range
        (fun j => ((((j + 2 : ℕ) : ℕ) : ℂ) /
          (((j + 1 : ℕ) : ℕ) : ℂ))) n]
      exact prod_range_burnolHilbert_ratio n

theorem eval_burnolHilbertRowPolynomial_zero (n : ℕ) :
    (burnolHilbertRowPolynomial (n + 1) (0 : Fin (n + 1))).eval
        (burnolHilbertPoleNode (0 : Fin (n + 1))) =
      ((n + 1).factorial : ℂ) * ((n + 1 : ℕ) : ℂ) := by
  rw [burnolHilbertRowPolynomial, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp only [if_pos, Polynomial.eval_mul, Polynomial.eval_C]
    rw [eval_burnolHilbertPoleNodal_zero, eval_burnolHilbertRowBasis_zero]
  · intro b _ hb
    simp [hb]
  · simp

theorem burnolHilbertInverseCandidate_zero_zero (n : ℕ) :
    burnolHilbertInverseCandidate (n + 1) (0 : Fin (n + 1)) (0 : Fin (n + 1)) =
      (((n + 1 : ℕ) : ℂ)) ^ 2 := by
  rw [burnolHilbertInverseCandidate, burnolHilbertPoleWeight_zero,
    eval_burnolHilbertRowPolynomial_zero, Nat.factorial_succ]
  push_cast
  have hfac : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem burnolHilbertMatrix_inv_zero_zero (n : ℕ) :
    (burnolHilbertMatrix (n + 1))⁻¹ (0 : Fin (n + 1)) (0 : Fin (n + 1)) =
      (((n + 1 : ℕ) : ℂ)) ^ 2 := by
  rw [burnolHilbertMatrix_inv_eq_inverseCandidate]
  exact burnolHilbertInverseCandidate_zero_zero n

def burnolGramMatrix (lambda : ℝ) (s : ℂ) (m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => inner ℂ (burnolX lambda s (j : ℕ))
    (burnolX lambda s (i : ℕ))

theorem tendsto_matrix_of_tendsto_apply
    {X ι : Type*} {l : Filter X}
    {A : X → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : ∀ i j, Tendsto (fun x => A x i j) l (nhds (B i j))) :
    Tendsto A l (nhds B) := by
  change Tendsto (fun x i j => A x i j) l (nhds fun i j => B i j)
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  exact hA i

theorem tendsto_burnolGramMatrix
    {s : ℂ} (hs : s.re = 1 / 2) (m : ℕ) :
    Tendsto (fun lambda : ℝ => burnolGramMatrix lambda s m)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (burnolHilbertMatrix m)) := by
  apply tendsto_matrix_of_tendsto_apply
  intro i j
  simpa [burnolGramMatrix, burnolHilbertMatrix] using
    tendsto_inner_burnolX hs hs (i : ℕ) (j : ℕ)

theorem tendsto_matrix_nonsingInv
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter X} {A : X → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : Tendsto A l (nhds B)) (hdet : B.det ≠ 0) :
    Tendsto (fun x => (A x)⁻¹) l (nhds B⁻¹) := by
  have hinv : ContinuousAt Ring.inverse B.det := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  exact (continuousAt_matrix_inv B hinv).tendsto.comp hA

theorem tendsto_matrix_nonsingInv_apply
    {ι X : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter X} {A : X → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (hA : Tendsto A l (nhds B)) (hdet : B.det ≠ 0) (i j : ι) :
    Tendsto (fun x => (A x)⁻¹ i j) l (nhds (B⁻¹ i j)) := by
  have hentry : Continuous (fun M : Matrix ι ι ℂ => M i j) :=
    (continuous_apply j).comp (continuous_apply i)
  exact hentry.continuousAt.tendsto.comp
    (tendsto_matrix_nonsingInv hA hdet)

theorem tendsto_burnolGramMatrix_inv
    {s : ℂ} (hs : s.re = 1 / 2) (m : ℕ) :
    Tendsto (fun lambda : ℝ => (burnolGramMatrix lambda s m)⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolHilbertMatrix m)⁻¹) :=
  tendsto_matrix_nonsingInv (tendsto_burnolGramMatrix hs m)
    (burnolHilbertMatrix_det_ne_zero m)

/-! ### Several distinct critical parameters -/

section BurnolBlockGram

variable {ι : Type*} [DecidableEq ι]

/-- The Gram matrix for a finite family of critical parameters, retaining derivatives below `m`. -/
def burnolBlockGramMatrix
    (lambda : ℝ) (rho : ι → ℂ) (m : ℕ) :
    Matrix (Fin m × ι) (Fin m × ι) ℂ :=
  fun i j => inner ℂ (burnolX lambda (rho j.2) (j.1 : ℕ))
    (burnolX lambda (rho i.2) (i.1 : ℕ))

/-- The block-diagonal Hilbert limit, with one `m × m` block for each parameter. -/
def burnolHilbertBlockMatrix (m : ℕ) :
    Matrix (Fin m × ι) (Fin m × ι) ℂ :=
  Matrix.blockDiagonal fun _ : ι => burnolHilbertMatrix m

theorem tendsto_burnolBlockGramMatrix
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (m : ℕ) :
    Tendsto (fun lambda : ℝ => burnolBlockGramMatrix lambda rho m)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolHilbertBlockMatrix (ι := ι) m)) := by
  apply tendsto_matrix_of_tendsto_apply
  intro i j
  have hscalar := tendsto_inner_burnolX
    (hcritical i.2) (hcritical j.2) (i.1 : ℕ) (j.1 : ℕ)
  by_cases hij : i.2 = j.2
  · have hrho : rho i.2 = rho j.2 := congrArg rho hij
    simpa [burnolBlockGramMatrix, burnolHilbertBlockMatrix,
      Matrix.blockDiagonal_apply, burnolHilbertMatrix, hij, hrho] using hscalar
  · have hrho : rho i.2 ≠ rho j.2 := fun h => hij (hinjective h)
    simpa [burnolBlockGramMatrix, burnolHilbertBlockMatrix,
      Matrix.blockDiagonal_apply, hij, hrho] using hscalar

theorem burnolHilbertBlockMatrix_det_ne_zero [Fintype ι] (m : ℕ) :
    (burnolHilbertBlockMatrix (ι := ι) m).det ≠ 0 := by
  rw [burnolHilbertBlockMatrix, Matrix.det_blockDiagonal]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => burnolHilbertMatrix_det_ne_zero m

theorem burnolHilbertBlockMatrix_isUnit_det [Fintype ι] (m : ℕ) :
    IsUnit (burnolHilbertBlockMatrix (ι := ι) m).det :=
  isUnit_iff_ne_zero.mpr (burnolHilbertBlockMatrix_det_ne_zero m)

theorem burnolHilbertBlockMatrix_inv [Fintype ι] (m : ℕ) :
    (burnolHilbertBlockMatrix (ι := ι) m)⁻¹ =
      Matrix.blockDiagonal (fun _ : ι => (burnolHilbertMatrix m)⁻¹) := by
  let B := burnolHilbertBlockMatrix (ι := ι) m
  let C := Matrix.blockDiagonal (fun _ : ι => (burnolHilbertMatrix m)⁻¹)
  have hmul : B * C = 1 := by
    dsimp [B, C, burnolHilbertBlockMatrix]
    rw [← Matrix.blockDiagonal_mul]
    simp only [Matrix.mul_nonsing_inv _ (burnolHilbertMatrix_isUnit_det m)]
    change Matrix.blockDiagonal (1 : ι → Matrix (Fin m) (Fin m) ℂ) = 1
    exact Matrix.blockDiagonal_one
  calc
    B⁻¹ = B⁻¹ * 1 := by rw [mul_one]
    _ = B⁻¹ * (B * C) := by rw [hmul]
    _ = (B⁻¹ * B) * C := by rw [Matrix.mul_assoc]
    _ = C := by
      rw [Matrix.nonsing_inv_mul B (burnolHilbertBlockMatrix_isUnit_det m),
        Matrix.one_mul]

theorem tendsto_burnolBlockGramMatrix_inv
    [Fintype ι]
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (m : ℕ) :
    Tendsto (fun lambda : ℝ => (burnolBlockGramMatrix lambda rho m)⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolHilbertBlockMatrix (ι := ι) m)⁻¹) :=
  tendsto_matrix_nonsingInv
    (tendsto_burnolBlockGramMatrix hcritical hinjective m)
    (burnolHilbertBlockMatrix_det_ne_zero m)

theorem burnolHilbertBlockMatrix_inv_zero_zero
    [Fintype ι] (a : ι) (n : ℕ) :
    (burnolHilbertBlockMatrix (ι := ι) (n + 1))⁻¹
        ((0 : Fin (n + 1)), a) ((0 : Fin (n + 1)), a) =
      (((n + 1 : ℕ) : ℂ)) ^ 2 := by
  rw [burnolHilbertBlockMatrix_inv]
  simp only [Matrix.blockDiagonal_apply_eq,
    burnolHilbertMatrix_inv_zero_zero]

/-! ### Parameter-dependent multiplicities -/

/-- The source-level finite Gram matrix when each critical parameter has its own multiplicity. -/
def burnolFiniteGramMatrix
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    Matrix (Σ a, Fin (multiplicity a)) (Σ a, Fin (multiplicity a)) ℂ :=
  fun i j => inner ℂ (burnolX lambda (rho j.1) (j.2 : ℕ))
    (burnolX lambda (rho i.1) (i.2 : ℕ))

/-- The unequal-size block-diagonal Hilbert limit for source multiplicities. -/
def burnolFiniteHilbertMatrix (multiplicity : ι → ℕ) :
    Matrix (Σ a, Fin (multiplicity a)) (Σ a, Fin (multiplicity a)) ℂ :=
  Matrix.blockDiagonal' fun a : ι => burnolHilbertMatrix (multiplicity a)

theorem tendsto_burnolFiniteGramMatrix
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      burnolFiniteGramMatrix lambda rho multiplicity)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolFiniteHilbertMatrix multiplicity)) := by
  apply tendsto_matrix_of_tendsto_apply
  rintro ⟨a, i⟩ ⟨b, j⟩
  have hscalar := tendsto_inner_burnolX
    (hcritical a) (hcritical b) (i : ℕ) (j : ℕ)
  by_cases hab : a = b
  · subst b
    simpa [burnolFiniteGramMatrix, burnolFiniteHilbertMatrix,
      Matrix.blockDiagonal'_apply, burnolHilbertMatrix] using hscalar
  · have hrho : rho a ≠ rho b := fun h => hab (hinjective h)
    simpa [burnolFiniteGramMatrix, burnolFiniteHilbertMatrix,
      Matrix.blockDiagonal'_apply, hab, hrho] using hscalar

theorem burnolFiniteHilbertMatrix_mul_blockInverse
    [Fintype ι] (multiplicity : ι → ℕ) :
    burnolFiniteHilbertMatrix multiplicity *
        Matrix.blockDiagonal'
          (fun a : ι => (burnolHilbertMatrix (multiplicity a))⁻¹) = 1 := by
  rw [burnolFiniteHilbertMatrix, ← Matrix.blockDiagonal'_mul]
  simp only [Matrix.mul_nonsing_inv _
    (burnolHilbertMatrix_isUnit_det (multiplicity _))]
  change Matrix.blockDiagonal'
    (1 : ∀ a : ι, Matrix (Fin (multiplicity a)) (Fin (multiplicity a)) ℂ) = 1
  exact Matrix.blockDiagonal'_one

theorem burnolFiniteHilbertMatrix_det_ne_zero
    [Fintype ι] (multiplicity : ι → ℕ) :
    (burnolFiniteHilbertMatrix multiplicity).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse
    (burnolFiniteHilbertMatrix_mul_blockInverse multiplicity)

theorem burnolFiniteHilbertMatrix_isUnit_det
    [Fintype ι] (multiplicity : ι → ℕ) :
    IsUnit (burnolFiniteHilbertMatrix multiplicity).det :=
  isUnit_iff_ne_zero.mpr
    (burnolFiniteHilbertMatrix_det_ne_zero multiplicity)

theorem burnolFiniteHilbertMatrix_inv
    [Fintype ι] (multiplicity : ι → ℕ) :
    (burnolFiniteHilbertMatrix multiplicity)⁻¹ =
      Matrix.blockDiagonal'
        (fun a : ι => (burnolHilbertMatrix (multiplicity a))⁻¹) := by
  let B := burnolFiniteHilbertMatrix multiplicity
  let C := Matrix.blockDiagonal'
    (fun a : ι => (burnolHilbertMatrix (multiplicity a))⁻¹)
  have hmul : B * C = 1 :=
    burnolFiniteHilbertMatrix_mul_blockInverse multiplicity
  calc
    B⁻¹ = B⁻¹ * 1 := by rw [mul_one]
    _ = B⁻¹ * (B * C) := by rw [hmul]
    _ = (B⁻¹ * B) * C := by rw [Matrix.mul_assoc]
    _ = C := by
      rw [Matrix.nonsing_inv_mul B
        (burnolFiniteHilbertMatrix_isUnit_det multiplicity), Matrix.one_mul]

theorem tendsto_burnolFiniteGramMatrix_inv
    [Fintype ι] {rho : ι → ℂ}
    (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      (burnolFiniteGramMatrix lambda rho multiplicity)⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolFiniteHilbertMatrix multiplicity)⁻¹) :=
  tendsto_matrix_nonsingInv
    (tendsto_burnolFiniteGramMatrix hcritical hinjective multiplicity)
    (burnolFiniteHilbertMatrix_det_ne_zero multiplicity)

end BurnolBlockGram

theorem tendsto_burnolGramMatrix_inv_zero_zero
    {s : ℂ} (hs : s.re = 1 / 2) (n : ℕ) :
    Tendsto (fun lambda : ℝ =>
      (burnolGramMatrix lambda s (n + 1))⁻¹
        (0 : Fin (n + 1)) (0 : Fin (n + 1)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ((((n + 1 : ℕ) : ℂ)) ^ 2)) := by
  have h := tendsto_matrix_nonsingInv_apply
    (tendsto_burnolGramMatrix hs (n + 1))
    (burnolHilbertMatrix_det_ne_zero (n + 1))
    (0 : Fin (n + 1)) (0 : Fin (n + 1))
  simpa only [burnolHilbertMatrix_inv_zero_zero] using h

end LeanLab.Riemann
