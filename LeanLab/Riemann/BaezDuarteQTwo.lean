import LeanLab.Riemann.BaezDuarteForwardLimit
import LeanLab.Riemann.WeilConvolution
import LeanLab.Riemann.BurnolY

set_option linter.style.header false

/-!
# The twice-weighted Baez-Duarte criterion

This file builds the `q = 2` variation of the Baez-Duarte criterion from multiplicative
convolution with the indicator of `(0, 1]`.  Its critical-line Mellin error has one additional
factor `1 / s` compared with the existing project criterion.
-/

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped ENNReal FourierTransform

namespace LeanLab.Riemann

/-- The complex-valued indicator used as the extra Mellin-convolution factor. -/
def baezDuarteComplexTargetFunction (x : Real) : Complex :=
  (Ioc (0 : Real) 1).indicator (fun _ => 1) x

theorem baezDuarteComplexTargetFunction_stronglyMeasurable :
    StronglyMeasurable baezDuarteComplexTargetFunction := by
  exact (measurable_const.indicator measurableSet_Ioc).stronglyMeasurable

theorem hasMellin_baezDuarteComplexTargetFunction
    (s : Complex) (hs : 0 < s.re) :
    HasMellin baezDuarteComplexTargetFunction s (1 / s) := by
  change HasMellin ((Ioc (0 : Real) 1).indicator (fun _ => (1 : Complex))) s (1 / s)
  exact hasMellin_one_Ioc (s := s) hs

/-- The `q = 2` target, namely `chi *M chi`. -/
def baezDuarteQTwoTargetFunction (x : Real) : Complex :=
  weilConvolution baezDuarteComplexTargetFunction baezDuarteComplexTargetFunction x

/-- The `q = 2` positive-natural generator, namely `chi *M rho_n`. -/
def baezDuarteQTwoKernelFunction
    (n : baezDuartePositiveNatIndex) (x : Real) : Complex :=
  weilConvolution baezDuarteComplexTargetFunction
    (fun y : Real =>
      (fractionalPartKernel (((n : Nat) : Real)⁻¹) y : Complex)) x

theorem baezDuarteQTwoTargetFunction_stronglyMeasurable :
    StronglyMeasurable baezDuarteQTwoTargetFunction := by
  change StronglyMeasurable (fun x : Real =>
    ∫ y : Real,
      baezDuarteComplexTargetFunction y *
        baezDuarteComplexTargetFunction (x / y) / (y : Complex)
      ∂(volume.restrict (Ioi 0)))
  have hjoint : StronglyMeasurable (fun p : Real × Real =>
      baezDuarteComplexTargetFunction p.2 *
        baezDuarteComplexTargetFunction (p.1 / p.2) / (p.2 : Complex)) :=
    (baezDuarteComplexTargetFunction_stronglyMeasurable.comp_measurable
      measurable_snd).mul
    (baezDuarteComplexTargetFunction_stronglyMeasurable.comp_measurable
      (measurable_fst.div measurable_snd)) |>.div
        (Complex.continuous_ofReal.measurable.comp measurable_snd).stronglyMeasurable
  exact hjoint.integral_prod_right'

theorem baezDuarteQTwoKernelFunction_stronglyMeasurable
    (n : baezDuartePositiveNatIndex) :
    StronglyMeasurable (baezDuarteQTwoKernelFunction n) := by
  change StronglyMeasurable (fun x : Real =>
    ∫ y : Real,
      baezDuarteComplexTargetFunction y *
        (fractionalPartKernel (((n : Nat) : Real)⁻¹) (x / y) : Complex) /
          (y : Complex) ∂(volume.restrict (Ioi 0)))
  have hkernel : StronglyMeasurable
      (fun p : Real × Real =>
        (fractionalPartKernel (((n : Nat) : Real)⁻¹) (p.1 / p.2) : Complex)) := by
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_fractionalPartKernel (((n : Nat) : Real)⁻¹)).comp
        (measurable_fst.div measurable_snd))).stronglyMeasurable
  have hjoint : StronglyMeasurable (fun p : Real × Real =>
      baezDuarteComplexTargetFunction p.2 *
        (fractionalPartKernel (((n : Nat) : Real)⁻¹) (p.1 / p.2) : Complex) /
          (p.2 : Complex)) :=
    (baezDuarteComplexTargetFunction_stronglyMeasurable.comp_measurable
      measurable_snd).mul hkernel |>.div
        (Complex.continuous_ofReal.measurable.comp measurable_snd).stronglyMeasurable
  exact hjoint.integral_prod_right'

/-- The target convolution has exactly one extra Mellin factor `1 / s`. -/
theorem hasMellin_baezDuarteQTwoTargetFunction
    (s : Complex) (hs : 0 < s.re) :
    HasMellin baezDuarteQTwoTargetFunction s (1 / s ^ 2) := by
  have hchi := hasMellin_baezDuarteComplexTargetFunction s hs
  constructor
  · exact mellinConvergent_weilConvolution hchi.1 hchi.1
  · change mellin
      (weilConvolution baezDuarteComplexTargetFunction
        baezDuarteComplexTargetFunction) s = _
    rw [mellin_weilConvolution hchi.1 hchi.1, hchi.2]
    ring

/-- Every natural convolution generator has transform
`n^(-s) * (-zeta(s) / s^2)`. -/
theorem hasMellin_baezDuarteQTwoKernelFunction
    (n : baezDuartePositiveNatIndex) (s : Complex)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (baezDuarteQTwoKernelFunction n) s
      (((n : Nat) : Complex) ^ (-s) * (-riemannZeta s / s ^ 2)) := by
  have hchi := hasMellin_baezDuarteComplexTargetFunction s hs0
  have hkernel := hasMellin_baezDuarteKernel n s hs0 hs1
  constructor
  · exact mellinConvergent_weilConvolution hchi.1 hkernel.1
  · change mellin
      (weilConvolution baezDuarteComplexTargetFunction
        (fun y : Real =>
          (fractionalPartKernel (((n : Nat) : Real)⁻¹) y : Complex))) s = _
    rw [mellin_weilConvolution hchi.1 hkernel.1, hchi.2, hkernel.2]
    ring

theorem baezDuarteQTwoTargetFunction_eq_neg_log
    {x : Real} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    baezDuarteQTwoTargetFunction x = -(Real.log x : Complex) := by
  change (∫ y : Real in Ioi 0,
      baezDuarteComplexTargetFunction y *
        baezDuarteComplexTargetFunction (x / y) / (y : Complex)) = _
  calc
    _ = ∫ y : Real in Icc x 1, (y : Complex)⁻¹ := by
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        by_cases hy0 : 0 < y
        · by_cases hy1 : y ≤ 1
          · by_cases hxy : x ≤ y
            · have hdiv0 : 0 < x / y := div_pos hx0 hy0
              have hdiv1 : x / y ≤ 1 := (div_le_one hy0).2 hxy
              have hmem : x * y⁻¹ ∈ Ioc (0 : Real) 1 := by
                simpa [div_eq_mul_inv] using And.intro hdiv0 hdiv1
              simp [baezDuarteComplexTargetFunction, hy0, hy1, hxy,
                hmem, div_eq_mul_inv]
            · have hdiv : 1 < x / y := (one_lt_div hy0).2 (lt_of_not_ge hxy)
              simp [baezDuarteComplexTargetFunction, hy0, hy1, hxy,
                not_le_of_gt hdiv]
          · have hy1' : 1 < y := lt_of_not_ge hy1
            have hxy : x ≤ y := hx1.trans hy1'.le
            simp [baezDuarteComplexTargetFunction, hy0, hy1, hxy]
        · have hy0' : y ≤ 0 := le_of_not_gt hy0
          have hyx : y < x := lt_of_le_of_lt hy0' hx0
          have hxy : ¬x ≤ y := not_le_of_gt hyx
          simp [baezDuarteComplexTargetFunction, hy0, hxy]
    _ = Complex.ofReal (∫ y : Real in Icc x 1, (y⁻¹ : Real)) := by
      rw [show (fun y : Real => (y : Complex)⁻¹) =
          fun y : Real => ((y⁻¹ : Real) : Complex) by funext y; simp]
      exact integral_complex_ofReal
    _ = -(Real.log x : Complex) := by
      rw [← Complex.ofReal_neg]
      congr 1
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hx1,
        integral_inv_of_pos hx0 one_pos]
      simp

theorem baezDuarteQTwoTargetFunction_eq_zero_of_one_lt
    {x : Real} (hx : 1 < x) :
    baezDuarteQTwoTargetFunction x = 0 := by
  change (∫ y : Real in Ioi 0,
      baezDuarteComplexTargetFunction y *
        baezDuarteComplexTargetFunction (x / y) / (y : Complex)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy0
  by_cases hy1 : y ≤ 1
  · have hxy : y < x := lt_of_le_of_lt hy1 hx
    have hdiv : 1 < x / y := (one_lt_div hy0).2 hxy
    simp [baezDuarteComplexTargetFunction, not_le_of_gt hdiv]
  · simp [baezDuarteComplexTargetFunction, hy1]

theorem baezDuarteQTwoTargetFunction_memLp_two_positiveHalfLine :
    MemLp baezDuarteQTwoTargetFunction (2 : ENNReal)
      (volume.restrict (Ioi (0 : Real))) := by
  rw [memLp_two_iff_integrable_sq_norm
    baezDuarteQTwoTargetFunction_stronglyMeasurable.aestronglyMeasurable]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : Real) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · have hlog := integrableOn_abs_log_pow_mul_rpow_Ioc 2
      (a := (0 : Real)) (by norm_num)
    refine hlog.congr_fun ?_ measurableSet_Ioc
    intro x hx
    change |Real.log x| ^ 2 * x ^ (0 : Real) =
      ‖baezDuarteQTwoTargetFunction x‖ ^ 2
    rw [baezDuarteQTwoTargetFunction_eq_neg_log hx.1 hx.2]
    simp [Complex.norm_real, Real.norm_eq_abs]
  · refine integrableOn_zero.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [baezDuarteQTwoTargetFunction_eq_zero_of_one_lt hx]
    simp

/-- The twice-weighted target as an element of complex `L²(0, infinity)`. -/
def baezDuarteQTwoComplexTargetL2 : positiveHalfLineComplexL2 :=
  baezDuarteQTwoTargetFunction_memLp_two_positiveHalfLine.toLp
    baezDuarteQTwoTargetFunction

theorem baezDuarteQTwoComplexTargetL2_coeFn :
    baezDuarteQTwoComplexTargetL2
      =ᵐ[volume.restrict (Ioi (0 : Real))] baezDuarteQTwoTargetFunction := by
  exact MemLp.coeFn_toLp baezDuarteQTwoTargetFunction_memLp_two_positiveHalfLine

theorem baezDuarteQTwoKernelFunction_eq_inv_mul_inv_of_one_lt
    (n : baezDuartePositiveNatIndex) {x : Real} (hx : 1 < x) :
    baezDuarteQTwoKernelFunction n x =
      ((((n : Nat) : Real)⁻¹ * x⁻¹ : Real) : Complex) := by
  let a : Real := ((n : Nat) : Real)⁻¹
  have ha := baezDuarte_reciprocal_mem_restricted n
  change (∫ y : Real in Ioi 0,
      baezDuarteComplexTargetFunction y *
        (fractionalPartKernel a (x / y) : Complex) / (y : Complex)) = _
  calc
    _ = ∫ _y : Real in Ioc 0 1, ((a * x⁻¹ : Real) : Complex) := by
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact ae_of_all volume fun y => by
        by_cases hy0 : 0 < y
        · by_cases hy1 : y ≤ 1
          · have hxy : y < x := lt_of_le_of_lt hy1 hx
            have ht : 1 < x / y := (one_lt_div hy0).2 hxy
            have ht0 : 0 < x / y := one_pos.trans ht
            have harg0 : 0 ≤ a / (x / y) := (div_pos ha.1 ht0).le
            have hat : a < x / y := lt_of_le_of_lt ha.2 ht
            have harg1 : a / (x / y) < 1 := (div_lt_one ht0).2 hat
            have hyIoi : y ∈ Ioi (0 : Real) := hy0
            have hyIoc : y ∈ Ioc (0 : Real) 1 := ⟨hy0, hy1⟩
            rw [Set.indicator_of_mem hyIoi, Set.indicator_of_mem hyIoc]
            rw [baezDuarteComplexTargetFunction, Set.indicator_of_mem hyIoc,
              one_mul, fractionalPartKernel, Int.fract_eq_self.mpr ⟨harg0, harg1⟩]
            push_cast
            field_simp [hy0.ne', hx.ne', ha.1.ne']
          · have hy1' : 1 < y := lt_of_not_ge hy1
            simp [baezDuarteComplexTargetFunction, hy0, hy1]
        · have hy0' : y ≤ 0 := le_of_not_gt hy0
          simp [baezDuarteComplexTargetFunction, hy0]
    _ = ((a * x⁻¹ : Real) : Complex) := by
      simp
    _ = ((((n : Nat) : Real)⁻¹ * x⁻¹ : Real) : Complex) := by
      rfl

/-- An integrable two-piece majorant for a `q = 2` kernel on `0 < x ≤ 1`. -/
def baezDuarteQTwoKernelSmallMajor (x y : Real) : Real :=
  (Ioc (0 : Real) x).indicator (fun _ => x⁻¹) y +
    (Ioc x 1).indicator (fun t => t⁻¹) y

theorem integrable_baezDuarteQTwoKernelSmallMajor
    {x : Real} (hx0 : 0 < x) (_hx1 : x ≤ 1) :
    Integrable (baezDuarteQTwoKernelSmallMajor x) := by
  have hfirst : Integrable
      ((Ioc (0 : Real) x).indicator (fun _ => x⁻¹)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const measure_Ioc_lt_top.ne
  have hinv : IntervalIntegrable (fun y : Real => y⁻¹) volume x 1 := by
    exact intervalIntegrable_inv_iff.2
      (Or.inr (notMem_uIcc_of_lt hx0 one_pos))
  have hsecond : Integrable
      ((Ioc x 1).indicator (fun y : Real => y⁻¹)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact hinv.1
  exact hfirst.add hsecond

theorem integral_Ioi_baezDuarteQTwoKernelSmallMajor
    {x : Real} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (∫ y : Real in Ioi 0, baezDuarteQTwoKernelSmallMajor x y) =
      1 - Real.log x := by
  have hglobal := integrable_baezDuarteQTwoKernelSmallMajor hx0 hx1
  have hfirst : Integrable
      ((Ioc (0 : Real) x).indicator (fun _ => x⁻¹)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const measure_Ioc_lt_top.ne
  have hinv : IntervalIntegrable (fun y : Real => y⁻¹) volume x 1 := by
    exact intervalIntegrable_inv_iff.2
      (Or.inr (notMem_uIcc_of_lt hx0 one_pos))
  have hsecond : Integrable
      ((Ioc x 1).indicator (fun y : Real => y⁻¹)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact hinv.1
  have hsetFirst : Ioi (0 : Real) ∩ Ioc 0 x = Ioc 0 x := by
    ext y
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    tauto
  have hsetSecond : Ioi (0 : Real) ∩ Ioc x 1 = Ioc x 1 := by
    ext y
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨hx0.trans h.1, h⟩
  change (∫ y : Real in Ioi 0,
    (Ioc (0 : Real) x).indicator (fun _ => x⁻¹) y +
      (Ioc x 1).indicator (fun t => t⁻¹) y) = _
  rw [integral_add hfirst.integrableOn hsecond.integrableOn,
    setIntegral_indicator measurableSet_Ioc,
    setIntegral_indicator measurableSet_Ioc,
    hsetFirst, hsetSecond]
  have hconst : (∫ _y : Real in Ioc 0 x, x⁻¹) = 1 := by
    rw [← intervalIntegral.integral_of_le hx0.le]
    simp [hx0.ne']
  have hintegral : (∫ y : Real in Ioc x 1, y⁻¹) = -Real.log x := by
    rw [← intervalIntegral.integral_of_le hx1,
      integral_inv_of_pos hx0 one_pos]
    simp
  rw [hconst, hintegral]
  ring

theorem norm_baezDuarteQTwoKernelIntegrand_le_smallMajor
    (n : baezDuartePositiveNatIndex) {x y : Real}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) :
    ‖baezDuarteComplexTargetFunction y *
        (fractionalPartKernel (((n : Nat) : Real)⁻¹) (x / y) : Complex) /
          (y : Complex)‖ ≤
      baezDuarteQTwoKernelSmallMajor x y := by
  let a : Real := ((n : Nat) : Real)⁻¹
  have ha := baezDuarte_reciprocal_mem_restricted n
  have hfrac0 := fractionalPartKernel_nonneg a (x / y)
  by_cases hyx : y ≤ x
  · have hy1 : y ≤ 1 := hyx.trans hx1
    have htarget : baezDuarteComplexTargetFunction y = 1 := by
      simp [baezDuarteComplexTargetFunction, hy0, hy1]
    have hz0 : 0 ≤ a / (x / y) := by positivity
    have hfloor : (0 : Int) ≤ ⌊a / (x / y)⌋ := Int.floor_nonneg.mpr hz0
    have hfract_le_arg : Int.fract (a / (x / y)) ≤ a / (x / y) := by
      rw [Int.fract]
      exact sub_le_self _ (Int.cast_nonneg hfloor)
    have hz : a / (x / y) = a * (y / x) := by
      field_simp [hx0.ne', hy0.ne']
    have hyx0 : 0 ≤ y / x := (div_pos hy0 hx0).le
    have harg_le : a / (x / y) ≤ y / x := by
      rw [hz]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha.2 hyx0
    have hfrac_le : fractionalPartKernel a (x / y) ≤ y / x := by
      rw [fractionalPartKernel]
      exact hfract_le_arg.trans harg_le
    have hyFirst : y ∈ Ioc (0 : Real) x := ⟨hy0, hyx⟩
    have hySecond : y ∉ Ioc x 1 := fun h => (not_lt_of_ge hyx) h.1
    rw [htarget, one_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hfrac0, Real.norm_of_nonneg hy0.le,
      baezDuarteQTwoKernelSmallMajor,
      Set.indicator_of_mem hyFirst, Set.indicator_of_notMem hySecond, add_zero]
    apply (div_le_iff₀ hy0).2
    simpa [div_eq_mul_inv, mul_comm] using hfrac_le
  · have hxy : x < y := lt_of_not_ge hyx
    by_cases hy1 : y ≤ 1
    · have htarget : baezDuarteComplexTargetFunction y = 1 := by
        simp [baezDuarteComplexTargetFunction, hy0, hy1]
      have hyFirst : y ∉ Ioc (0 : Real) x := fun h => hyx h.2
      have hySecond : y ∈ Ioc x 1 := ⟨hxy, hy1⟩
      rw [htarget, one_mul, norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hfrac0, Real.norm_of_nonneg hy0.le,
        baezDuarteQTwoKernelSmallMajor,
        Set.indicator_of_notMem hyFirst, Set.indicator_of_mem hySecond, zero_add]
      simpa only [one_div] using div_le_div_of_nonneg_right
        (fractionalPartKernel_lt_one a (x / y)).le hy0.le
    · have hy1' : 1 < y := lt_of_not_ge hy1
      have htarget : baezDuarteComplexTargetFunction y = 0 := by
        simp [baezDuarteComplexTargetFunction, hy0, hy1]
      rw [htarget, zero_mul, zero_div, norm_zero]
      exact add_nonneg
        (Set.indicator_nonneg (s := Ioc (0 : Real) x)
          (f := fun _ : Real => x⁻¹)
          (fun _ _ => inv_nonneg.mpr hx0.le) y)
        (Set.indicator_nonneg (s := Ioc x 1)
          (f := fun t : Real => t⁻¹)
          (fun t ht => inv_nonneg.mpr (hx0.le.trans ht.1.le)) y)

theorem norm_baezDuarteQTwoKernelFunction_le_one_sub_log
    (n : baezDuartePositiveNatIndex) {x : Real}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖baezDuarteQTwoKernelFunction n x‖ ≤ 1 - Real.log x := by
  change ‖∫ y : Real in Ioi 0,
      baezDuarteComplexTargetFunction y *
        (fractionalPartKernel (((n : Nat) : Real)⁻¹) (x / y) : Complex) /
          (y : Complex)‖ ≤ _
  rw [← integral_Ioi_baezDuarteQTwoKernelSmallMajor hx0 hx1]
  exact norm_integral_le_of_norm_le
    (integrable_baezDuarteQTwoKernelSmallMajor hx0 hx1).integrableOn
    (ae_restrict_mem measurableSet_Ioi |>.mono fun y hy =>
      norm_baezDuarteQTwoKernelIntegrand_le_smallMajor n hx0 hx1 hy)

theorem baezDuarteQTwoKernelFunction_memLp_two_positiveHalfLine
    (n : baezDuartePositiveNatIndex) :
    MemLp (baezDuarteQTwoKernelFunction n) (2 : ENNReal)
      (volume.restrict (Ioi (0 : Real))) := by
  rw [memLp_two_iff_integrable_sq_norm
    (baezDuarteQTwoKernelFunction_stronglyMeasurable n).aestronglyMeasurable]
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : Real) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · have hmajor := integrableOn_one_add_abs_log_pow_mul_rpow_Ioc 2
      (a := (0 : Real)) (by norm_num)
    apply Integrable.mono' hmajor
    · exact ((baezDuarteQTwoKernelFunction_stronglyMeasurable n).norm.pow 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hbound := norm_baezDuarteQTwoKernelFunction_le_one_sub_log n hx.1 hx.2
      have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2
      have hnorm0 := norm_nonneg (baezDuarteQTwoKernelFunction n x)
      have hmajor0 : 0 ≤ 1 - Real.log x := by linarith
      have hsquare : ‖baezDuarteQTwoKernelFunction n x‖ ^ 2 ≤
          (1 - Real.log x) ^ 2 := by nlinarith
      simpa [sub_eq_add_neg, abs_of_nonpos hlog] using hsquare
  · let a : Real := ((n : Nat) : Real)⁻¹
    have hbase : IntegrableOn (fun x : Real => x ^ (-2 : Real)) (Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    have hmajor : IntegrableOn (fun x : Real => a ^ 2 * x ^ (-2 : Real))
        (Ioi 1) volume := hbase.const_mul (a ^ 2)
    refine hmajor.congr_fun ?_ measurableSet_Ioi
    intro x hx
    have hx1 : 1 < x := hx
    change a ^ 2 * x ^ (-2 : Real) =
      ‖baezDuarteQTwoKernelFunction n x‖ ^ 2
    rw [baezDuarteQTwoKernelFunction_eq_inv_mul_inv_of_one_lt n hx1]
    change a ^ 2 * x ^ (-2 : Real) = ‖((a * x⁻¹ : Real) : Complex)‖ ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (inv_nonneg.mpr (le_trans zero_le_one hx1.le)))]
    have hrpow : x ^ (-2 : Real) = (x ^ (2 : Nat))⁻¹ := by
      rw [show (-2 : Real) = -(2 : Real) by norm_num,
        Real.rpow_neg (zero_le_one.trans hx1.le)]
      exact congrArg Inv.inv (Real.rpow_natCast x 2)
    rw [hrpow]
    dsimp [a]
    field_simp [hx1.ne']

/-- A twice-weighted natural generator in complex `L²(0, infinity)`. -/
def baezDuarteQTwoComplexKernelL2
    (n : baezDuartePositiveNatIndex) : positiveHalfLineComplexL2 :=
  (baezDuarteQTwoKernelFunction_memLp_two_positiveHalfLine n).toLp
    (baezDuarteQTwoKernelFunction n)

theorem baezDuarteQTwoComplexKernelL2_coeFn
    (n : baezDuartePositiveNatIndex) :
    baezDuarteQTwoComplexKernelL2 n
      =ᵐ[volume.restrict (Ioi (0 : Real))] baezDuarteQTwoKernelFunction n := by
  exact MemLp.coeFn_toLp
    (baezDuarteQTwoKernelFunction_memLp_two_positiveHalfLine n)

theorem baezDuarteComplexKernelL2_coeFn
    (n : baezDuartePositiveNatIndex) :
    baezDuarteComplexKernelL2 n
      =ᵐ[volume.restrict (Ioi (0 : Real))]
        fun x : Real =>
          (fractionalPartKernel (((n : Nat) : Real)⁻¹) x : Complex) := by
  filter_upwards [baezDuarteOfRealLp_coeFn (baezDuarteKernelL2 n),
    baezDuarteKernelL2_coeFn n] with x hof hk
  rw [baezDuarteComplexKernelL2, hof, hk]

theorem norm_baezDuarteScaledTargetTransform_le_two (ξ : Real) :
    ‖baezDuarteScaledTargetTransform ξ‖ ≤ 2 := by
  let s : Complex :=
    (1 / 2 : Complex) + ((2 * Real.pi * ξ : Real) : Complex) * Complex.I
  have hsre : s.re = 1 / 2 := by
    dsimp only [s]
    norm_num
  have hsne : s ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    rw [hsre] at this
    norm_num at this
  have hnorm : 1 / 2 ≤ ‖s‖ := by
    have habs := Complex.abs_re_le_norm s
    rw [hsre, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)] at habs
    exact habs
  change ‖1 / s‖ ≤ 2
  rw [norm_div, norm_one]
  exact (div_le_iff₀ (norm_pos_iff.mpr hsne)).2 (by nlinarith)

/-- Pointwise multiplication by the extra critical-line factor `1 / s`. -/
def baezDuarteQTwoFrequencyMultiplierFun
    (f : realLineComplexL2) (ξ : Real) : Complex :=
  baezDuarteScaledTargetTransform ξ * f ξ

theorem baezDuarteQTwoFrequencyMultiplierFun_aestronglyMeasurable
    (f : realLineComplexL2) :
    AEStronglyMeasurable (baezDuarteQTwoFrequencyMultiplierFun f) volume := by
  have hm : StronglyMeasurable baezDuarteScaledTargetTransform := by
    apply Continuous.stronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    intro ξ
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [baezDuarteScaledTargetTransform, Complex.div_re, Complex.normSq] at hre
  exact hm.aestronglyMeasurable.mul (Lp.memLp f).1

theorem baezDuarteQTwoFrequencyMultiplierFun_memLp
    (f : realLineComplexL2) :
    MemLp (baezDuarteQTwoFrequencyMultiplierFun f) (2 : ENNReal) volume := by
  refine (Lp.memLp f).of_le_mul (c := 2)
    (baezDuarteQTwoFrequencyMultiplierFun_aestronglyMeasurable f) ?_
  exact ae_of_all volume fun ξ => by
    rw [baezDuarteQTwoFrequencyMultiplierFun, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_baezDuarteScaledTargetTransform_le_two ξ) (norm_nonneg _)

def baezDuarteQTwoFrequencyMultiplier
    (f : realLineComplexL2) : realLineComplexL2 :=
  (baezDuarteQTwoFrequencyMultiplierFun_memLp f).toLp
    (baezDuarteQTwoFrequencyMultiplierFun f)

theorem baezDuarteQTwoFrequencyMultiplier_coeFn
    (f : realLineComplexL2) :
    baezDuarteQTwoFrequencyMultiplier f
      =ᵐ[volume] baezDuarteQTwoFrequencyMultiplierFun f := by
  exact MemLp.coeFn_toLp (baezDuarteQTwoFrequencyMultiplierFun_memLp f)

theorem baezDuarteQTwoFrequencyMultiplier_add
    (f g : realLineComplexL2) :
    baezDuarteQTwoFrequencyMultiplier (f + g) =
      baezDuarteQTwoFrequencyMultiplier f +
        baezDuarteQTwoFrequencyMultiplier g := by
  apply Lp.ext
  filter_upwards [baezDuarteQTwoFrequencyMultiplier_coeFn (f + g),
    baezDuarteQTwoFrequencyMultiplier_coeFn f,
    baezDuarteQTwoFrequencyMultiplier_coeFn g,
    Lp.coeFn_add f g,
    Lp.coeFn_add (baezDuarteQTwoFrequencyMultiplier f)
      (baezDuarteQTwoFrequencyMultiplier g)] with ξ hsum hf hg hfg hout
  rw [hsum, hout]
  change baezDuarteQTwoFrequencyMultiplierFun (f + g) ξ =
    baezDuarteQTwoFrequencyMultiplier f ξ +
      baezDuarteQTwoFrequencyMultiplier g ξ
  rw [hf, hg]
  change baezDuarteScaledTargetTransform ξ * (f + g) ξ =
    baezDuarteScaledTargetTransform ξ * f ξ +
      baezDuarteScaledTargetTransform ξ * g ξ
  rw [hfg]
  simp [Pi.add_apply, mul_add]

theorem baezDuarteQTwoFrequencyMultiplier_smul
    (c : Complex) (f : realLineComplexL2) :
    baezDuarteQTwoFrequencyMultiplier (c • f) =
      c • baezDuarteQTwoFrequencyMultiplier f := by
  apply Lp.ext
  filter_upwards [baezDuarteQTwoFrequencyMultiplier_coeFn (c • f),
    baezDuarteQTwoFrequencyMultiplier_coeFn f,
    Lp.coeFn_smul c f,
    Lp.coeFn_smul c (baezDuarteQTwoFrequencyMultiplier f)] with ξ hcf hf hfin hout
  rw [hcf, hout]
  change baezDuarteQTwoFrequencyMultiplierFun (c • f) ξ =
    c * baezDuarteQTwoFrequencyMultiplier f ξ
  rw [hf]
  change baezDuarteScaledTargetTransform ξ * (c • f) ξ =
    c * (baezDuarteScaledTargetTransform ξ * f ξ)
  rw [hfin]
  simp [Pi.smul_apply, smul_eq_mul]
  ring

def baezDuarteQTwoFrequencyMultiplierLinearMap :
    realLineComplexL2 →ₗ[Complex] realLineComplexL2 where
  toFun := baezDuarteQTwoFrequencyMultiplier
  map_add' := baezDuarteQTwoFrequencyMultiplier_add
  map_smul' := baezDuarteQTwoFrequencyMultiplier_smul

theorem norm_baezDuarteQTwoFrequencyMultiplier_le
    (f : realLineComplexL2) :
    ‖baezDuarteQTwoFrequencyMultiplier f‖ ≤ 2 * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [baezDuarteQTwoFrequencyMultiplier_coeFn f] with ξ hξ
  rw [hξ, baezDuarteQTwoFrequencyMultiplierFun, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_baezDuarteScaledTargetTransform_le_two ξ) (norm_nonneg _)

/-- The bounded critical-line multiplier by `1 / s`, with operator norm at most `2`. -/
def baezDuarteQTwoFrequencyMultiplierCLM :
    realLineComplexL2 →L[Complex] realLineComplexL2 :=
  LinearMap.mkContinuous baezDuarteQTwoFrequencyMultiplierLinearMap 2
    norm_baezDuarteQTwoFrequencyMultiplier_le

/-- Concrete logarithmic representative of the twice-weighted target. -/
def baezDuarteQTwoTargetWeightedLog (u : Real) : Complex :=
  (Real.exp (-u / 2) : Complex) *
    baezDuarteQTwoTargetFunction (Real.exp (-u))

theorem baezDuarteQTwoTargetWeightedLog_ae_weightedLogForwardFun :
    baezDuarteQTwoTargetWeightedLog =ᵐ[volume]
      weightedLogForwardFun baezDuarteQTwoComplexTargetL2 := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    baezDuarteQTwoComplexTargetL2_coeFn
  filter_upwards [hsource] with u hu
  change baezDuarteQTwoComplexTargetL2 (Real.exp (-u)) =
    baezDuarteQTwoTargetFunction (Real.exp (-u)) at hu
  simp only [baezDuarteQTwoTargetWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem baezDuarteQTwoTargetWeightedLog_memLp :
    MemLp baezDuarteQTwoTargetWeightedLog (2 : ENNReal) volume :=
  (weightedLogForwardFun_memLp baezDuarteQTwoComplexTargetL2).ae_eq
    baezDuarteQTwoTargetWeightedLog_ae_weightedLogForwardFun.symm

theorem baezDuarteQTwoTargetWeightedLog_toLp :
    baezDuarteQTwoTargetWeightedLog_memLp.toLp
        baezDuarteQTwoTargetWeightedLog =
      weightedLogPullback baezDuarteQTwoComplexTargetL2 := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr baezDuarteQTwoTargetWeightedLog_memLp
    (weightedLogForwardFun_memLp baezDuarteQTwoComplexTargetL2)
    baezDuarteQTwoTargetWeightedLog_ae_weightedLogForwardFun

theorem baezDuarteQTwoTargetWeightedLog_integrable :
    Integrable baezDuarteQTwoTargetWeightedLog := by
  have hconv :=
    (hasMellin_baezDuarteQTwoTargetFunction (1 / 2 : Complex) (by norm_num)).1
  exact integrable_weightedLog_of_mellinConvergent hconv

/-- The concrete `q = 2` target transform, equal to `1 / s^2`. -/
def baezDuarteQTwoScaledTargetTransform (ξ : Real) : Complex :=
  baezDuarteScaledTargetTransform ξ ^ 2

theorem baezDuarteQTwoScaledTargetTransform_memLp :
    MemLp baezDuarteQTwoScaledTargetTransform (2 : ENNReal) volume := by
  have hmeas : AEStronglyMeasurable baezDuarteQTwoScaledTargetTransform volume := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.pow
    apply continuous_iff_continuousAt.mpr
    intro ξ
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [baezDuarteScaledTargetTransform, Complex.div_re, Complex.normSq] at hre
  refine baezDuarteScaledTargetTransform_memLp.of_le_mul (c := 2) hmeas ?_
  exact ae_of_all volume fun ξ => by
    rw [baezDuarteQTwoScaledTargetTransform, pow_two, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_baezDuarteScaledTargetTransform_le_two ξ) (norm_nonneg _)

theorem fourier_baezDuarteQTwoTargetWeightedLog (ξ : Real) :
    𝓕 baezDuarteQTwoTargetWeightedLog ξ =
      baezDuarteQTwoScaledTargetTransform ξ := by
  let τ : Real := 2 * Real.pi * ξ
  let s : Complex := (1 / 2 : Complex) + τ * Complex.I
  have hs : 0 < s.re := by dsimp only [s]; norm_num
  have hM := hasMellin_baezDuarteQTwoTargetFunction s hs
  have hFourier := mellin_criticalLine_eq_fourier baezDuarteQTwoTargetFunction τ
  rw [hM.2] at hFourier
  have hτ : τ / (2 * Real.pi) = ξ := by
    dsimp only [τ]
    field_simp [Real.pi_ne_zero]
  rw [hτ] at hFourier
  change 𝓕 (fun u : Real => (Real.exp (-u / 2) : Complex) *
    baezDuarteQTwoTargetFunction (Real.exp (-u))) ξ = _
  rw [← hFourier]
  dsimp only [baezDuarteQTwoScaledTargetTransform,
    baezDuarteScaledTargetTransform, s, τ]
  rw [div_pow]
  norm_num

theorem baezDuarteFourierMellinL2_qTwoTarget_eq :
    baezDuarteFourierMellinL2 baezDuarteQTwoComplexTargetL2 =
      baezDuarteQTwoScaledTargetTransform_memLp.toLp
        baezDuarteQTwoScaledTargetTransform := by
  have hF2 : MemLp (𝓕 baezDuarteQTwoTargetWeightedLog) (2 : ENNReal) volume :=
    baezDuarteQTwoScaledTargetTransform_memLp.ae_eq
      (ae_of_all volume fun ξ => (fourier_baezDuarteQTwoTargetWeightedLog ξ).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    baezDuarteQTwoTargetWeightedLog_integrable
    baezDuarteQTwoTargetWeightedLog_memLp hF2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← baezDuarteQTwoTargetWeightedLog_toLp]
  calc
    _ = hF2.toLp (𝓕 baezDuarteQTwoTargetWeightedLog) := hcompat
    _ = _ := MemLp.toLp_congr hF2 baezDuarteQTwoScaledTargetTransform_memLp
      (ae_of_all volume fun ξ => fourier_baezDuarteQTwoTargetWeightedLog ξ)

theorem baezDuarteQTwoFrequencyMultiplier_target_eq :
    baezDuarteQTwoFrequencyMultiplier
        (baezDuarteFourierMellinL2 baezDuarteComplexTargetL2) =
      baezDuarteFourierMellinL2 baezDuarteQTwoComplexTargetL2 := by
  rw [baezDuarteFourierMellinL2_target_eq,
    baezDuarteFourierMellinL2_qTwoTarget_eq]
  apply Lp.ext
  filter_upwards [baezDuarteQTwoFrequencyMultiplier_coeFn
      (baezDuarteScaledTargetTransform_memLp.toLp
        baezDuarteScaledTargetTransform),
    baezDuarteScaledTargetTransform_memLp.coeFn_toLp,
    baezDuarteQTwoScaledTargetTransform_memLp.coeFn_toLp] with ξ hmul hm hq
  rw [hmul, hq, baezDuarteQTwoFrequencyMultiplierFun, hm]
  simp [baezDuarteQTwoScaledTargetTransform, pow_two]

/-- Concrete logarithmic representative of a `q = 1` natural generator. -/
def baezDuarteKernelWeightedLog
    (n : baezDuartePositiveNatIndex) (u : Real) : Complex :=
  (Real.exp (-u / 2) : Complex) *
    (fractionalPartKernel (((n : Nat) : Real)⁻¹) (Real.exp (-u)) : Complex)

/-- Concrete logarithmic representative of a `q = 2` natural generator. -/
def baezDuarteQTwoKernelWeightedLog
    (n : baezDuartePositiveNatIndex) (u : Real) : Complex :=
  (Real.exp (-u / 2) : Complex) *
    baezDuarteQTwoKernelFunction n (Real.exp (-u))

theorem baezDuarteKernelWeightedLog_ae_weightedLogForwardFun
    (n : baezDuartePositiveNatIndex) :
    baezDuarteKernelWeightedLog n =ᵐ[volume]
      weightedLogForwardFun (baezDuarteComplexKernelL2 n) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (baezDuarteComplexKernelL2_coeFn n)
  filter_upwards [hsource] with u hu
  change baezDuarteComplexKernelL2 n (Real.exp (-u)) =
    (fractionalPartKernel (((n : Nat) : Real)⁻¹)
      (Real.exp (-u)) : Complex) at hu
  simp only [baezDuarteKernelWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem baezDuarteQTwoKernelWeightedLog_ae_weightedLogForwardFun
    (n : baezDuartePositiveNatIndex) :
    baezDuarteQTwoKernelWeightedLog n =ᵐ[volume]
      weightedLogForwardFun (baezDuarteQTwoComplexKernelL2 n) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (baezDuarteQTwoComplexKernelL2_coeFn n)
  filter_upwards [hsource] with u hu
  change baezDuarteQTwoComplexKernelL2 n (Real.exp (-u)) =
    baezDuarteQTwoKernelFunction n (Real.exp (-u)) at hu
  simp only [baezDuarteQTwoKernelWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem baezDuarteKernelWeightedLog_memLp
    (n : baezDuartePositiveNatIndex) :
    MemLp (baezDuarteKernelWeightedLog n) (2 : ENNReal) volume :=
  (weightedLogForwardFun_memLp (baezDuarteComplexKernelL2 n)).ae_eq
    (baezDuarteKernelWeightedLog_ae_weightedLogForwardFun n).symm

theorem baezDuarteQTwoKernelWeightedLog_memLp
    (n : baezDuartePositiveNatIndex) :
    MemLp (baezDuarteQTwoKernelWeightedLog n) (2 : ENNReal) volume :=
  (weightedLogForwardFun_memLp (baezDuarteQTwoComplexKernelL2 n)).ae_eq
    (baezDuarteQTwoKernelWeightedLog_ae_weightedLogForwardFun n).symm

theorem baezDuarteKernelWeightedLog_toLp
    (n : baezDuartePositiveNatIndex) :
    (baezDuarteKernelWeightedLog_memLp n).toLp
        (baezDuarteKernelWeightedLog n) =
      weightedLogPullback (baezDuarteComplexKernelL2 n) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (baezDuarteKernelWeightedLog_memLp n)
    (weightedLogForwardFun_memLp (baezDuarteComplexKernelL2 n))
    (baezDuarteKernelWeightedLog_ae_weightedLogForwardFun n)

theorem baezDuarteQTwoKernelWeightedLog_toLp
    (n : baezDuartePositiveNatIndex) :
    (baezDuarteQTwoKernelWeightedLog_memLp n).toLp
        (baezDuarteQTwoKernelWeightedLog n) =
      weightedLogPullback (baezDuarteQTwoComplexKernelL2 n) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (baezDuarteQTwoKernelWeightedLog_memLp n)
    (weightedLogForwardFun_memLp (baezDuarteQTwoComplexKernelL2 n))
    (baezDuarteQTwoKernelWeightedLog_ae_weightedLogForwardFun n)

theorem baezDuarteKernelWeightedLog_integrable
    (n : baezDuartePositiveNatIndex) :
    Integrable (baezDuarteKernelWeightedLog n) := by
  have hconv := (hasMellin_baezDuarteKernel n (1 / 2 : Complex)
    (by norm_num) (by norm_num)).1
  exact integrable_weightedLog_of_mellinConvergent hconv

theorem baezDuarteQTwoKernelWeightedLog_integrable
    (n : baezDuartePositiveNatIndex) :
    Integrable (baezDuarteQTwoKernelWeightedLog n) := by
  have hconv := (hasMellin_baezDuarteQTwoKernelFunction n (1 / 2 : Complex)
    (by norm_num) (by norm_num)).1
  exact integrable_weightedLog_of_mellinConvergent hconv

/-- The scaled critical-line Mellin transform of a `q = 1` generator. -/
def baezDuarteScaledKernelTransform
    (n : baezDuartePositiveNatIndex) (xi : Real) : Complex :=
  let s : Complex :=
    (1 / 2 : Complex) + ((2 * Real.pi * xi : Real) : Complex) * Complex.I
  ((n : Nat) : Complex) ^ (-s) * (-riemannZeta s / s)

/-- The scaled critical-line Mellin transform of a `q = 2` generator. -/
def baezDuarteQTwoScaledKernelTransform
    (n : baezDuartePositiveNatIndex) (xi : Real) : Complex :=
  baezDuarteScaledTargetTransform xi * baezDuarteScaledKernelTransform n xi

theorem fourier_baezDuarteKernelWeightedLog
    (n : baezDuartePositiveNatIndex) (xi : Real) :
    𝓕 (baezDuarteKernelWeightedLog n) xi =
      baezDuarteScaledKernelTransform n xi := by
  let tau : Real := 2 * Real.pi * xi
  let s : Complex := (1 / 2 : Complex) + tau * Complex.I
  have hs0 : 0 < s.re := by dsimp only [s]; norm_num
  have hs1 : s.re < 1 := by dsimp only [s]; norm_num
  have hM := hasMellin_baezDuarteKernel n s hs0 hs1
  have hFourier := mellin_criticalLine_eq_fourier
    (fun x : Real =>
      (fractionalPartKernel (((n : Nat) : Real)⁻¹) x : Complex)) tau
  rw [hM.2] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : Real => (Real.exp (-u / 2) : Complex) *
    (fractionalPartKernel (((n : Nat) : Real)⁻¹)
      (Real.exp (-u)) : Complex)) xi = _
  rw [← hFourier]
  rfl

theorem fourier_baezDuarteQTwoKernelWeightedLog
    (n : baezDuartePositiveNatIndex) (xi : Real) :
    𝓕 (baezDuarteQTwoKernelWeightedLog n) xi =
      baezDuarteQTwoScaledKernelTransform n xi := by
  let tau : Real := 2 * Real.pi * xi
  let s : Complex := (1 / 2 : Complex) + tau * Complex.I
  have hs0 : 0 < s.re := by dsimp only [s]; norm_num
  have hs1 : s.re < 1 := by dsimp only [s]; norm_num
  have hsne : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s] at hre
  have hM := hasMellin_baezDuarteQTwoKernelFunction n s hs0 hs1
  have hFourier := mellin_criticalLine_eq_fourier
    (baezDuarteQTwoKernelFunction n) tau
  rw [hM.2] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : Real => (Real.exp (-u / 2) : Complex) *
    baezDuarteQTwoKernelFunction n (Real.exp (-u))) xi = _
  rw [← hFourier]
  dsimp only [baezDuarteQTwoScaledKernelTransform,
    baezDuarteScaledTargetTransform, baezDuarteScaledKernelTransform, s, tau]
  field_simp [hsne]

theorem continuous_baezDuarteScaledKernelTransform
    (n : baezDuartePositiveNatIndex) :
    Continuous (baezDuarteScaledKernelTransform n) := by
  rw [← funext (fourier_baezDuarteKernelWeightedLog n)]
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ Real)
    (baezDuarteKernelWeightedLog n))
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (baezDuarteKernelWeightedLog_integrable n)

theorem continuous_baezDuarteQTwoScaledKernelTransform
    (n : baezDuartePositiveNatIndex) :
    Continuous (baezDuarteQTwoScaledKernelTransform n) := by
  rw [← funext (fourier_baezDuarteQTwoKernelWeightedLog n)]
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ Real)
    (baezDuarteQTwoKernelWeightedLog n))
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (baezDuarteQTwoKernelWeightedLog_integrable n)

theorem baezDuarteScaledKernelTransform_memLp
    (n : baezDuartePositiveNatIndex) :
    MemLp (baezDuarteScaledKernelTransform n) (2 : ENNReal) volume := by
  obtain ⟨C, hC, hquot⟩ := exists_norm_riemannZeta_div_criticalLine_le_rpow
  have hmajor :=
    (baezDuarteScaledVerticalMajorant_memLp (γ := 3 / 8) (by norm_num)).const_smul
      (C : Complex)
  refine hmajor.of_le (continuous_baezDuarteScaledKernelTransform n).aestronglyMeasurable
    (ae_of_all volume fun xi => ?_)
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hC]
  let s : Complex :=
    (1 / 2 : Complex) + ((2 * Real.pi * xi : Real) : Complex) * Complex.I
  have hnpow : ‖((n : Nat) : Complex) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos n.property]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt n.property))
    · dsimp only [s]
      norm_num
  have hquot' :
      ‖-riemannZeta s / s‖ ≤
        C * (1 + |2 * Real.pi * xi|) ^ (-5 / 8 : Real) := by
    simpa only [s, neg_div, norm_neg] using hquot (2 * Real.pi * xi)
  have hmajor_norm :
      ‖baezDuarteScaledVerticalMajorant (3 / 8) xi‖ =
        (1 + |2 * Real.pi * xi|) ^ (-5 / 8 : Real) := by
    simpa [baezDuarteScaledVerticalMajorant] using
      (norm_baezDuarteVerticalMajorant_three_eighths_add
        0 (2 * Real.pi * xi))
  rw [hmajor_norm]
  change ‖((n : Nat) : Complex) ^ (-s) * (-riemannZeta s / s)‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul hnpow hquot' (norm_nonneg _) zero_le_one).trans_eq
    (one_mul _)

theorem baezDuarteQTwoScaledKernelTransform_memLp
    (n : baezDuartePositiveNatIndex) :
    MemLp (baezDuarteQTwoScaledKernelTransform n) (2 : ENNReal) volume := by
  refine (baezDuarteScaledKernelTransform_memLp n).of_le_mul (c := 2)
    (continuous_baezDuarteQTwoScaledKernelTransform n).aestronglyMeasurable ?_
  exact ae_of_all volume fun xi => by
    rw [baezDuarteQTwoScaledKernelTransform, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_baezDuarteScaledTargetTransform_le_two xi) (norm_nonneg _)

theorem baezDuarteFourierMellinL2_kernel_eq
    (n : baezDuartePositiveNatIndex) :
    baezDuarteFourierMellinL2 (baezDuarteComplexKernelL2 n) =
      (baezDuarteScaledKernelTransform_memLp n).toLp
        (baezDuarteScaledKernelTransform n) := by
  have hF2 : MemLp (𝓕 (baezDuarteKernelWeightedLog n))
      (2 : ENNReal) volume :=
    (baezDuarteScaledKernelTransform_memLp n).ae_eq
      (ae_of_all volume fun xi => (fourier_baezDuarteKernelWeightedLog n xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    (baezDuarteKernelWeightedLog_integrable n)
    (baezDuarteKernelWeightedLog_memLp n) hF2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← baezDuarteKernelWeightedLog_toLp n]
  calc
    _ = hF2.toLp (𝓕 (baezDuarteKernelWeightedLog n)) := hcompat
    _ = _ := MemLp.toLp_congr hF2
      (baezDuarteScaledKernelTransform_memLp n)
      (ae_of_all volume fun xi => fourier_baezDuarteKernelWeightedLog n xi)

theorem baezDuarteFourierMellinL2_qTwoKernel_eq
    (n : baezDuartePositiveNatIndex) :
    baezDuarteFourierMellinL2 (baezDuarteQTwoComplexKernelL2 n) =
      (baezDuarteQTwoScaledKernelTransform_memLp n).toLp
        (baezDuarteQTwoScaledKernelTransform n) := by
  have hF2 : MemLp (𝓕 (baezDuarteQTwoKernelWeightedLog n))
      (2 : ENNReal) volume :=
    (baezDuarteQTwoScaledKernelTransform_memLp n).ae_eq
      (ae_of_all volume fun xi =>
        (fourier_baezDuarteQTwoKernelWeightedLog n xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    (baezDuarteQTwoKernelWeightedLog_integrable n)
    (baezDuarteQTwoKernelWeightedLog_memLp n) hF2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← baezDuarteQTwoKernelWeightedLog_toLp n]
  calc
    _ = hF2.toLp (𝓕 (baezDuarteQTwoKernelWeightedLog n)) := hcompat
    _ = _ := MemLp.toLp_congr hF2
      (baezDuarteQTwoScaledKernelTransform_memLp n)
      (ae_of_all volume fun xi =>
        fourier_baezDuarteQTwoKernelWeightedLog n xi)

theorem baezDuarteQTwoFrequencyMultiplier_kernel_eq
    (n : baezDuartePositiveNatIndex) :
    baezDuarteQTwoFrequencyMultiplier
        (baezDuarteFourierMellinL2 (baezDuarteComplexKernelL2 n)) =
      baezDuarteFourierMellinL2 (baezDuarteQTwoComplexKernelL2 n) := by
  rw [baezDuarteFourierMellinL2_kernel_eq,
    baezDuarteFourierMellinL2_qTwoKernel_eq]
  apply Lp.ext
  filter_upwards [baezDuarteQTwoFrequencyMultiplier_coeFn
      ((baezDuarteScaledKernelTransform_memLp n).toLp
        (baezDuarteScaledKernelTransform n)),
    (baezDuarteScaledKernelTransform_memLp n).coeFn_toLp,
    (baezDuarteQTwoScaledKernelTransform_memLp n).coeFn_toLp] with xi hmul hk hq
  rw [hmul, hq, baezDuarteQTwoFrequencyMultiplierFun, hk]
  rfl

/-- The physical bounded convolution operator obtained by Fourier-Mellin transport. -/
def baezDuarteQTwoPhysicalCLM :
    positiveHalfLineComplexL2 →L[Complex] positiveHalfLineComplexL2 :=
  baezDuarteFourierMellinL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (baezDuarteQTwoFrequencyMultiplierCLM.comp
      baezDuarteFourierMellinL2.toContinuousLinearEquiv.toContinuousLinearMap)

theorem baezDuarteQTwoPhysicalCLM_target_eq :
    baezDuarteQTwoPhysicalCLM baezDuarteComplexTargetL2 =
      baezDuarteQTwoComplexTargetL2 := by
  rw [baezDuarteQTwoPhysicalCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change baezDuarteFourierMellinL2.symm
      (baezDuarteQTwoFrequencyMultiplier
        (baezDuarteFourierMellinL2 baezDuarteComplexTargetL2)) = _
  rw [baezDuarteQTwoFrequencyMultiplier_target_eq]
  exact baezDuarteFourierMellinL2.symm_apply_apply _

theorem baezDuarteQTwoPhysicalCLM_kernel_eq
    (n : baezDuartePositiveNatIndex) :
    baezDuarteQTwoPhysicalCLM (baezDuarteComplexKernelL2 n) =
      baezDuarteQTwoComplexKernelL2 n := by
  rw [baezDuarteQTwoPhysicalCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change baezDuarteFourierMellinL2.symm
      (baezDuarteQTwoFrequencyMultiplier
        (baezDuarteFourierMellinL2 (baezDuarteComplexKernelL2 n))) = _
  rw [baezDuarteQTwoFrequencyMultiplier_kernel_eq]
  exact baezDuarteFourierMellinL2.symm_apply_apply _

/-- The complex finite span of the twice-weighted natural generators. -/
def baezDuarteQTwoComplexKernelSpan :
    Submodule Complex positiveHalfLineComplexL2 :=
  Submodule.span Complex (Set.range baezDuarteQTwoComplexKernelL2)

/-- The closed complex span in the `q = 2` criterion. -/
def baezDuarteQTwoComplexKernelClosure :
    Submodule Complex positiveHalfLineComplexL2 :=
  baezDuarteQTwoComplexKernelSpan.topologicalClosure

theorem baezDuarteQTwoComplexKernelClosure_coe :
    (baezDuarteQTwoComplexKernelClosure : Set positiveHalfLineComplexL2) =
      closure
        (baezDuarteQTwoComplexKernelSpan : Set positiveHalfLineComplexL2) := by
  exact Submodule.topologicalClosure_coe baezDuarteQTwoComplexKernelSpan

theorem mem_baezDuarteQTwoComplexKernelSpan_iff_exists_finsupp_sum
    (g : positiveHalfLineComplexL2) :
    g ∈ baezDuarteQTwoComplexKernelSpan ↔
      ∃ c : baezDuartePositiveNatIndex →₀ Complex,
        c.sum (fun n z => z • baezDuarteQTwoComplexKernelL2 n) = g := by
  rw [baezDuarteQTwoComplexKernelSpan]
  exact Finsupp.mem_span_range_iff_exists_finsupp

theorem baezDuarteQTwoPhysicalCLM_maps_kernelSpan
    {f : positiveHalfLineComplexL2}
    (hf : f ∈ baezDuarteComplexKernelSpan) :
    baezDuarteQTwoPhysicalCLM f ∈ baezDuarteQTwoComplexKernelSpan := by
  refine Submodule.span_induction
    (p := fun f _ =>
      baezDuarteQTwoPhysicalCLM f ∈ baezDuarteQTwoComplexKernelSpan)
    ?gen ?zero ?add ?smul hf
  · rintro _ ⟨n, rfl⟩
    rw [baezDuarteQTwoPhysicalCLM_kernel_eq]
    exact Submodule.subset_span (Set.mem_range_self n)
  · simp
  · intro f g _hf _hg hfm hgm
    rw [map_add]
    exact Submodule.add_mem _ hfm hgm
  · intro c f _hf hfm
    rw [map_smul]
    exact Submodule.smul_mem _ c hfm

/-- Forward half of the exact `q = 2` Baez-Duarte closure criterion. -/
theorem RiemannHypothesis.baezDuarteQTwoComplexTargetL2_mem_kernelClosure
    (hRH : RiemannHypothesis) :
    baezDuarteQTwoComplexTargetL2 ∈
      baezDuarteQTwoComplexKernelClosure := by
  have hsource : baezDuarteComplexTargetL2 ∈
      closure (baezDuarteComplexKernelSpan : Set positiveHalfLineComplexL2) := by
    rw [← baezDuarteComplexKernelClosure_coe]
    exact RiemannHypothesis.baezDuarteComplexTargetL2_mem_kernelClosure hRH
  have himage : baezDuarteQTwoPhysicalCLM baezDuarteComplexTargetL2 ∈
      closure
        (baezDuarteQTwoComplexKernelSpan : Set positiveHalfLineComplexL2) :=
    map_mem_closure baezDuarteQTwoPhysicalCLM.continuous hsource
      (fun _ hf => baezDuarteQTwoPhysicalCLM_maps_kernelSpan hf)
  change baezDuarteQTwoComplexTargetL2 ∈
    (baezDuarteQTwoComplexKernelClosure : Set positiveHalfLineComplexL2)
  rw [baezDuarteQTwoComplexKernelClosure_coe,
    ← baezDuarteQTwoPhysicalCLM_target_eq]
  exact himage

/-- A finite complex linear combination of the twice-weighted natural generators. -/
def baezDuarteQTwoFiniteKernelSum
    (c : baezDuartePositiveNatIndex →₀ Complex) (x : Real) : Complex :=
  c.sum fun n z => z * baezDuarteQTwoKernelFunction n x

/-- The reciprocal tail moment of a finite `q = 2` generator sum. -/
def baezDuarteQTwoReciprocalMoment
    (c : baezDuartePositiveNatIndex →₀ Complex) : Complex :=
  c.sum fun n z => z * ((((n : Nat) : Real)⁻¹ : Real) : Complex)

theorem hasMellin_baezDuarteQTwoFiniteKernelSum_zero
    (c : baezDuartePositiveNatIndex →₀ Complex) (s : Complex)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) :
    HasMellin (baezDuarteQTwoFiniteKernelSum c) s 0 := by
  classical
  have hterm : ∀ n : baezDuartePositiveNatIndex,
      HasMellin
        (fun x : Real => c n * baezDuarteQTwoKernelFunction n x) s 0 := by
    intro n
    have hk := hasMellin_baezDuarteQTwoKernelFunction n s hs0 hs1
    have hsmul := hasMellin_const_smul hk.1 (c n)
    rw [hk.2, hz] at hsmul
    simpa [smul_eq_mul] using hsmul
  have hsum : HasMellin
      (fun x : Real => ∑ n ∈ c.support,
        c n * baezDuarteQTwoKernelFunction n x) s 0 := by
    induction c.support using Finset.induction_on with
    | empty =>
        simp [HasMellin, MellinConvergent, mellin]
    | @insert n u hn ih =>
        have hnM := hterm n
        have hadd := hasMellin_add hnM.1 ih.1
        simpa [hn, hnM.2, ih.2] using hadd
  convert hsum using 1
  funext x
  simp [baezDuarteQTwoFiniteKernelSum, Finsupp.sum]

theorem baezDuarteQTwoFiniteKernelSum_eq_moment_mul_inv_of_one_lt
    (c : baezDuartePositiveNatIndex →₀ Complex)
    {x : Real} (hx : 1 < x) :
    baezDuarteQTwoFiniteKernelSum c x =
      baezDuarteQTwoReciprocalMoment c * (x⁻¹ : Real) := by
  classical
  rw [baezDuarteQTwoFiniteKernelSum, baezDuarteQTwoReciprocalMoment,
    Finsupp.sum, Finsupp.sum]
  simp_rw [baezDuarteQTwoKernelFunction_eq_inv_mul_inv_of_one_lt _ hx]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem integral_Ioi_baezDuarteQTwoFiniteKernelSum
    (c : baezDuartePositiveNatIndex →₀ Complex)
    (s : Complex) (hs1 : s.re < 1) :
    (∫ x : Real in Ioi (1 : Real),
        (x : Complex) ^ (s - 1) * baezDuarteQTwoFiniteKernelSum c x) =
      baezDuarteQTwoReciprocalMoment c / (1 - s) := by
  let m : Complex := baezDuarteQTwoReciprocalMoment c
  have hpow : IntegrableOn (fun x : Real => (x : Complex) ^ (s - 2))
      (Ioi (1 : Real)) :=
    integrableOn_Ioi_cpow_of_lt (by
      change s.re - 2 < -1
      linarith) zero_lt_one
  calc
    (∫ x : Real in Ioi (1 : Real),
        (x : Complex) ^ (s - 1) * baezDuarteQTwoFiniteKernelSum c x) =
        ∫ x : Real in Ioi (1 : Real), m * (x : Complex) ^ (s - 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [baezDuarteQTwoFiniteKernelSum_eq_moment_mul_inv_of_one_lt c hx]
      dsimp only [m]
      push_cast
      rw [← Complex.cpow_neg_one]
      have hxne : (x : Complex) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hx))
      calc
        (x : Complex) ^ (s - 1) *
            (baezDuarteQTwoReciprocalMoment c * (x : Complex) ^ (-1 : Complex)) =
            baezDuarteQTwoReciprocalMoment c *
              ((x : Complex) ^ (s - 1) * (x : Complex) ^ (-1 : Complex)) := by ring
        _ = baezDuarteQTwoReciprocalMoment c *
              (x : Complex) ^ ((s - 1) + (-1 : Complex)) := by
          rw [← Complex.cpow_add _ _ hxne]
        _ = baezDuarteQTwoReciprocalMoment c * (x : Complex) ^ (s - 2) := by
          congr 2
          ring
    _ = m * ∫ x : Real in Ioi (1 : Real), (x : Complex) ^ (s - 2) := by
      rw [integral_const_mul]
    _ = m * (-((1 : Complex) ^ ((s - 2) + 1)) / ((s - 2) + 1)) := by
      rw [integral_Ioi_cpow_of_lt (by
        change s.re - 2 < -1
        linarith) zero_lt_one]
      norm_num
    _ = baezDuarteQTwoReciprocalMoment c / (1 - s) := by
      dsimp only [m]
      rw [show (s - 2) + 1 = s - 1 by ring, Complex.one_cpow]
      have hrel : 1 - s = -(s - 1) := by ring
      rw [hrel]
      simp only [div_eq_mul_inv, inv_neg]
      ring

/-- The finite generator sum as an element of complex `L2(0,infinity)`. -/
def baezDuarteQTwoFiniteKernelL2
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    positiveHalfLineComplexL2 :=
  c.sum fun n z => z • baezDuarteQTwoComplexKernelL2 n

theorem baezDuarteQTwoFiniteKernelL2_coeFn
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    baezDuarteQTwoFiniteKernelL2 c
      =ᵐ[volume.restrict (Ioi (0 : Real))]
        baezDuarteQTwoFiniteKernelSum c := by
  classical
  rw [baezDuarteQTwoFiniteKernelL2, Finsupp.sum]
  refine (Lp.coeFn_fun_finsetSum c.support fun n =>
    c n • baezDuarteQTwoComplexKernelL2 n).trans ?_
  have hfun :
      (fun x : Real => ∑ n ∈ c.support,
          ((c n • baezDuarteQTwoComplexKernelL2 n :
            positiveHalfLineComplexL2) : Real → Complex) x)
        =ᵐ[volume.restrict (Ioi (0 : Real))]
          (∑ n ∈ c.support,
            ((c n • baezDuarteQTwoComplexKernelL2 n :
              positiveHalfLineComplexL2) : Real → Complex)) := by
    exact ae_of_all _ fun x => by simp [Finset.sum_apply]
  refine hfun.trans ?_
  refine (eventuallyEq_sum
    (s := c.support) (l := ae (volume.restrict (Ioi (0 : Real))))
    (fun n _hn => by
      refine (Lp.coeFn_smul (c n) (baezDuarteQTwoComplexKernelL2 n)).trans ?_
      exact (baezDuarteQTwoComplexKernelL2_coeFn n).const_smul (c n))).trans ?_
  exact ae_of_all _ fun x => by
    simp [baezDuarteQTwoFiniteKernelSum, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finsupp.sum]

/-- The concrete full-half-line error used by the reverse criterion. -/
def baezDuarteQTwoMellinError
    (c : baezDuartePositiveNatIndex →₀ Complex) (x : Real) : Complex :=
  baezDuarteQTwoTargetFunction x - baezDuarteQTwoFiniteKernelSum c x

/-- The same approximation error in complex `L2(0,infinity)`. -/
def baezDuarteQTwoMellinErrorL2
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    positiveHalfLineComplexL2 :=
  baezDuarteQTwoComplexTargetL2 - baezDuarteQTwoFiniteKernelL2 c

theorem baezDuarteQTwoMellinErrorL2_coeFn
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    baezDuarteQTwoMellinErrorL2 c
      =ᵐ[volume.restrict (Ioi (0 : Real))]
        baezDuarteQTwoMellinError c := by
  refine (Lp.coeFn_sub baezDuarteQTwoComplexTargetL2
    (baezDuarteQTwoFiniteKernelL2 c)).trans ?_
  exact baezDuarteQTwoComplexTargetL2_coeFn.sub
    (baezDuarteQTwoFiniteKernelL2_coeFn c)

theorem baezDuarteQTwoMellinError_memLp_two
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    MemLp (baezDuarteQTwoMellinError c) (2 : ENNReal)
      (volume.restrict (Ioi (0 : Real))) := by
  classical
  have hsum : MemLp (baezDuarteQTwoFiniteKernelSum c) (2 : ENNReal)
      (volume.restrict (Ioi (0 : Real))) := by
    change MemLp
      (fun x : Real => ∑ n ∈ c.support,
        c n * baezDuarteQTwoKernelFunction n x)
      (2 : ENNReal) (volume.restrict (Ioi (0 : Real)))
    apply memLp_finsetSum
    intro n _hn
    convert
      (baezDuarteQTwoKernelFunction_memLp_two_positiveHalfLine n).const_smul (c n)
        using 1
    ext x
    rfl
  exact baezDuarteQTwoTargetFunction_memLp_two_positiveHalfLine.sub hsum

theorem baezDuarteQTwoMellinError_memLp_two_unitInterval
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    MemLp (baezDuarteQTwoMellinError c) (2 : ENNReal)
      (volume.restrict (Ioo (0 : Real) 1)) := by
  exact (baezDuarteQTwoMellinError_memLp_two c).mono_measure
    (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)

theorem positiveHalfLineComplexL2_norm_sq_eq_integral_norm_sq
    (f : positiveHalfLineComplexL2) :
    ‖f‖ ^ 2 = ∫ x : Real, ‖f x‖ ^ 2 ∂
      (volume.restrict (Ioi (0 : Real))) := by
  rw [← inner_self_eq_norm_sq (𝕜 := Complex), MeasureTheory.L2.inner_def]
  rw [← integral_re (MeasureTheory.L2.integrable_inner f f)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (inner Complex (f x) (f x)).re = ‖f x‖ ^ 2
    exact inner_self_eq_norm_sq (𝕜 := Complex) (f x)

theorem norm_baezDuarteQTwoMellinErrorL2_sq_eq_integral
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    ‖baezDuarteQTwoMellinErrorL2 c‖ ^ 2 =
      ∫ x : Real, ‖baezDuarteQTwoMellinError c x‖ ^ 2 ∂
        (volume.restrict (Ioi (0 : Real))) := by
  rw [positiveHalfLineComplexL2_norm_sq_eq_integral_norm_sq]
  exact integral_congr_ae
    ((baezDuarteQTwoMellinErrorL2_coeFn c).fun_comp
      (fun z : Complex => ‖z‖ ^ 2))

theorem integral_Ioi_norm_baezDuarteQTwoMellinError_sq
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    (∫ x : Real in Ioi (1 : Real),
        ‖baezDuarteQTwoMellinError c x‖ ^ 2) =
      ‖baezDuarteQTwoReciprocalMoment c‖ ^ 2 := by
  have hrpow {x : Real} (hx : 0 < x) :
      x ^ (-2 : Real) = (x ^ (2 : Nat))⁻¹ := by
    rw [show (-2 : Real) = -(2 : Real) by norm_num, Real.rpow_neg hx.le]
    exact congrArg Inv.inv (Real.rpow_natCast x 2)
  have hbase : (∫ x : Real in Ioi (1 : Real), x ^ (-2 : Real)) = 1 := by
    have h := integral_Ioi_rpow_of_lt
      (a := (-2 : Real)) (by norm_num) (c := (1 : Real)) (by norm_num)
    norm_num at h
    calc
      (∫ x : Real in Ioi (1 : Real), x ^ (-2 : Real)) =
          ∫ x : Real in Ioi (1 : Real), (x ^ (2 : Nat))⁻¹ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        exact hrpow (lt_trans zero_lt_one hx)
      _ = 1 := h
  calc
    (∫ x : Real in Ioi (1 : Real),
        ‖baezDuarteQTwoMellinError c x‖ ^ 2) =
        ∫ x : Real in Ioi (1 : Real),
          ‖baezDuarteQTwoReciprocalMoment c‖ ^ 2 * x ^ (-2 : Real) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      rw [baezDuarteQTwoMellinError,
        baezDuarteQTwoTargetFunction_eq_zero_of_one_lt hx,
        baezDuarteQTwoFiniteKernelSum_eq_moment_mul_inv_of_one_lt c hx,
        zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hx0), hrpow hx0]
      ring
    _ = ‖baezDuarteQTwoReciprocalMoment c‖ ^ 2 *
        ∫ x : Real in Ioi (1 : Real), x ^ (-2 : Real) := by
      rw [integral_const_mul]
    _ = ‖baezDuarteQTwoReciprocalMoment c‖ ^ 2 := by rw [hbase, mul_one]

theorem integral_unitInterval_norm_baezDuarteQTwoMellinError_sq_le
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    (∫ x : Real in Ioo (0 : Real) 1,
        ‖baezDuarteQTwoMellinError c x‖ ^ 2) ≤
      ‖baezDuarteQTwoMellinErrorL2 c‖ ^ 2 := by
  have hfull : Integrable
      (fun x : Real => ‖baezDuarteQTwoMellinError c x‖ ^ 2)
      (volume.restrict (Ioi (0 : Real))) :=
    (memLp_two_iff_integrable_sq_norm
      (baezDuarteQTwoMellinError_memLp_two c).1).mp
        (baezDuarteQTwoMellinError_memLp_two c)
  rw [norm_baezDuarteQTwoMellinErrorL2_sq_eq_integral]
  exact setIntegral_mono_set hfull (ae_of_all _ fun _ => sq_nonneg _)
    Ioo_subset_Ioi_self.eventuallyLE

theorem norm_baezDuarteQTwoReciprocalMoment_sq_le
    (c : baezDuartePositiveNatIndex →₀ Complex) :
    ‖baezDuarteQTwoReciprocalMoment c‖ ^ 2 ≤
      ‖baezDuarteQTwoMellinErrorL2 c‖ ^ 2 := by
  have hfull : Integrable
      (fun x : Real => ‖baezDuarteQTwoMellinError c x‖ ^ 2)
      (volume.restrict (Ioi (0 : Real))) :=
    (memLp_two_iff_integrable_sq_norm
      (baezDuarteQTwoMellinError_memLp_two c).1).mp
        (baezDuarteQTwoMellinError_memLp_two c)
  rw [← integral_Ioi_norm_baezDuarteQTwoMellinError_sq,
    norm_baezDuarteQTwoMellinErrorL2_sq_eq_integral]
  exact setIntegral_mono_set hfull (ae_of_all _ fun _ => sq_nonneg _)
    (Ioi_subset_Ioi zero_le_one).eventuallyLE

theorem baezDuarteQTwoComplexTarget_mem_closure_iff_approx :
    baezDuarteQTwoComplexTargetL2 ∈ baezDuarteQTwoComplexKernelClosure ↔
      ∀ ε : Real, 0 < ε →
        ∃ c : baezDuartePositiveNatIndex →₀ Complex,
          ‖baezDuarteQTwoMellinErrorL2 c‖ < ε := by
  constructor
  · intro hclosure ε hε
    have hmetric : baezDuarteQTwoComplexTargetL2 ∈
        closure
          (baezDuarteQTwoComplexKernelSpan : Set positiveHalfLineComplexL2) := by
      rwa [← baezDuarteQTwoComplexKernelClosure_coe]
    obtain ⟨g, hgspan, hgdist⟩ := Metric.mem_closure_iff.mp hmetric ε hε
    rcases (mem_baezDuarteQTwoComplexKernelSpan_iff_exists_finsupp_sum g).mp
      hgspan with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    simpa [baezDuarteQTwoMellinErrorL2, baezDuarteQTwoFiniteKernelL2,
      hc, dist_eq_norm] using hgdist
  · intro happrox
    change baezDuarteQTwoComplexTargetL2 ∈
      (baezDuarteQTwoComplexKernelClosure : Set positiveHalfLineComplexL2)
    rw [baezDuarteQTwoComplexKernelClosure_coe]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨c, hc⟩ := happrox ε hε
    refine ⟨baezDuarteQTwoFiniteKernelL2 c, ?_, ?_⟩
    · exact
        (mem_baezDuarteQTwoComplexKernelSpan_iff_exists_finsupp_sum _).mpr
          ⟨c, rfl⟩
    · simpa [baezDuarteQTwoMellinErrorL2, dist_eq_norm] using hc

theorem integral_Ioo_baezDuarteQTwoTargetFunction
    (s : Complex) (hs0 : 0 < s.re) :
    (∫ x : Real in Ioo (0 : Real) 1,
        (x : Complex) ^ (s - 1) * baezDuarteQTwoTargetFunction x) =
      1 / s ^ 2 := by
  let g : Real → Complex := fun x =>
    (x : Complex) ^ (s - 1) * baezDuarteQTwoTargetFunction x
  have hM := hasMellin_baezDuarteQTwoTargetFunction s hs0
  have htotal : IntegrableOn g (Ioi (0 : Real)) := by
    simpa only [MellinConvergent, g, smul_eq_mul] using hM.1
  have htail : IntegrableOn g (Ioi (1 : Real)) :=
    htotal.mono_set (Ioi_subset_Ioi zero_le_one)
  have htail_zero : (∫ x : Real in Ioi (1 : Real), g x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [g]
    rw [baezDuarteQTwoTargetFunction_eq_zero_of_one_lt hx, mul_zero]
    rfl
  have hvalue : (∫ x : Real in Ioi (0 : Real), g x) = 1 / s ^ 2 := by
    simpa only [mellin, g, smul_eq_mul] using hM.2
  have hsplit := hvalue
  rw [← intervalIntegral.integral_interval_add_Ioi htotal htail,
    htail_zero, add_zero] at hsplit
  have hinterval :
      (∫ x : Real in (0 : Real)..1, g x) =
        ∫ x : Real in Ioo (0 : Real) 1, g x := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
  rw [hinterval] at hsplit
  exact hsplit

theorem integral_baezDuarteQTwoMellinError_eq
    (c : baezDuartePositiveNatIndex →₀ Complex) (s : Complex)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) :
    (∫ x : Real,
        (x : Complex) ^ (s - 1) * baezDuarteQTwoMellinError c x ∂
          (volume.restrict (Ioo (0 : Real) 1))) =
      1 / s ^ 2 + baezDuarteQTwoReciprocalMoment c / (1 - s) := by
  let g : Real → Complex := fun x =>
    (x : Complex) ^ (s - 1) * baezDuarteQTwoFiniteKernelSum c x
  have hM := hasMellin_baezDuarteQTwoFiniteKernelSum_zero c s hs0 hs1 hz
  have htotal : IntegrableOn g (Ioi (0 : Real)) := by
    simpa only [MellinConvergent, g, smul_eq_mul] using hM.1
  have htail : IntegrableOn g (Ioi (1 : Real)) :=
    htotal.mono_set (Ioi_subset_Ioi zero_le_one)
  have hzero : (∫ x : Real in Ioi (0 : Real), g x) = 0 := by
    simpa only [mellin, g, smul_eq_mul] using hM.2
  have hsplit :
      (∫ x : Real in (0 : Real)..1, g x) +
          (∫ x : Real in Ioi (1 : Real), g x) = 0 := by
    have h := hzero
    rw [← intervalIntegral.integral_interval_add_Ioi htotal htail] at h
    exact h
  have hlocal_sum :
      (∫ x : Real in Ioo (0 : Real) 1, g x) =
        -baezDuarteQTwoReciprocalMoment c / (1 - s) := by
    have htail_value := integral_Ioi_baezDuarteQTwoFiniteKernelSum c s hs1
    have hinterval :
        (∫ x : Real in (0 : Real)..1, g x) =
          ∫ x : Real in Ioo (0 : Real) 1, g x := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo]
    rw [hinterval, htail_value] at hsplit
    linear_combination hsplit
  have htarget_total :=
    (hasMellin_baezDuarteQTwoTargetFunction s hs0).1
  have htarget_local : Integrable
      (fun x : Real =>
        (x : Complex) ^ (s - 1) * baezDuarteQTwoTargetFunction x)
      (volume.restrict (Ioo (0 : Real) 1)) := by
    have htarget_ioi : IntegrableOn
        (fun x : Real =>
          (x : Complex) ^ (s - 1) * baezDuarteQTwoTargetFunction x)
        (Ioi (0 : Real)) := by
      simpa only [MellinConvergent, smul_eq_mul] using htarget_total
    exact htarget_ioi.mono_set Ioo_subset_Ioi_self
  have hsum_local : Integrable g
      (volume.restrict (Ioo (0 : Real) 1)) :=
    htotal.mono_set Ioo_subset_Ioi_self
  calc
    (∫ x : Real,
        (x : Complex) ^ (s - 1) * baezDuarteQTwoMellinError c x ∂
          (volume.restrict (Ioo (0 : Real) 1))) =
        (∫ x : Real in Ioo (0 : Real) 1,
          (x : Complex) ^ (s - 1) * baezDuarteQTwoTargetFunction x) -
        ∫ x : Real in Ioo (0 : Real) 1, g x := by
      rw [← integral_sub htarget_local hsum_local]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only [g]
      rw [baezDuarteQTwoMellinError]
      ring
    _ = 1 / s ^ 2 -
        (-baezDuarteQTwoReciprocalMoment c / (1 - s)) := by
      rw [integral_Ioo_baezDuarteQTwoTargetFunction s hs0, hlocal_sum]
    _ = 1 / s ^ 2 + baezDuarteQTwoReciprocalMoment c / (1 - s) := by ring

theorem norm_integral_baezDuarteQTwoMellinError_le
    (c : baezDuartePositiveNatIndex →₀ Complex)
    (s : Complex) (hs : 1 / 2 < s.re) :
    ‖∫ x : Real,
        (x : Complex) ^ (s - 1) * baezDuarteQTwoMellinError c x ∂
          (volume.restrict (Ioo (0 : Real) 1))‖ ≤
      (∫ x : Real, ‖(x : Complex) ^ (s - 1)‖ ^ (2 : Real) ∂
          (volume.restrict (Ioo (0 : Real) 1))) ^ (1 / (2 : Real)) *
        (∫ x : Real, ‖baezDuarteQTwoMellinError c x‖ ^ (2 : Real) ∂
          (volume.restrict (Ioo (0 : Real) 1))) ^ (1 / (2 : Real)) := by
  let μ := volume.restrict (Ioo (0 : Real) 1)
  have hw := mellinWeight_memLp_two_unitInterval s hs
  have he := baezDuarteQTwoMellinError_memLp_two_unitInterval c
  have hw' : MemLp (fun x : Real => (x : Complex) ^ (s - 1))
      (ENNReal.ofReal (2 : Real)) μ := by simpa [μ] using hw
  have he' : MemLp (baezDuarteQTwoMellinError c)
      (ENNReal.ofReal (2 : Real)) μ := by simpa [μ] using he
  calc
    ‖∫ x : Real,
        (x : Complex) ^ (s - 1) * baezDuarteQTwoMellinError c x ∂μ‖ ≤
        ∫ x : Real,
          ‖(x : Complex) ^ (s - 1) * baezDuarteQTwoMellinError c x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : Real,
        ‖(x : Complex) ^ (s - 1)‖ *
          ‖baezDuarteQTwoMellinError c x‖ ∂μ := by
      congr 1
      funext x
      rw [norm_mul]
    _ ≤ (∫ x : Real, ‖(x : Complex) ^ (s - 1)‖ ^ (2 : Real) ∂μ) ^
          (1 / (2 : Real)) *
        (∫ x : Real, ‖baezDuarteQTwoMellinError c x‖ ^ (2 : Real) ∂μ) ^
          (1 / (2 : Real)) := by
      exact integral_mul_norm_le_Lp_mul_Lq
        (Real.HolderConjugate.two_two) hw' he'

/-- The `q = 2` closure excludes every zeta zero strictly right of the critical line. -/
theorem riemannZeta_ne_zero_of_baezDuarteQTwoComplexTarget_mem_closure
    (hclosure : baezDuarteQTwoComplexTargetL2 ∈
      baezDuarteQTwoComplexKernelClosure)
    {s : Complex} (hs_half : 1 / 2 < s.re) (hs_one : s.re < 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : 0 < s.re := by linarith
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs_half
    norm_num at hs_half
  let A : Real :=
    (∫ x : Real, ‖(x : Complex) ^ (s - 1)‖ ^ (2 : Real) ∂
      (volume.restrict (Ioo (0 : Real) 1))) ^ (1 / (2 : Real))
  let B : Real := ‖(1 - s)⁻¹‖
  let Q : Real := ‖1 / s ^ 2‖
  let D : Real := A + B + 1
  let ε : Real := Q / (2 * D)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact norm_pos_iff.mpr
      (div_ne_zero one_ne_zero (pow_ne_zero 2 hs_ne))
  have hD : 0 < D := by dsimp only [D]; linarith
  have hε : 0 < ε := by dsimp only [ε]; positivity
  obtain ⟨c, hc⟩ :=
    (baezDuarteQTwoComplexTarget_mem_closure_iff_approx.mp hclosure) ε hε
  let L : Real :=
    (∫ x : Real in Ioo (0 : Real) 1,
      ‖baezDuarteQTwoMellinError c x‖ ^ 2) ^ (1 / (2 : Real))
  have hlocal_root_le : L ≤ ‖baezDuarteQTwoMellinErrorL2 c‖ := by
    dsimp only [L]
    rw [← Real.sqrt_eq_rpow]
    calc
      Real.sqrt (∫ x : Real in Ioo (0 : Real) 1,
          ‖baezDuarteQTwoMellinError c x‖ ^ 2) ≤
          Real.sqrt (‖baezDuarteQTwoMellinErrorL2 c‖ ^ 2) :=
        Real.sqrt_le_sqrt
          (integral_unitInterval_norm_baezDuarteQTwoMellinError_sq_le c)
      _ = ‖baezDuarteQTwoMellinErrorL2 c‖ :=
        Real.sqrt_sq (norm_nonneg _)
  have hm_le : ‖baezDuarteQTwoReciprocalMoment c‖ ≤
      ‖baezDuarteQTwoMellinErrorL2 c‖ := by
    nlinarith [norm_nonneg (baezDuarteQTwoReciprocalMoment c),
      norm_nonneg (baezDuarteQTwoMellinErrorL2 c),
      norm_baezDuarteQTwoReciprocalMoment_sq_le c]
  have hL_lt : L < ε := hlocal_root_le.trans_lt hc
  have hm_lt : ‖baezDuarteQTwoReciprocalMoment c‖ < ε := hm_le.trans_lt hc
  let I : Complex := ∫ x : Real,
    (x : Complex) ^ (s - 1) * baezDuarteQTwoMellinError c x ∂
      (volume.restrict (Ioo (0 : Real) 1))
  have hI : ‖I‖ ≤ A * L := by
    simpa only [I, A, L, Real.rpow_two] using
      norm_integral_baezDuarteQTwoMellinError_le c s hs_half
  have hidentity :
      1 / s ^ 2 = I - baezDuarteQTwoReciprocalMoment c / (1 - s) := by
    have h := integral_baezDuarteQTwoMellinError_eq c s hs0 hs_one hz
    change I = 1 / s ^ 2 +
      baezDuarteQTwoReciprocalMoment c / (1 - s) at h
    rw [h]
    ring
  have htail_norm :
      ‖baezDuarteQTwoReciprocalMoment c / (1 - s)‖ =
        ‖baezDuarteQTwoReciprocalMoment c‖ * B := by
    dsimp only [B]
    rw [norm_div, norm_inv]
    ring
  have hQ_bound : Q ≤
      A * L + B * ‖baezDuarteQTwoReciprocalMoment c‖ := by
    dsimp only [Q]
    rw [hidentity]
    calc
      ‖I - baezDuarteQTwoReciprocalMoment c / (1 - s)‖ ≤
          ‖I‖ + ‖baezDuarteQTwoReciprocalMoment c / (1 - s)‖ :=
        norm_sub_le _ _
      _ ≤ A * L + B * ‖baezDuarteQTwoReciprocalMoment c‖ := by
        rw [htail_norm, mul_comm ‖baezDuarteQTwoReciprocalMoment c‖ B]
        gcongr
  have hsmall :
      A * L + B * ‖baezDuarteQTwoReciprocalMoment c‖ ≤
        (A + B) * ε := by
    calc
      A * L + B * ‖baezDuarteQTwoReciprocalMoment c‖ ≤
          A * ε + B * ε := by gcongr
      _ = (A + B) * ε := by ring
  have hstrict : (A + B) * ε < Q := by
    dsimp only [ε]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hD)).2
    dsimp only [D] at hD ⊢
    have hpos : 0 < Q * (A + B + 2) := mul_pos hQ (by linarith)
    nlinarith
  exact (not_lt_of_ge (hQ_bound.trans hsmall)) hstrict

/-- Reverse half of the exact `q = 2` Baez-Duarte criterion. -/
theorem baezDuarteQTwoComplexTarget_mem_closure_imp_riemannHypothesis
    (hclosure : baezDuarteQTwoComplexTargetL2 ∈
      baezDuarteQTwoComplexKernelClosure) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro s hs
  rw [OnCriticalLine]
  rcases lt_trichotomy s.re (1 / 2) with hleft | hline | hright
  · have hreflect_zero := riemannZeta_one_sub_eq_zero_of_isNontrivialZero hs
    have hreflect_half : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    by_cases hreflect_one : (1 - s).re < 1
    · exact False.elim
        (riemannZeta_ne_zero_of_baezDuarteQTwoComplexTarget_mem_closure
          hclosure hreflect_half hreflect_one hreflect_zero)
    · exact False.elim
        (riemannZeta_ne_zero_of_one_le_re
          (le_of_not_gt hreflect_one) hreflect_zero)
  · exact hline
  · exact False.elim
      (riemannZeta_ne_zero_of_baezDuarteQTwoComplexTarget_mem_closure
        hclosure hright (nontrivial_zero_re_lt_one hs) hs.1)

/-- Ehm's twice-weighted positive-natural criterion in the project's exact closure model. -/
theorem riemannHypothesis_iff_baezDuarteQTwoComplexTarget_mem_kernelClosure :
    RiemannHypothesis ↔
      baezDuarteQTwoComplexTargetL2 ∈
        baezDuarteQTwoComplexKernelClosure := by
  exact
    ⟨RiemannHypothesis.baezDuarteQTwoComplexTargetL2_mem_kernelClosure,
      baezDuarteQTwoComplexTarget_mem_closure_imp_riemannHypothesis⟩

end LeanLab.Riemann
