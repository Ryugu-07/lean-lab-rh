import LeanLab.Riemann.LevinsonMontgomeryHeightTenRiemannSiegelLowZero
import LeanLab.Riemann.DeBruijnNewmanPolymathStieltjesScaledGamma

set_option linter.style.header false

/-!
# Phase-aware Riemann--Siegel norm reduction at height ten

This module retains the principal-argument contribution in the critical-line complex power.
It reduces a uniform two-variable raw-integral bound to two fixed endpoint half-line masses and
connects that bound, together with a prefactor phase margin, to the existing literal low-zero
remainder margin.
-/

open Complex MeasureTheory Real Set

namespace LeanLab.Riemann

noncomputable section

def heightTenRiemannSiegelCriticalPoint (y : ℝ) : ℂ :=
  (1 / 2 : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem heightTenRiemannSiegelCriticalPoint_re (y : ℝ) :
    (heightTenRiemannSiegelCriticalPoint y).re = 1 / 2 := by
  simp [heightTenRiemannSiegelCriticalPoint]

@[simp] theorem heightTenRiemannSiegelCriticalPoint_im (y : ℝ) :
    (heightTenRiemannSiegelCriticalPoint y).im = y := by
  simp [heightTenRiemannSiegelCriticalPoint]

theorem norm_cpow_neg_heightTenRiemannSiegelCriticalPoint
    (N : ℕ) (v y : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint y)‖ =
      ‖deBruijnNewmanRiemannSiegelLine N v‖ ^ (-(1 / 2 : ℝ)) *
        Real.exp (y * Complex.arg (deBruijnNewmanRiemannSiegelLine N v)) := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hw : w ≠ 0 :=
    Complex.slitPlane_ne_zero (deBruijnNewmanRiemannSiegelLine_mem_slitPlane N v)
  rw [Complex.norm_cpow_of_ne_zero hw]
  simp only [heightTenRiemannSiegelCriticalPoint_re,
    heightTenRiemannSiegelCriticalPoint_im, Complex.neg_re, Complex.neg_im]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  dsimp [w]
  congr 1
  ring_nf

theorem deBruijnNewmanRiemannSiegelLine_arg_nonneg_of_nonpos
    (N : ℕ) {v : ℝ} (hv : v ≤ 0) :
    0 ≤ Complex.arg (deBruijnNewmanRiemannSiegelLine N v) := by
  rw [Complex.arg_nonneg_iff, deBruijnNewmanRiemannSiegelLine_im]
  have hsqrt : 0 < Real.sqrt 2 / 2 := by positivity
  nlinarith

theorem deBruijnNewmanRiemannSiegelLine_arg_nonpos_of_nonneg
    (N : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine N v) ≤ 0 := by
  rcases hv.eq_or_lt with rfl | hv
  · rw [deBruijnNewmanRiemannSiegelLine]
    rw [show (((0 : ℝ) : ℂ)) = 0 by norm_num, mul_zero, add_zero]
    have hcast :
        (N : ℂ) + 1 / 2 = ((((N : ℝ) + 1 / 2 : ℝ) : ℂ)) := by
      norm_num
    rw [hcast]
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
  · exact (Complex.arg_neg_iff.mpr (by
      rw [deBruijnNewmanRiemannSiegelLine_im]
      have hsqrt : 0 < Real.sqrt 2 / 2 := by positivity
      nlinarith)).le

theorem normSq_sin_pi_mul_deBruijnNewmanRiemannSiegelLine
    (N : ℕ) (v : ℝ) :
    Complex.normSq (Complex.sin
        ((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v)) =
      Real.sinh (Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im) ^ 2 +
        Real.cos (Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im) ^ 2 := by
  rw [normSq_complex_sin]
  let u : ℝ := Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im
  have hre : (((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v).re) =
      (u + N * Real.pi) + Real.pi / 2 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, u]
    rw [deBruijnNewmanRiemannSiegelLine_re_eq]
    ring
  have him : (((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v).im) = u := by
    simp [u, Complex.mul_im]
  rw [hre, him, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    Real.cos_add_nat_mul_pi, Real.sin_add_nat_mul_pi]
  have htrig : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hcosh := Real.cosh_sq u
  have hsign : ((-1 : ℝ) ^ N) ^ 2 = 1 := by rw [← pow_mul]; simp
  simp only [mul_pow, neg_sq, hsign, one_mul]
  nlinarith

theorem two_mul_abs_sinh_le_norm_deBruijnNewmanRiemannSiegelDenominator
    (N : ℕ) (v : ℝ) :
    2 * |Real.sinh (Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im)| ≤
      ‖deBruijnNewmanRiemannSiegelDenominator
        (deBruijnNewmanRiemannSiegelLine N v)‖ := by
  let z := Complex.sin ((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v)
  let u := Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im
  have hnormsq : ‖z‖ ^ 2 = Real.sinh u ^ 2 + Real.cos u ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact normSq_sin_pi_mul_deBruijnNewmanRiemannSiegelLine N v
  have hsinh : |Real.sinh u| ≤ ‖z‖ := by
    have habs : |Real.sinh u| ^ 2 = Real.sinh u ^ 2 := sq_abs _
    nlinarith [sq_nonneg (Real.cos u), abs_nonneg (Real.sinh u), norm_nonneg z]
  rw [deBruijnNewmanRiemannSiegelDenominator_eq, norm_mul, norm_mul]
  norm_num
  simpa [z, u, deBruijnNewmanRiemannSiegelLine_im, Real.sinh_neg] using hsinh

theorem norm_deBruijnNewmanRiemannSiegelLine_one_sq (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ 2 =
      v ^ 2 - (3 * Real.sqrt 2 / 2) * v + 9 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply,
    deBruijnNewmanRiemannSiegelLine_re,
    deBruijnNewmanRiemannSiegelLine_im]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  norm_num
  nlinarith

theorem one_le_norm_deBruijnNewmanRiemannSiegelLine_one (v : ℝ) :
    1 ≤ ‖deBruijnNewmanRiemannSiegelLine 1 v‖ := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hsq : 0 ≤ (v - 3 * Real.sqrt 2 / 4) ^ 2 := sq_nonneg _
  have hnorm := norm_deBruijnNewmanRiemannSiegelLine_one_sq v
  nlinarith [norm_nonneg (deBruijnNewmanRiemannSiegelLine 1 v)]

theorem rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_le_one (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine 1 v‖ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos
    (one_le_norm_deBruijnNewmanRiemannSiegelLine_one v) (by norm_num)

theorem norm_cpow_heightTenRiemannSiegelCriticalPoint_le_ten_of_nonpos
    (N : ℕ) {v y : ℝ} (hv : v ≤ 0) (hy : y ≤ 10) :
    ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint y)‖ ≤
      ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint 10)‖ := by
  rw [norm_cpow_neg_heightTenRiemannSiegelCriticalPoint,
    norm_cpow_neg_heightTenRiemannSiegelCriticalPoint]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have harg := deBruijnNewmanRiemannSiegelLine_arg_nonneg_of_nonpos N hv
  nlinarith

theorem norm_cpow_heightTenRiemannSiegelCriticalPoint_le_thirteenHalves_of_nonneg
    (N : ℕ) {v y : ℝ} (hv : 0 ≤ v) (hy : 13 / 2 ≤ y) :
    ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint y)‖ ≤
      ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint (13 / 2))‖ := by
  rw [norm_cpow_neg_heightTenRiemannSiegelCriticalPoint,
    norm_cpow_neg_heightTenRiemannSiegelCriticalPoint]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have harg := deBruijnNewmanRiemannSiegelLine_arg_nonpos_of_nonneg N hv
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_le_ten_of_nonpos
    (N : ℕ) {v y : ℝ} (hv : v ≤ 0) (hy : y ≤ 10) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N
        (heightTenRiemannSiegelCriticalPoint y) v‖ ≤
      ‖deBruijnNewmanRiemannSiegelLineIntegrand N
        (heightTenRiemannSiegelCriticalPoint 10) v‖ := by
  unfold deBruijnNewmanRiemannSiegelLineIntegrand
    deBruijnNewmanRiemannSiegelKernel deBruijnNewmanRiemannSiegelNumerator
  simp only [norm_mul, norm_div]
  gcongr
  exact norm_cpow_heightTenRiemannSiegelCriticalPoint_le_ten_of_nonpos N hv hy

theorem norm_heightTenRiemannSiegelLineIntegrand_le_thirteenHalves_of_nonneg
    (N : ℕ) {v y : ℝ} (hv : 0 ≤ v) (hy : 13 / 2 ≤ y) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N
        (heightTenRiemannSiegelCriticalPoint y) v‖ ≤
      ‖deBruijnNewmanRiemannSiegelLineIntegrand N
        (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖ := by
  unfold deBruijnNewmanRiemannSiegelLineIntegrand
    deBruijnNewmanRiemannSiegelKernel deBruijnNewmanRiemannSiegelNumerator
  simp only [norm_mul, norm_div]
  gcongr
  exact norm_cpow_heightTenRiemannSiegelCriticalPoint_le_thirteenHalves_of_nonneg N hv hy

def heightTenRiemannSiegelNegativeEndpointMass (N : ℕ) : ℝ :=
  ∫ v in Set.Iic (0 : ℝ),
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N
      (heightTenRiemannSiegelCriticalPoint 10) v‖

def heightTenRiemannSiegelPositiveEndpointMass (N : ℕ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ),
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N
      (heightTenRiemannSiegelCriticalPoint (13 / 2)) v‖

theorem norm_deBruijnNewmanRiemannSiegelRawIntegral_le_endpointMasses
    (N : ℕ) {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    ‖deBruijnNewmanRiemannSiegelRawIntegral N
        (heightTenRiemannSiegelCriticalPoint y)‖ ≤
      heightTenRiemannSiegelNegativeEndpointMass N +
        heightTenRiemannSiegelPositiveEndpointMass N := by
  let f : ℝ → ℂ := deBruijnNewmanRiemannSiegelLineIntegrand N
    (heightTenRiemannSiegelCriticalPoint y)
  have hf : Integrable f :=
    integrable_deBruijnNewmanRiemannSiegelLineIntegrand N
      (heightTenRiemannSiegelCriticalPoint y)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hf.integrableOn hf.integrableOn
  unfold deBruijnNewmanRiemannSiegelRawIntegral
  change ‖∫ v : ℝ, f v‖ ≤ _
  rw [← hsplit]
  calc
    ‖(∫ v in Set.Iic (0 : ℝ), f v) + (∫ v in Set.Ioi (0 : ℝ), f v)‖ ≤
        ‖∫ v in Set.Iic (0 : ℝ), f v‖ + ‖∫ v in Set.Ioi (0 : ℝ), f v‖ :=
      norm_add_le _ _
    _ ≤ heightTenRiemannSiegelNegativeEndpointMass N +
          heightTenRiemannSiegelPositiveEndpointMass N := by
      apply add_le_add
      · apply MeasureTheory.norm_integral_le_of_norm_le
          (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N
            (heightTenRiemannSiegelCriticalPoint 10)).norm.integrableOn
        rw [ae_restrict_iff' measurableSet_Iic]
        filter_upwards with v hv
        exact norm_heightTenRiemannSiegelLineIntegrand_le_ten_of_nonpos N hv hy1
      · apply MeasureTheory.norm_integral_le_of_norm_le
          (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N
            (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
        rw [ae_restrict_iff' measurableSet_Ioi]
        filter_upwards with v hv
        exact norm_heightTenRiemannSiegelLineIntegrand_le_thirteenHalves_of_nonneg
          N hv.le hy0

def HeightTenRiemannSiegelOneEndpointMassBound : Prop :=
  heightTenRiemannSiegelNegativeEndpointMass 1 +
    heightTenRiemannSiegelPositiveEndpointMass 1 ≤ 3 / 5

theorem heightTenRiemannSiegelOneEndpointMassBound_of_individual
    (hneg : heightTenRiemannSiegelNegativeEndpointMass 1 ≤ 1 / 10)
    (hpos : heightTenRiemannSiegelPositiveEndpointMass 1 ≤ 1 / 2) :
    HeightTenRiemannSiegelOneEndpointMassBound := by
  dsimp [HeightTenRiemannSiegelOneEndpointMassBound]
  nlinarith

theorem norm_deBruijnNewmanRiemannSiegelRawIntegral_one_le_threeFifths
    (hmass : HeightTenRiemannSiegelOneEndpointMassBound)
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    ‖deBruijnNewmanRiemannSiegelRawIntegral 1
        (heightTenRiemannSiegelCriticalPoint y)‖ ≤ 3 / 5 := by
  exact (norm_deBruijnNewmanRiemannSiegelRawIntegral_le_endpointMasses 1 hy0 hy1).trans hmass

def HeightTenRiemannSiegelOnePrefactorPhaseMargin : Prop :=
  ∀ y : ℝ, 13 / 2 ≤ y → y ≤ 10 →
    (9 / 10 : ℝ) *
        ‖deBruijnNewmanRiemannSiegelPrefactor
          (heightTenRiemannSiegelCriticalPoint y)‖ <
      |(deBruijnNewmanRiemannSiegelPrefactor
        (heightTenRiemannSiegelCriticalPoint y)).re|

theorem heightTenRiemannSiegelOneRemainderMargin_of_phaseNormBounds
    (hmass : HeightTenRiemannSiegelOneEndpointMassBound)
    (hphase : HeightTenRiemannSiegelOnePrefactorPhaseMargin) :
    HeightTenRiemannSiegelOneRemainderMargin := by
  intro y hy0 hy1
  let s := heightTenRiemannSiegelCriticalPoint y
  have hraw :
      ‖deBruijnNewmanRiemannSiegelRawIntegral 1 s‖ ≤ 3 / 5 := by
    exact norm_deBruijnNewmanRiemannSiegelRawIntegral_one_le_threeFifths
      hmass hy0 hy1
  calc
    |(deBruijnNewmanRiemannSiegelR0N 1 s).re| ≤
        ‖deBruijnNewmanRiemannSiegelR0N 1 s‖ := Complex.abs_re_le_norm _
    _ = ‖deBruijnNewmanRiemannSiegelPrefactor s‖ *
          ‖deBruijnNewmanRiemannSiegelRawIntegral 1 s‖ := by
      rw [deBruijnNewmanRiemannSiegelR0N, norm_mul]
    _ ≤ ‖deBruijnNewmanRiemannSiegelPrefactor s‖ * (3 / 5) := by
      exact mul_le_mul_of_nonneg_left hraw (norm_nonneg _)
    _ ≤ (9 / 10) * ‖deBruijnNewmanRiemannSiegelPrefactor s‖ := by
      nlinarith [norm_nonneg (deBruijnNewmanRiemannSiegelPrefactor s)]
    _ < |(deBruijnNewmanRiemannSiegelPrefactor s).re| := by
      exact hphase y hy0 hy1

def heightTenStieltjesRectangularMajorant (b t : ℝ) : ℝ :=
  (1 / 8) * (t ^ 2 + b ^ 2)⁻¹

theorem norm_deBruijnNewmanPolymathStieltjesIntegrand_le_rectangular
    {z : ℂ} (hz : 0 < z.re) (hzIm : z.im ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖deBruijnNewmanPolymathStieltjesIntegrand z t‖ ≤
      heightTenStieltjesRectangularMajorant z.im t := by
  have hQ0 := deBruijnNewmanPolymathStieltjesQ_nonneg t
  have hQ8 := deBruijnNewmanPolymathStieltjesQ_le_one_eighth t
  have hpointRe : 0 < (z + (t : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hpointNorm : 0 < ‖z + (t : ℂ)‖ :=
    hpointRe.trans_le ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hdenSq : ‖z + (t : ℂ)‖ ^ 2 =
      (z.re + t) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, add_zero]
    ring
  have hbasePos : 0 < t ^ 2 + z.im ^ 2 := by
    have himsq : 0 < z.im ^ 2 := sq_pos_of_ne_zero hzIm
    nlinarith [sq_nonneg t]
  have hdenLower : t ^ 2 + z.im ^ 2 ≤ ‖z + (t : ℂ)‖ ^ 2 := by
    rw [hdenSq]
    nlinarith [mul_nonneg ht hz.le]
  have hinv : (‖z + (t : ℂ)‖ ^ 2)⁻¹ ≤ (t ^ 2 + z.im ^ 2)⁻¹ :=
    (inv_le_inv₀ (sq_pos_of_pos hpointNorm) hbasePos).2 hdenLower
  rw [deBruijnNewmanPolymathStieltjesIntegrand,
    heightTenStieltjesRectangularMajorant, norm_div, norm_pow, norm_real,
    Real.norm_of_nonneg hQ0, div_eq_mul_inv]
  exact mul_le_mul hQ8 hinv (inv_nonneg.mpr (sq_nonneg _)) (by norm_num)

theorem integrable_heightTenStieltjesRectangularKernel {b : ℝ} (hb : b ≠ 0) :
    Integrable (fun t : ℝ => (t ^ 2 + b ^ 2)⁻¹) := by
  have hbase : Integrable (fun t : ℝ => (1 + (b⁻¹ * t) ^ 2)⁻¹) := by
    exact integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hb)
  have hscaled := hbase.const_mul ((b ^ 2)⁻¹)
  convert hscaled using 1
  funext t
  field_simp
  ring

theorem integrableOn_heightTenStieltjesRectangularMajorant
    {b : ℝ} (hb : b ≠ 0) :
    IntegrableOn (heightTenStieltjesRectangularMajorant b) (Ioi (0 : ℝ)) := by
  exact (integrable_heightTenStieltjesRectangularKernel hb).const_mul (1 / 8) |>.integrableOn

theorem integral_heightTenStieltjesRectangularKernel_Ioi
    {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, (t ^ 2 + b ^ 2)⁻¹) = Real.pi / (2 * b) := by
  let g : ℝ → ℝ := fun t => (t ^ 2 + b ^ 2)⁻¹
  have hscale := integral_comp_mul_left_Ioi g 0 hb
  have hleft :
      (∫ x : ℝ in Ioi 0, g (b * x)) = (b ^ 2)⁻¹ * (Real.pi / 2) := by
    calc
      (∫ x : ℝ in Ioi 0, g (b * x)) =
          ∫ x : ℝ in Ioi 0, (b ^ 2)⁻¹ * (1 + x ^ 2)⁻¹ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp [g]
        field_simp
        ring
      _ = (b ^ 2)⁻¹ * (Real.pi / 2) := by
        rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
        simp
  simp only [mul_zero, smul_eq_mul] at hscale
  rw [hleft] at hscale
  change (b ^ 2)⁻¹ * (Real.pi / 2) =
    b⁻¹ * (∫ x : ℝ in Ioi 0, g x) at hscale
  change (∫ t : ℝ in Ioi 0, g t) = Real.pi / (2 * b)
  field_simp at hscale ⊢
  simpa [mul_comm] using hscale.symm

theorem integral_heightTenStieltjesRectangularMajorant_Ioi
    {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, heightTenStieltjesRectangularMajorant b t) =
      Real.pi / (16 * b) := by
  change (∫ t : ℝ in Ioi 0, (1 / 8) * (t ^ 2 + b ^ 2)⁻¹) = _
  rw [integral_const_mul,
    integral_heightTenStieltjesRectangularKernel_Ioi hb]
  ring

theorem norm_deBruijnNewmanPolymathStieltjesLogRemainder_le_pi_div_im
    {z : ℂ} (hz : 0 < z.re) (hzIm : 0 < z.im) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ≤
      Real.pi / (16 * z.im) := by
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le
    (integrableOn_heightTenStieltjesRectangularMajorant hzIm.ne') (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_deBruijnNewmanPolymathStieltjesIntegrand_le_rectangular
        hz hzIm.ne' ht.le)
  rw [deBruijnNewmanPolymathStieltjesLogRemainder]
  exact hnorm.trans_eq (integral_heightTenStieltjesRectangularMajorant_Ioi hzIm)

theorem norm_heightTenStieltjesLogRemainder_halfCritical_le_oneSixteenth
    {y : ℝ} (hy : 13 / 2 ≤ y) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint y / 2)‖ ≤ 1 / 16 := by
  let z := heightTenRiemannSiegelCriticalPoint y / 2
  have hzRe : z.re = 1 / 4 := by norm_num [z]
  have hzIm : z.im = y / 2 := by norm_num [z]
  have hzImPos : 0 < z.im := by rw [hzIm]; linarith
  have h := norm_deBruijnNewmanPolymathStieltjesLogRemainder_le_pi_div_im
    (z := z) (by rw [hzRe]; norm_num) hzImPos
  rw [hzIm] at h
  apply h.trans
  have hpi : Real.pi < 13 / 4 := Real.pi_lt_d2.trans (by norm_num)
  have hyHalf : 13 / 4 ≤ y / 2 := by linarith
  have hden : 0 < 16 * (y / 2) := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

end

end LeanLab.Riemann
