import LeanLab.Riemann.HardyLittlewoodLinearCount
import LeanLab.Riemann.DeBruijnNewmanPolymathStieltjesScaledGamma
import LeanLab.Riemann.HardyComplexAlpha

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy--Littlewood's source normalization and eta lower estimate

This module constructs a globally positive extension of the real coordinate used by
Hardy--Littlewood (1921). On the source range it has the literal positive-height normalization.
The explicit H6 Stirling remainder supplies a concrete comparison with zeta and eta, which is
then integrated into the absolute-window lower premise consumed by the finite count bridge.

The eta primitive-series identification and both source second-moment estimates remain open.
-/

open Complex MeasureTheory Real Set

namespace LeanLab.Riemann

noncomputable section

def hardyLittlewoodGammaPoint (t : ℝ) : ℂ :=
  (1 / 4 : ℂ) + (t / 2 : ℝ) * Complex.I

@[simp] theorem hardyLittlewoodGammaPoint_re (t : ℝ) :
    (hardyLittlewoodGammaPoint t).re = 1 / 4 := by
  simp [hardyLittlewoodGammaPoint]

@[simp] theorem hardyLittlewoodGammaPoint_im (t : ℝ) :
    (hardyLittlewoodGammaPoint t).im = t / 2 := by
  simp [hardyLittlewoodGammaPoint]

theorem norm_hardyLittlewoodGammaMain (t : ℝ) :
    ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ =
      Real.sqrt (2 * Real.pi) *
        Real.exp
          ((-1 / 4 : ℝ) * Real.log ‖hardyLittlewoodGammaPoint t‖ -
            (t / 2) * Complex.arg (hardyLittlewoodGammaPoint t) - 1 / 4) := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  rw [deBruijnNewmanPolymathGammaStirlingMain, norm_mul,
    Complex.norm_exp]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt]
  congr 1
  congr 1
  simp only [sub_re, mul_re, Complex.log_re, Complex.log_im, hardyLittlewoodGammaPoint_re]
  norm_num [hardyLittlewoodGammaPoint]

theorem hardyLittlewoodGammaMain_lower {t : ℝ} (ht : 8 ≤ t) :
    Real.sqrt (2 * Real.pi) *
        Real.exp
          ((-1 / 4 : ℝ) * Real.log t -
            Real.pi * t / 4 - 1 / 4) ≤
      ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ := by
  have htPos : 0 < t := by linarith
  have hzNe : hardyLittlewoodGammaPoint t ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    norm_num [hardyLittlewoodGammaPoint] at hre
  have hzNormPos : 0 < ‖hardyLittlewoodGammaPoint t‖ := norm_pos_iff.mpr hzNe
  have hzNormLe : ‖hardyLittlewoodGammaPoint t‖ ≤ t := by
    calc
      ‖hardyLittlewoodGammaPoint t‖ ≤ |(hardyLittlewoodGammaPoint t).re| + |(hardyLittlewoodGammaPoint t).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = 1 / 4 + t / 2 := by
        rw [hardyLittlewoodGammaPoint_re, hardyLittlewoodGammaPoint_im, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
      _ ≤ t := by linarith
  have hlog :
      Real.log ‖hardyLittlewoodGammaPoint t‖ ≤ Real.log t :=
    Real.strictMonoOn_log.monotoneOn hzNormPos htPos hzNormLe
  have harg : Complex.arg (hardyLittlewoodGammaPoint t) ≤ Real.pi / 2 :=
    Complex.arg_le_pi_div_two_iff.mpr (Or.inl (by norm_num [hardyLittlewoodGammaPoint]))
  have hargMul :
      (t / 2) * Complex.arg (hardyLittlewoodGammaPoint t) ≤
        (t / 2) * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left harg (by positivity)
  have hexponent :
      (-1 / 4 : ℝ) * Real.log t - Real.pi * t / 4 - 1 / 4 ≤
        (-1 / 4 : ℝ) * Real.log ‖hardyLittlewoodGammaPoint t‖ -
          (t / 2) * Complex.arg (hardyLittlewoodGammaPoint t) - 1 / 4 := by
    nlinarith
  rw [norm_hardyLittlewoodGammaMain]
  gcongr

theorem hardyLittlewoodGamma_lower {t : ℝ} (ht : 8 ≤ t) :
    (1 / 2 : ℝ) *
        ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ ≤
      ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ := by
  have htPos : 0 < t := by linarith
  have hzNormFour : 4 ≤ ‖hardyLittlewoodGammaPoint t‖ := by
    calc
      4 ≤ |(hardyLittlewoodGammaPoint t).im| := by
        rw [hardyLittlewoodGammaPoint_im, abs_of_nonneg (by positivity)]
        linarith
      _ ≤ ‖hardyLittlewoodGammaPoint t‖ := Complex.abs_im_le_norm _
  have hzNormOne : 1 ≤ ‖hardyLittlewoodGammaPoint t‖ := by linarith
  have hzRe : 0 < (hardyLittlewoodGammaPoint t).re := by norm_num [hardyLittlewoodGammaPoint]
  have hR2 :=
    deBruijnNewmanPolymathGammaStirlingR2_norm_le_three hzRe hzNormOne
  let e : ℂ :=
    1 / (12 * hardyLittlewoodGammaPoint t) +
      deBruijnNewmanPolymathGammaStirlingR2 (hardyLittlewoodGammaPoint t)
  have he :
      ‖e‖ ≤ 1 / 2 := by
    have hzNormPos : 0 < ‖hardyLittlewoodGammaPoint t‖ := lt_of_lt_of_le (by norm_num) hzNormFour
    have hfirst :
        ‖(1 : ℂ) / (12 * hardyLittlewoodGammaPoint t)‖ =
          1 / (12 * ‖hardyLittlewoodGammaPoint t‖) := by
      rw [norm_div, norm_one, norm_mul]
      norm_num
    calc
      ‖e‖ ≤ ‖(1 : ℂ) / (12 * hardyLittlewoodGammaPoint t)‖ +
          ‖deBruijnNewmanPolymathGammaStirlingR2 (hardyLittlewoodGammaPoint t)‖ := by
        dsimp [e]
        exact norm_add_le _ _
      _ = 1 / (12 * ‖hardyLittlewoodGammaPoint t‖) +
          ‖deBruijnNewmanPolymathGammaStirlingR2 (hardyLittlewoodGammaPoint t)‖ := by
        rw [hfirst]
      _ ≤ 1 / (12 * ‖hardyLittlewoodGammaPoint t‖) + 3 / ‖hardyLittlewoodGammaPoint t‖ ^ 2 := by
        gcongr
      _ ≤ 1 / 2 := by
        have hfirstLe :
            1 / (12 * ‖hardyLittlewoodGammaPoint t‖) ≤ 1 / 48 := by
          apply one_div_le_one_div_of_le
          · norm_num
          · nlinarith
        have hsecondLe :
            3 / ‖hardyLittlewoodGammaPoint t‖ ^ 2 ≤ 3 / 16 := by
          gcongr
          nlinarith [sq_nonneg (‖hardyLittlewoodGammaPoint t‖ - 4)]
        linarith
  have hratio :
      Complex.Gamma (hardyLittlewoodGammaPoint t) /
          deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t) =
        1 + e := by
    dsimp [e, deBruijnNewmanPolymathGammaStirlingR2]
    ring_nf
  have hratioNorm : 1 / 2 ≤
      ‖Complex.Gamma (hardyLittlewoodGammaPoint t) /
        deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ := by
    rw [hratio]
    have htri :
        ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) + e‖ + ‖-e‖ := by
      calc
        ‖(1 : ℂ)‖ = ‖((1 : ℂ) + e) + (-e)‖ := by
          congr 1
          ring_nf
        _ ≤ ‖(1 : ℂ) + e‖ + ‖-e‖ := norm_add_le _ _
    simp only [norm_one, norm_neg] at htri
    linarith
  have hmainNe :
      deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t) ≠ 0 :=
    deBruijnNewmanPolymathGammaStirlingMain_ne_zero _
  calc
    (1 / 2 : ℝ) *
          ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖
        ≤ ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ *
            ‖Complex.Gamma (hardyLittlewoodGammaPoint t) /
              deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hratioNorm (norm_nonneg _)
    _ = ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ := by
      rw [← norm_mul]
      congr 1
      field_simp

def hardyLittlewoodRawSourceWeight (t : ℝ) : ℝ :=
  |t| ^ (1 / 4 : ℝ) * Real.exp (Real.pi * |t| / 4) /
    (t ^ 2 + 1 / 4)

@[simp] theorem hardyLittlewoodRawSourceWeight_zero :
    hardyLittlewoodRawSourceWeight 0 = 0 := by
  norm_num [hardyLittlewoodRawSourceWeight]

def hardyLittlewoodSourceRadius (t : ℝ) : ℝ :=
  max |t| 1

def hardyLittlewoodSourceWeight (t : ℝ) : ℝ :=
  hardyLittlewoodSourceRadius t ^ (1 / 4 : ℝ) *
    Real.exp (Real.pi * hardyLittlewoodSourceRadius t / 4) /
      (t ^ 2 + 1 / 4)

def hardyLittlewoodSourceX (t : ℝ) : ℝ :=
  -hardyLittlewoodSourceWeight t * hardyXi t

theorem hardyLittlewoodSourceRadius_pos (t : ℝ) :
    0 < hardyLittlewoodSourceRadius t := by
  unfold hardyLittlewoodSourceRadius
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem hardyLittlewoodSourceRadius_eq {t : ℝ} (ht : 1 ≤ t) :
    hardyLittlewoodSourceRadius t = t := by
  unfold hardyLittlewoodSourceRadius
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  rw [abs_of_nonneg ht0, max_eq_left ht]

theorem hardyLittlewoodSourceWeight_eq_rawWeight {t : ℝ} (ht : 1 ≤ t) :
    hardyLittlewoodSourceWeight t = hardyLittlewoodRawSourceWeight t := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  rw [hardyLittlewoodSourceWeight, hardyLittlewoodRawSourceWeight, hardyLittlewoodSourceRadius_eq ht,
    abs_of_nonneg ht0]

theorem continuous_hardyLittlewoodSourceRadius :
    Continuous hardyLittlewoodSourceRadius := by
  exact continuous_abs.max continuous_const

theorem continuous_hardyLittlewoodSourceWeight :
    Continuous hardyLittlewoodSourceWeight := by
  unfold hardyLittlewoodSourceWeight
  apply Continuous.div₀
  · apply Continuous.mul
    · exact continuous_hardyLittlewoodSourceRadius.rpow_const
        (fun t => Or.inl (hardyLittlewoodSourceRadius_pos t).ne')
    · exact Real.continuous_exp.comp
        ((continuous_const.mul continuous_hardyLittlewoodSourceRadius).div_const 4)
  · fun_prop
  · intro t hden
    have : 0 < t ^ 2 + 1 / 4 := by positivity
    linarith

theorem hardyLittlewoodSourceWeight_pos (t : ℝ) :
    0 < hardyLittlewoodSourceWeight t := by
  unfold hardyLittlewoodSourceWeight
  exact div_pos
    (mul_pos (Real.rpow_pos_of_pos (hardyLittlewoodSourceRadius_pos t) _)
      (Real.exp_pos _))
    (by positivity)

theorem continuous_hardyLittlewoodSourceX :
    Continuous hardyLittlewoodSourceX := by
  unfold hardyLittlewoodSourceX
  exact continuous_hardyLittlewoodSourceWeight.neg.mul continuous_hardyXi

theorem hardyLittlewoodSourceX_zero_iff (t : ℝ) :
    hardyLittlewoodSourceX t = 0 ↔ hardyXi t = 0 := by
  unfold hardyLittlewoodSourceX
  rw [mul_eq_zero]
  simp [(hardyLittlewoodSourceWeight_pos t).ne']

theorem hardyLittlewoodSourceCoordinate :
    HardyLittlewoodZeroCoordinate hardyLittlewoodSourceX where
  continuous := continuous_hardyLittlewoodSourceX
  zero_iff := fun t => by
    rw [hardyLittlewoodSourceX_zero_iff, hardyXi_eq_zero_iff_isNontrivialZero]

theorem norm_hardyXi_source_factor {t : ℝ} (ht : 0 < t) :
    |hardyXi t| =
      (t ^ 2 + 1 / 4) / 2 *
        Real.pi ^ (-1 / 4 : ℝ) *
          ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ *
            ‖riemannZeta (hardyCriticalLinePoint t)‖ := by
  let s := hardyCriticalLinePoint t
  have hsPos : 0 < s.re := by simp [s]
  have hsOne : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s, ht.ne'] at him
  have hfactor :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos hsPos hsOne
  have hcoord :
      ((hardyXi t : ℝ) : ℂ) = riemannXi s := by
    rw [← hardyCriticalXi_eq_ofReal]
    rfl
  have hsMul :
      s * (s - 1) = -((t ^ 2 + 1 / 4 : ℝ) : ℂ) := by
    dsimp [s, hardyCriticalLinePoint]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  have hsHalf :
      s / 2 = hardyLittlewoodGammaPoint t := by
    dsimp [s, hardyCriticalLinePoint, hardyLittlewoodGammaPoint]
    push_cast
    ring_nf
  calc
    |hardyXi t| = ‖riemannXi s‖ := by
      rw [← hcoord]
      simp
    _ = ‖s * (s - 1) / 2‖ * ‖Complex.Gammaℝ s‖ *
          ‖riemannZeta s‖ := by
      rw [hfactor]
      simp only [norm_mul]
    _ = (t ^ 2 + 1 / 4) / 2 *
          Real.pi ^ (-1 / 4 : ℝ) *
            ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ *
              ‖riemannZeta s‖ := by
      rw [Complex.Gammaℝ_def, norm_mul, hsHalf,
        Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      have hpiRe : (-s / 2).re = -(1 / 4 : ℝ) := by
        norm_num [s, hardyCriticalLinePoint]
      rw [hpiRe, hsMul, norm_div, norm_neg, Complex.norm_real]
      rw [Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < t ^ 2 + 1 / 4)]
      have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hnormTwo]
      ring_nf

theorem abs_hardyLittlewoodSourceX_eq {t : ℝ} (ht : 1 ≤ t) :
    |hardyLittlewoodSourceX t| =
      (1 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
        t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
          ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ *
            ‖riemannZeta (hardyCriticalLinePoint t)‖ := by
  have htPos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hdenPos : 0 < t ^ 2 + 1 / 4 := by positivity
  rw [hardyLittlewoodSourceX, abs_mul, abs_neg, abs_of_pos (hardyLittlewoodSourceWeight_pos t),
    norm_hardyXi_source_factor htPos]
  unfold hardyLittlewoodSourceWeight
  rw [hardyLittlewoodSourceRadius_eq ht]
  field_simp [hdenPos.ne']

theorem hardyLittlewood_normalizedGammaMain_lower {t : ℝ} (ht : 8 ≤ t) :
    Real.sqrt (2 * Real.pi) * Real.exp (-1 / 4) ≤
      t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
        ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ := by
  have htPos : 0 < t := by linarith
  have hnonneg :
      0 ≤ t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) := by
    positivity
  have h := mul_le_mul_of_nonneg_left (hardyLittlewoodGammaMain_lower ht) hnonneg
  calc
    Real.sqrt (2 * Real.pi) * Real.exp (-1 / 4) =
        (t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4)) *
          (Real.sqrt (2 * Real.pi) *
            Real.exp
              ((-1 / 4 : ℝ) * Real.log t -
                Real.pi * t / 4 - 1 / 4)) := by
      rw [Real.rpow_def_of_pos htPos]
      rw [show
        Real.exp (Real.log t * (1 / 4)) *
              Real.exp (Real.pi * t / 4) *
              (Real.sqrt (2 * Real.pi) *
                Real.exp
                  ((-1 / 4 : ℝ) * Real.log t -
                    Real.pi * t / 4 - 1 / 4)) =
            Real.sqrt (2 * Real.pi) *
              (Real.exp (Real.log t * (1 / 4)) *
                Real.exp (Real.pi * t / 4) *
                  Real.exp
                    ((-1 / 4 : ℝ) * Real.log t -
                    Real.pi * t / 4 - 1 / 4)) by ring_nf]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring_nf
    _ ≤ (t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4)) *
          ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ := h
    _ = t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
          ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖ := rfl

def hardyLittlewoodZetaLowerConstant : ℝ :=
  Real.pi ^ (-1 / 4 : ℝ) *
    (Real.sqrt (2 * Real.pi) * Real.exp (-1 / 4)) / 4

theorem hardyLittlewoodZetaLowerConstant_pos :
    0 < hardyLittlewoodZetaLowerConstant := by
  unfold hardyLittlewoodZetaLowerConstant
  positivity

theorem hardyLittlewood_zeta_lower {t : ℝ} (ht : 8 ≤ t) :
    hardyLittlewoodZetaLowerConstant *
        ‖riemannZeta (hardyCriticalLinePoint t)‖ ≤
      |hardyLittlewoodSourceX t| := by
  have htOne : 1 ≤ t := by linarith
  rw [abs_hardyLittlewoodSourceX_eq htOne]
  have hgamma := hardyLittlewoodGamma_lower ht
  have hmain := hardyLittlewood_normalizedGammaMain_lower ht
  let Znorm := ‖riemannZeta (hardyCriticalLinePoint t)‖
  have hgammaScaled :
      (1 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
          ((1 / 2 : ℝ) *
            ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖) *
          Znorm ≤
        (1 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
          ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ * Znorm := by
    gcongr
  have hmainScaled :
      (1 / 4 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          (Real.sqrt (2 * Real.pi) * Real.exp (-1 / 4)) * Znorm ≤
        (1 / 4 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          (t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
            ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖) *
          Znorm := by
    gcongr
  have hfirst :
      hardyLittlewoodZetaLowerConstant * Znorm ≤
        (1 / 4 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          (t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
            ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖) *
          Znorm := by
    calc
      hardyLittlewoodZetaLowerConstant * Znorm =
          (1 / 4 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
            (Real.sqrt (2 * Real.pi) * Real.exp (-1 / 4)) * Znorm := by
        unfold hardyLittlewoodZetaLowerConstant
        ring_nf
      _ ≤ _ := hmainScaled
  have hsecond :
      (1 / 4 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          (t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
            ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖) *
          Znorm ≤
        (1 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
          t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
          ‖Complex.Gamma (hardyLittlewoodGammaPoint t)‖ * Znorm := by
    calc
      (1 / 4 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
            (t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
              ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖) *
            Znorm =
          (1 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ) *
            t ^ (1 / 4 : ℝ) * Real.exp (Real.pi * t / 4) *
            ((1 / 2 : ℝ) *
              ‖deBruijnNewmanPolymathGammaStirlingMain (hardyLittlewoodGammaPoint t)‖) *
            Znorm := by ring_nf
      _ ≤ _ := hgammaScaled
  exact hfirst.trans hsecond

def hardyLittlewoodEta (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

def hardyLittlewoodEtaCritical (t : ℝ) : ℂ :=
  hardyLittlewoodEta (hardyCriticalLinePoint t)

theorem continuous_hardyLittlewoodEtaCritical :
    Continuous hardyLittlewoodEtaCritical := by
  unfold hardyLittlewoodEtaCritical hardyLittlewoodEta
  apply Continuous.mul
  · apply Continuous.sub continuous_const
    have hpow : Continuous (fun z : ℂ => (2 : ℂ) ^ z) :=
      continuous_iff_continuousAt.mpr fun _ =>
        continuousAt_const_cpow (by norm_num)
    exact hpow.comp (continuous_const.sub continuous_hardyCriticalLinePoint)
  · rw [continuous_iff_continuousAt]
    intro t
    have hne : hardyCriticalLinePoint t ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [hardyCriticalLinePoint] at hre
    exact (differentiableAt_riemannZeta hne).continuousAt.comp
      continuous_hardyCriticalLinePoint.continuousAt

theorem norm_hardyLittlewoodEtaCritical_le (t : ℝ) :
    ‖hardyLittlewoodEtaCritical t‖ ≤
      3 * ‖riemannZeta (hardyCriticalLinePoint t)‖ := by
  have hpowNorm :
      ‖(2 : ℂ) ^ (1 - hardyCriticalLinePoint t)‖ =
        (2 : ℝ) ^ (1 / 2 : ℝ) := by
    have hnorm :=
      Complex.norm_cpow_eq_rpow_re_of_pos
        (x := 2) (by norm_num : (0 : ℝ) < 2)
        (1 - hardyCriticalLinePoint t)
    calc
      ‖(2 : ℂ) ^ (1 - hardyCriticalLinePoint t)‖ =
          (2 : ℝ) ^ (1 - hardyCriticalLinePoint t).re := by
            simpa using hnorm
      _ = (2 : ℝ) ^ (1 / 2 : ℝ) := by
        congr 1
        norm_num [hardyCriticalLinePoint]
  have hpowLe :
      (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    calc
      (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  unfold hardyLittlewoodEtaCritical hardyLittlewoodEta
  rw [norm_mul]
  calc
    ‖(1 : ℂ) - (2 : ℂ) ^ (1 - hardyCriticalLinePoint t)‖ *
          ‖riemannZeta (hardyCriticalLinePoint t)‖
        ≤ (‖(1 : ℂ)‖ +
            ‖(2 : ℂ) ^ (1 - hardyCriticalLinePoint t)‖) *
          ‖riemannZeta (hardyCriticalLinePoint t)‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (1 + 2) * ‖riemannZeta (hardyCriticalLinePoint t)‖ := by
      rw [norm_one]
      gcongr
      rw [hpowNorm]
      exact hpowLe
    _ = 3 * ‖riemannZeta (hardyCriticalLinePoint t)‖ := by ring_nf

def hardyLittlewoodEtaLowerConstant : ℝ :=
  hardyLittlewoodZetaLowerConstant / 3

theorem hardyLittlewoodEtaLowerConstant_pos :
    0 < hardyLittlewoodEtaLowerConstant := by
  unfold hardyLittlewoodEtaLowerConstant
  exact div_pos hardyLittlewoodZetaLowerConstant_pos (by norm_num)

theorem hardyLittlewood_eta_lower {t : ℝ} (ht : 8 ≤ t) :
    hardyLittlewoodEtaLowerConstant * ‖hardyLittlewoodEtaCritical t‖ ≤
      |hardyLittlewoodSourceX t| := by
  calc
    hardyLittlewoodEtaLowerConstant * ‖hardyLittlewoodEtaCritical t‖ ≤
        hardyLittlewoodEtaLowerConstant *
          (3 * ‖riemannZeta (hardyCriticalLinePoint t)‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_hardyLittlewoodEtaCritical_le t) hardyLittlewoodEtaLowerConstant_pos.le
    _ = hardyLittlewoodZetaLowerConstant *
          ‖riemannZeta (hardyCriticalLinePoint t)‖ := by
      unfold hardyLittlewoodEtaLowerConstant
      ring_nf
    _ ≤ |hardyLittlewoodSourceX t| := hardyLittlewood_zeta_lower ht

def hardyLittlewoodEtaReal (t : ℝ) : ℝ :=
  (hardyLittlewoodEtaCritical t).re

def hardyLittlewoodEtaPrimitive (t : ℝ) : ℝ :=
  ∫ u in 0..t, hardyLittlewoodEtaReal u - 1

def hardyLittlewoodEtaWindowError (H t : ℝ) : ℝ :=
  hardyLittlewoodEtaLowerConstant *
    (hardyLittlewoodEtaPrimitive (t + H) - hardyLittlewoodEtaPrimitive t)

theorem continuous_hardyLittlewoodEtaReal :
    Continuous hardyLittlewoodEtaReal :=
  Complex.continuous_re.comp continuous_hardyLittlewoodEtaCritical

theorem continuous_hardyLittlewoodEtaPrimitive :
    Continuous hardyLittlewoodEtaPrimitive :=
  intervalIntegral.continuous_primitive
    (fun a b => (continuous_hardyLittlewoodEtaReal.sub continuous_const).intervalIntegrable a b) 0

theorem continuous_hardyLittlewoodEtaWindowError (H : ℝ) :
    Continuous (hardyLittlewoodEtaWindowError H) := by
  unfold hardyLittlewoodEtaWindowError
  exact continuous_const.mul
    ((continuous_hardyLittlewoodEtaPrimitive.comp
      (continuous_id.add continuous_const)).sub continuous_hardyLittlewoodEtaPrimitive)

theorem integral_hardyLittlewoodEtaReal_eq
    (t H : ℝ) :
    (∫ u in t..t + H, hardyLittlewoodEtaReal u) =
      H + hardyLittlewoodEtaPrimitive (t + H) - hardyLittlewoodEtaPrimitive t := by
  have hzeroToT :
      IntervalIntegrable (fun u : ℝ => hardyLittlewoodEtaReal u - (1 : ℝ))
        volume 0 t :=
    (continuous_hardyLittlewoodEtaReal.sub continuous_const).intervalIntegrable
      (μ := volume) 0 t
  have hTToEnd :
      IntervalIntegrable (fun u : ℝ => hardyLittlewoodEtaReal u - (1 : ℝ))
        volume t (t + H) :=
    (continuous_hardyLittlewoodEtaReal.sub continuous_const).intervalIntegrable
      (μ := volume) t (t + H)
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hzeroToT hTToEnd
  have hsub :
      (∫ u in t..t + H, hardyLittlewoodEtaReal u - 1) =
        hardyLittlewoodEtaPrimitive (t + H) - hardyLittlewoodEtaPrimitive t := by
    unfold hardyLittlewoodEtaPrimitive
    linarith
  have heta :
      IntervalIntegrable hardyLittlewoodEtaReal volume t (t + H) :=
    continuous_hardyLittlewoodEtaReal.intervalIntegrable t (t + H)
  have hone :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume t (t + H) :=
    continuous_const.intervalIntegrable t (t + H)
  rw [intervalIntegral.integral_sub heta hone] at hsub
  rw [intervalIntegral.integral_const] at hsub
  simp only [smul_eq_mul] at hsub
  linarith

theorem hardyLittlewood_eta_interval_lower
    {t H : ℝ} (ht : 8 ≤ t) (hH : 0 ≤ H) :
    hardyLittlewoodEtaLowerConstant * H - |hardyLittlewoodEtaWindowError H t| ≤
      hardyLittlewoodAbsWindowIntegral hardyLittlewoodSourceX H t := by
  have hpointwise :
      ∀ u ∈ Set.Icc t (t + H),
        hardyLittlewoodEtaLowerConstant * hardyLittlewoodEtaReal u ≤ |hardyLittlewoodSourceX u| := by
    intro u hu
    have hu8 : 8 ≤ u := le_trans ht hu.1
    calc
      hardyLittlewoodEtaLowerConstant * hardyLittlewoodEtaReal u ≤
          hardyLittlewoodEtaLowerConstant * ‖hardyLittlewoodEtaCritical u‖ := by
        apply mul_le_mul_of_nonneg_left
        · exact Complex.re_le_norm _
        · exact hardyLittlewoodEtaLowerConstant_pos.le
      _ ≤ |hardyLittlewoodSourceX u| := hardyLittlewood_eta_lower hu8
  have hleft :
      IntervalIntegrable
        (fun u : ℝ => hardyLittlewoodEtaLowerConstant * hardyLittlewoodEtaReal u)
        volume t (t + H) :=
    (continuous_const.mul continuous_hardyLittlewoodEtaReal).intervalIntegrable
      t (t + H)
  have hright :
      IntervalIntegrable (fun u : ℝ => |hardyLittlewoodSourceX u|)
        volume t (t + H) :=
    continuous_hardyLittlewoodSourceX.abs.intervalIntegrable t (t + H)
  have hmono :
      (∫ u in t..t + H,
          hardyLittlewoodEtaLowerConstant * hardyLittlewoodEtaReal u) ≤
        hardyLittlewoodAbsWindowIntegral hardyLittlewoodSourceX H t := by
    unfold hardyLittlewoodAbsWindowIntegral
    exact intervalIntegral.integral_mono_on (by linarith) hleft hright hpointwise
  have hmain :
      (∫ u in t..t + H,
          hardyLittlewoodEtaLowerConstant * hardyLittlewoodEtaReal u) =
        hardyLittlewoodEtaLowerConstant * H + hardyLittlewoodEtaWindowError H t := by
    rw [intervalIntegral.integral_const_mul]
    rw [integral_hardyLittlewoodEtaReal_eq]
    unfold hardyLittlewoodEtaWindowError
    ring_nf
  calc
    hardyLittlewoodEtaLowerConstant * H - |hardyLittlewoodEtaWindowError H t| ≤
        hardyLittlewoodEtaLowerConstant * H + hardyLittlewoodEtaWindowError H t := by
      linarith [neg_abs_le (hardyLittlewoodEtaWindowError H t)]
    _ = (∫ u in t..t + H,
          hardyLittlewoodEtaLowerConstant * hardyLittlewoodEtaReal u) := hmain.symm
    _ ≤ hardyLittlewoodAbsWindowIntegral hardyLittlewoodSourceX H t := hmono

theorem hardyLittlewood_eta_lower_on_source_range
    {T H : ℝ} (hT : 8 ≤ T) (hH : 0 ≤ H) :
    ∀ t ∈ Set.Icc T (2 * T),
      t ∉ hardyLittlewoodBadSet
        hardyLittlewoodSourceX (hardyLittlewoodEtaWindowError H) H
          (hardyLittlewoodEtaLowerConstant * H / 2) →
      hardyLittlewoodEtaLowerConstant * H -
          |hardyLittlewoodEtaWindowError H t| ≤
        hardyLittlewoodAbsWindowIntegral hardyLittlewoodSourceX H t := by
  intro t ht _
  exact hardyLittlewood_eta_interval_lower (le_trans hT ht.1) hH

structure HardyLittlewoodSourceNormalizationCertificate : Prop where
  coordinate : HardyLittlewoodZeroCoordinate hardyLittlewoodSourceX
  sourceRange :
    ∀ {t : ℝ}, 1 ≤ t → hardyLittlewoodSourceWeight t = hardyLittlewoodRawSourceWeight t
  zetaLower :
    ∀ {t : ℝ}, 8 ≤ t →
      hardyLittlewoodZetaLowerConstant *
          ‖riemannZeta (hardyCriticalLinePoint t)‖ ≤ |hardyLittlewoodSourceX t|
  etaLower :
    ∀ {t : ℝ}, 8 ≤ t →
      hardyLittlewoodEtaLowerConstant * ‖hardyLittlewoodEtaCritical t‖ ≤ |hardyLittlewoodSourceX t|
  primitiveIdentity :
    ∀ t H,
      (∫ u in t..t + H, hardyLittlewoodEtaReal u) =
        H + hardyLittlewoodEtaPrimitive (t + H) - hardyLittlewoodEtaPrimitive t
  windowLower :
    ∀ {t H : ℝ}, 8 ≤ t → 0 ≤ H →
      hardyLittlewoodEtaLowerConstant * H - |hardyLittlewoodEtaWindowError H t| ≤
        hardyLittlewoodAbsWindowIntegral hardyLittlewoodSourceX H t
  sourceRangeLower :
    ∀ {T H : ℝ}, 8 ≤ T → 0 ≤ H →
      ∀ t ∈ Set.Icc T (2 * T),
        t ∉ hardyLittlewoodBadSet
          hardyLittlewoodSourceX (hardyLittlewoodEtaWindowError H) H
            (hardyLittlewoodEtaLowerConstant * H / 2) →
        hardyLittlewoodEtaLowerConstant * H -
            |hardyLittlewoodEtaWindowError H t| ≤
          hardyLittlewoodAbsWindowIntegral hardyLittlewoodSourceX H t
  rawWeightAtZero : hardyLittlewoodRawSourceWeight 0 = 0

theorem hardyLittlewoodSourceNormalization_endpoint :
    HardyLittlewoodSourceNormalizationCertificate where
  coordinate := hardyLittlewoodSourceCoordinate
  sourceRange := hardyLittlewoodSourceWeight_eq_rawWeight
  zetaLower := hardyLittlewood_zeta_lower
  etaLower := hardyLittlewood_eta_lower
  primitiveIdentity := integral_hardyLittlewoodEtaReal_eq
  windowLower := hardyLittlewood_eta_interval_lower
  sourceRangeLower := hardyLittlewood_eta_lower_on_source_range
  rawWeightAtZero := hardyLittlewoodRawSourceWeight_zero

end

end LeanLab.Riemann
