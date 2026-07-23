import LeanLab.Riemann.BettinGonekAuxiliary
import LeanLab.Riemann.BettinGonekMellinIdentity
import LeanLab.Riemann.DeBruijnNewmanPolymathBoydBoundaryDispersion
import LeanLab.Riemann.TruncatedPerron
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Asymptotics

set_option linter.style.header false

/-!
# Bettin--Gonek's rational J-contour

This module formalizes equations (2.3)--(2.5) of Bettin--Gonek. The already compiled actual
mollifier Mellin transform and regularized auxiliary factor cancel to the literal rational
one-pole kernel. Finite rectangles then give the infinite contour shift, a boundary-line bound
uniform in the source scale `x`, and the exact selected-zero residue growth.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Set Topology
open scoped Interval Topology

noncomputable section

/-- The normalized `1/(2*pi*i)` vertical integral, parameterized by ordinate. -/
def bettinGonekJLineIntegral (rho : ℂ) (t x sigma : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) *
    ∫ y : ℝ, bettinGonekJKernel rho t x (sigma + y * Complex.I)

/-- The positive constant multiplying the selected-zero power in the residue norm. -/
def bettinGonekResidueScale (rho : ℂ) (t : ℝ) : ℝ :=
  ‖rho - 1‖ /
    (‖rho + 3 / 2 - t * Complex.I‖ ^ 2 * ‖rho + 3 / 2‖ ^ 4)

theorem bettinGonekAuxiliary_mul_H_eq_JKernel
    {rho w : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) (x : ℝ)
    (hw : 3 / 2 < w.re) :
    bettinGonekAuxiliaryG rho t w * bettinGonekH t w * (x : ℂ) ^ w =
      bettinGonekJKernel rho t x w := by
  have hargRho : bettinGonekShiftedArgument t w ≠ rho := by
    intro h
    have hre := congrArg Complex.re h
    have hrho_lt : rho.re < 1 := nontrivial_zero_re_lt_one hrho
    norm_num [bettinGonekShiftedArgument, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hargOne : bettinGonekShiftedArgument t w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [bettinGonekShiftedArgument, Complex.add_re, Complex.mul_re] at hre
    linarith
  have hwOne : w - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hwAddOne : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hwAddItOne : w + t * Complex.I + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hwPole : w - (rho + 1 / 2 - t * Complex.I) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hrho_lt : rho.re < 1 := nontrivial_zero_re_lt_one hrho
    norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re] at hre
    linarith
  have hzeta : riemannZeta (w - 1 / 2 + t * Complex.I) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hshiftOne :
      w - 1 / 2 + t * Complex.I - 1 = w - 3 / 2 + t * Complex.I := by
    ring
  have hshiftRho :
      w - 1 / 2 + t * Complex.I - rho =
        w - (rho + 1 / 2 - t * Complex.I) := by
    ring
  have hA : (w - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hwOne
  have hD : (w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hwAddOne) (pow_ne_zero 4 hwAddItOne)
  have hcancel {A N Z B D X : ℂ}
      (hA : A ≠ 0) (hZ : Z ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) :
      A * (N * Z / B) / D * (1 / (A * Z)) * X = N * X / (B * D) := by
    field_simp [hA, hZ, hB, hD]
  rw [bettinGonekAuxiliaryG_eq_raw hrho t hargRho hargOne,
    bettinGonekAuxiliaryGRaw, bettinGonekH_eq t hw, bettinGonekJKernel,
    bettinGonekShiftedArgument, bettinGonekSelectedPole]
  rw [hshiftOne, hshiftRho]
  exact hcancel hA hzeta hwPole hD

theorem bettinGonekResidueScale_pos
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) :
    0 < bettinGonekResidueScale rho t := by
  rw [bettinGonekResidueScale]
  apply div_pos
  · exact norm_pos_iff.mpr (sub_ne_zero.mpr hrho.2.2)
  · have hrhoAdd : rho + 3 / 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith [nontrivial_zero_re_pos hrho]
    have hrhoAddSub : rho + 3 / 2 - t * Complex.I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.sub_re, Complex.mul_re] at hre
      linarith [nontrivial_zero_re_pos hrho]
    exact mul_pos (pow_pos (norm_pos_iff.mpr hrhoAddSub) 2)
      (pow_pos (norm_pos_iff.mpr hrhoAdd) 4)

theorem norm_bettinGonekResidueCoefficient
    (rho : ℂ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖bettinGonekResidueCoefficient rho t x‖ =
      bettinGonekResidueScale rho t * x ^ (rho.re + 1 / 2) := by
  have hpoleRe : (bettinGonekSelectedPole rho t).re = rho.re + 1 / 2 := by
    simp [bettinGonekSelectedPole]
  rw [bettinGonekResidueCoefficient, bettinGonekResidueScale, norm_div,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hpoleRe, norm_mul,
    norm_pow, norm_pow]
  ring

private theorem abs_re_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs,
    ← Complex.normSq_eq_norm_sq]
  simpa [pow_two] using Complex.re_sq_le_normSq z

private theorem abs_im_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _), sq_abs,
    ← Complex.normSq_eq_norm_sq]
  simpa [pow_two] using Complex.im_sq_le_normSq z

theorem norm_bettinGonekJKernel_zero_line_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    ‖bettinGonekJKernel rho t x (y * Complex.I)‖ ≤
      4 / (1 + (y + t) ^ 2) := by
  let w : ℂ := y * Complex.I
  let u : ℝ := y + t
  let Q : ℝ := 1 + u ^ 2
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hlinear : w - 3 / 2 + t * Complex.I = (-3 / 2 : ℝ) + u * Complex.I := by
    dsimp [w, u]
    push_cast
    ring
  have hnum : ‖w - 3 / 2 + t * Complex.I‖ ≤ 2 * Q := by
    rw [hlinear]
    calc
      ‖((-3 / 2 : ℝ) : ℂ) + u * Complex.I‖ ≤
          ‖((-3 / 2 : ℝ) : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 3 / 2 + |u| := by
        rw [norm_mul, norm_I]
        norm_num [Real.norm_eq_abs, abs_of_nonneg]
      _ ≤ 2 * Q := by
        have habs_sq : |u| ^ 2 = u ^ 2 := sq_abs u
        have hsquare : 0 ≤ (2 * |u| - 1) ^ 2 := sq_nonneg _
        dsimp [Q]
        nlinarith
  have hpole : 1 / 2 ≤ ‖w - bettinGonekSelectedPole rho t‖ := by
    have hre : (w - bettinGonekSelectedPole rho t).re = -(rho.re + 1 / 2) := by
      simp [w, bettinGonekSelectedPole]
    calc
      1 / 2 ≤ |(w - bettinGonekSelectedPole rho t).re| := by
        rw [hre, abs_neg, abs_of_pos]
        · linarith [nontrivial_zero_re_pos hrho]
        · linarith [nontrivial_zero_re_pos hrho]
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ := abs_re_le_norm _
  have hone : 1 ≤ ‖w + 1‖ := by
    have hre : (w + 1).re = 1 := by simp [w]
    simpa [hre] using abs_re_le_norm (w + 1)
  have hit : w + t * Complex.I + 1 = 1 + u * Complex.I := by
    dsimp [w, u]
    push_cast
    ring
  have hitSq : ‖w + t * Complex.I + 1‖ ^ 2 = Q := by
    rw [hit, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    dsimp [Q]
    ring
  have hitFourth : ‖w + t * Complex.I + 1‖ ^ 4 = Q ^ 2 := by
    calc
      ‖w + t * Complex.I + 1‖ ^ 4 =
          (‖w + t * Complex.I + 1‖ ^ 2) ^ 2 := by ring
      _ = Q ^ 2 := by rw [hitSq]
  have hdenLower :
      (1 / 2 : ℝ) * Q ^ 2 ≤
        ‖(w - bettinGonekSelectedPole rho t) *
          ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hitFourth]
    calc
      (1 / 2 : ℝ) * Q ^ 2 ≤
          ‖w - bettinGonekSelectedPole rho t‖ * Q ^ 2 :=
        mul_le_mul_of_nonneg_right hpole (sq_nonneg Q)
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ *
          (‖w + 1‖ ^ 2 * Q ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have honeSq : 1 ≤ ‖w + 1‖ ^ 2 := by
          nlinarith [hone, norm_nonneg (w + 1)]
        simpa using mul_le_mul_of_nonneg_right honeSq (sq_nonneg Q)
  have hdenPos :
      0 < ‖(w - bettinGonekSelectedPole rho t) *
        ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    have : 0 < (1 / 2 : ℝ) * Q ^ 2 := by positivity
    exact this.trans_le hdenLower
  have hnorm :
      ‖bettinGonekJKernel rho t x w‖ =
        ‖w - 3 / 2 + t * Complex.I‖ /
          ‖(w - bettinGonekSelectedPole rho t) *
            ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    rw [bettinGonekJKernel, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [w]
  change ‖bettinGonekJKernel rho t x w‖ ≤ 4 / Q
  rw [hnorm]
  apply (div_le_div_iff₀ hdenPos hQpos).2
  calc
    ‖w - 3 / 2 + t * Complex.I‖ * Q ≤ (2 * Q) * Q :=
      mul_le_mul_of_nonneg_right hnum hQpos.le
    _ = 2 * Q ^ 2 := by ring
    _ ≤ 4 * ‖(w - bettinGonekSelectedPole rho t) *
        ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
      nlinarith [hdenLower]

theorem continuous_bettinGonekJKernel_zero_line
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => bettinGonekJKernel rho t x (y * Complex.I)) := by
  have hline : Continuous (fun y : ℝ => (y : ℂ) * Complex.I) := by fun_prop
  have hpow : Continuous (fun y : ℝ => (x : ℂ) ^ ((y : ℂ) * Complex.I)) :=
    (continuous_iff_continuousAt.mpr fun _ =>
      continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx.ne')).comp hline
  simp only [bettinGonekJKernel]
  apply Continuous.div ((by fun_prop : Continuous (fun y : ℝ =>
    (y * Complex.I - 3 / 2 + t * Complex.I))) |>.mul hpow) (by fun_prop)
  intro y hzero
  rcases mul_eq_zero.mp hzero with hpole | hrest
  · have hre := congrArg Complex.re hpole
    simp [bettinGonekSelectedPole] at hre
    linarith [nontrivial_zero_re_pos hrho]
  · rcases mul_eq_zero.mp hrest with hone | hit
    · have hbase : (y : ℂ) * Complex.I + 1 = 0 := eq_zero_of_pow_eq_zero hone
      have hre := congrArg Complex.re hbase
      norm_num at hre
    · have hbase : (y : ℂ) * Complex.I + t * Complex.I + 1 = 0 :=
        eq_zero_of_pow_eq_zero hit
      have hre := congrArg Complex.re hbase
      norm_num [Complex.add_re, Complex.mul_re] at hre

theorem integrable_bettinGonekJKernel_zero_line
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => bettinGonekJKernel rho t x (y * Complex.I)) := by
  have hmajor : Integrable (fun y : ℝ => 4 / (1 + (y + t) ^ 2)) := by
    have hshift := integrable_inv_one_add_sq.comp_add_left t
    have hscaled := hshift.const_mul (4 : ℝ)
    simpa only [Function.comp_apply, add_comm, div_eq_mul_inv] using hscaled
  refine Integrable.mono' hmajor
    (continuous_bettinGonekJKernel_zero_line hrho t hx).aestronglyMeasurable ?_
  exact ae_of_all volume fun y => by
    exact norm_bettinGonekJKernel_zero_line_le hrho t hx y

theorem norm_integral_bettinGonekJKernel_zero_line_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I)‖ ≤ 4 * Real.pi := by
  have hmajor : Integrable (fun y : ℝ => 4 / (1 + (y + t) ^ 2)) := by
    have hshift := integrable_inv_one_add_sq.comp_add_left t
    have hscaled := hshift.const_mul (4 : ℝ)
    simpa only [Function.comp_apply, add_comm, div_eq_mul_inv] using hscaled
  have hbound := norm_integral_le_of_norm_le hmajor
    (ae_of_all volume fun y => norm_bettinGonekJKernel_zero_line_le hrho t hx y)
  calc
    ‖∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I)‖ ≤
        ∫ y : ℝ, 4 / (1 + (y + t) ^ 2) := hbound
    _ = 4 * ∫ y : ℝ, (1 + (y + t) ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, integral_const_mul]
    _ = 4 * ∫ y : ℝ, (1 + y ^ 2)⁻¹ := by
      congr 1
      simpa only [add_comm t] using
        (integral_add_left_eq_self t (f := fun y : ℝ => (1 + y ^ 2)⁻¹))
    _ = 4 * Real.pi := by rw [integral_univ_inv_one_add_sq]

theorem norm_bettinGonekJLineIntegral_zero_le_two
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖bettinGonekJLineIntegral rho t x 0‖ ≤ 2 := by
  rw [bettinGonekJLineIntegral]
  simp only [Complex.ofReal_zero, zero_add]
  rw [norm_mul, norm_real, Real.norm_of_nonneg (by positivity :
    0 ≤ 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I)‖ ≤
        (1 / (2 * Real.pi)) * (4 * Real.pi) :=
      mul_le_mul_of_nonneg_left
        (norm_integral_bettinGonekJKernel_zero_line_le hrho t hx) (by positivity)
    _ = 2 := by
      field_simp [Real.pi_ne_zero]
      norm_num

theorem norm_bettinGonekJKernel_three_line_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    (y : ℝ) :
    ‖bettinGonekJKernel rho t x (3 + y * Complex.I)‖ ≤
      4 * x ^ 3 / (1 + (y + t) ^ 2) := by
  let w : ℂ := 3 + y * Complex.I
  let u : ℝ := y + t
  let Q : ℝ := 1 + u ^ 2
  have hQpos : 0 < Q := by
    dsimp [Q]
    positivity
  have hlinear : w - 3 / 2 + t * Complex.I = (3 / 2 : ℝ) + u * Complex.I := by
    dsimp [w, u]
    push_cast
    ring
  have hnum : ‖w - 3 / 2 + t * Complex.I‖ ≤ 2 * Q := by
    rw [hlinear]
    calc
      ‖((3 / 2 : ℝ) : ℂ) + u * Complex.I‖ ≤
          ‖((3 / 2 : ℝ) : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = 3 / 2 + |u| := by
        rw [norm_mul, norm_I]
        norm_num [Real.norm_eq_abs, abs_of_nonneg]
      _ ≤ 2 * Q := by
        have habs_sq : |u| ^ 2 = u ^ 2 := sq_abs u
        have hsquare : 0 ≤ (2 * |u| - 1) ^ 2 := sq_nonneg _
        dsimp [Q]
        nlinarith
  have hpole : 1 ≤ ‖w - bettinGonekSelectedPole rho t‖ := by
    have hre : (w - bettinGonekSelectedPole rho t).re = 5 / 2 - rho.re := by
      simp [w, bettinGonekSelectedPole]
      ring
    calc
      1 ≤ |(w - bettinGonekSelectedPole rho t).re| := by
        rw [hre, abs_of_pos]
        · linarith [nontrivial_zero_re_lt_one hrho]
        · linarith [nontrivial_zero_re_lt_one hrho]
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ := abs_re_le_norm _
  have hone : 1 ≤ ‖w + 1‖ := by
    have hre : (w + 1).re = 4 := by norm_num [w]
    have := abs_re_le_norm (w + 1)
    rw [hre, abs_of_pos (by norm_num)] at this
    linarith
  have hit : w + t * Complex.I + 1 = 4 + u * Complex.I := by
    dsimp [w, u]
    push_cast
    ring
  have hitSq : ‖w + t * Complex.I + 1‖ ^ 2 = 16 + u ^ 2 := by
    rw [hit, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have hitSqLower : Q ≤ ‖w + t * Complex.I + 1‖ ^ 2 := by
    rw [hitSq]
    dsimp [Q]
    linarith
  have hitFourthLower : Q ^ 2 ≤ ‖w + t * Complex.I + 1‖ ^ 4 := by
    have hsquare := mul_self_le_mul_self hQpos.le hitSqLower
    nlinarith
  have hdenLower :
      Q ^ 2 ≤
        ‖(w - bettinGonekSelectedPole rho t) *
          ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc
      Q ^ 2 ≤ ‖w - bettinGonekSelectedPole rho t‖ * Q ^ 2 := by
        simpa using mul_le_mul_of_nonneg_right hpole (sq_nonneg Q)
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ *
          (‖w + 1‖ ^ 2 * Q ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have honeSq : 1 ≤ ‖w + 1‖ ^ 2 := by
          nlinarith [hone, norm_nonneg (w + 1)]
        simpa using mul_le_mul_of_nonneg_right honeSq (sq_nonneg Q)
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ *
          (‖w + 1‖ ^ 2 * ‖w + t * Complex.I + 1‖ ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hitFourthLower (sq_nonneg _)
  have hdenPos :
      0 < ‖(w - bettinGonekSelectedPole rho t) *
        ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ :=
    (sq_pos_of_pos hQpos).trans_le hdenLower
  have hnorm :
      ‖bettinGonekJKernel rho t x w‖ =
        (‖w - 3 / 2 + t * Complex.I‖ * x ^ 3) /
          ‖(w - bettinGonekSelectedPole rho t) *
            ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    rw [bettinGonekJKernel, norm_div, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [w]
  change ‖bettinGonekJKernel rho t x w‖ ≤ 4 * x ^ 3 / Q
  rw [hnorm]
  apply (div_le_div_iff₀ hdenPos hQpos).2
  calc
    (‖w - 3 / 2 + t * Complex.I‖ * x ^ 3) * Q ≤
        ((2 * Q) * x ^ 3) * Q := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnum (by positivity)) hQpos.le
    _ = 2 * x ^ 3 * Q ^ 2 := by ring
    _ ≤ 4 * x ^ 3 * Q ^ 2 := by
      have hnonneg : 0 ≤ x ^ 3 * Q ^ 2 := mul_nonneg (by positivity) (sq_nonneg Q)
      nlinarith
    _ ≤ 4 * x ^ 3 *
        ‖(w - bettinGonekSelectedPole rho t) *
          ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ :=
      mul_le_mul_of_nonneg_left hdenLower (by positivity)
    _ = (4 * x ^ 3) *
        ‖(w - bettinGonekSelectedPole rho t) *
          ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by ring

theorem continuous_bettinGonekJKernel_three_line
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => bettinGonekJKernel rho t x (3 + y * Complex.I)) := by
  have hline : Continuous (fun y : ℝ => (3 : ℂ) + (y : ℂ) * Complex.I) := by
    fun_prop
  have hpow : Continuous
      (fun y : ℝ => (x : ℂ) ^ ((3 : ℂ) + (y : ℂ) * Complex.I)) :=
    (continuous_iff_continuousAt.mpr fun _ =>
      continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx.ne')).comp hline
  simp only [bettinGonekJKernel]
  apply Continuous.div ((by fun_prop : Continuous (fun y : ℝ =>
    ((3 : ℂ) + y * Complex.I - 3 / 2 + t * Complex.I))) |>.mul hpow) (by fun_prop)
  intro y hzero
  rcases mul_eq_zero.mp hzero with hpole | hrest
  · have hre := congrArg Complex.re hpole
    simp [bettinGonekSelectedPole] at hre
    linarith [nontrivial_zero_re_lt_one hrho]
  · rcases mul_eq_zero.mp hrest with hone | hit
    · have hbase : (3 : ℂ) + y * Complex.I + 1 = 0 := eq_zero_of_pow_eq_zero hone
      have hre := congrArg Complex.re hbase
      norm_num at hre
    · have hbase : (3 : ℂ) + y * Complex.I + t * Complex.I + 1 = 0 :=
        eq_zero_of_pow_eq_zero hit
      have hre := congrArg Complex.re hbase
      norm_num [Complex.add_re, Complex.mul_re] at hre

theorem integrable_bettinGonekJKernel_three_line
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => bettinGonekJKernel rho t x (3 + y * Complex.I)) := by
  have hmajor : Integrable (fun y : ℝ => 4 * x ^ 3 / (1 + (y + t) ^ 2)) := by
    have hshift := integrable_inv_one_add_sq.comp_add_left t
    have hscaled := hshift.const_mul (4 * x ^ 3)
    simpa only [Function.comp_apply, add_comm, div_eq_mul_inv] using hscaled
  refine Integrable.mono' hmajor
    (continuous_bettinGonekJKernel_three_line hrho t hx).aestronglyMeasurable ?_
  exact ae_of_all volume fun y => norm_bettinGonekJKernel_three_line_le hrho t hx y

theorem norm_integral_bettinGonekJKernel_three_line_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, bettinGonekJKernel rho t x (3 + y * Complex.I)‖ ≤
      4 * x ^ 3 * Real.pi := by
  have hmajor : Integrable (fun y : ℝ => 4 * x ^ 3 / (1 + (y + t) ^ 2)) := by
    have hshift := integrable_inv_one_add_sq.comp_add_left t
    have hscaled := hshift.const_mul (4 * x ^ 3)
    simpa only [Function.comp_apply, add_comm, div_eq_mul_inv] using hscaled
  have hbound := norm_integral_le_of_norm_le hmajor
    (ae_of_all volume fun y => norm_bettinGonekJKernel_three_line_le hrho t hx y)
  calc
    ‖∫ y : ℝ, bettinGonekJKernel rho t x (3 + y * Complex.I)‖ ≤
        ∫ y : ℝ, 4 * x ^ 3 / (1 + (y + t) ^ 2) := hbound
    _ = (4 * x ^ 3) * ∫ y : ℝ, (1 + (y + t) ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, integral_const_mul]
    _ = (4 * x ^ 3) * ∫ y : ℝ, (1 + y ^ 2)⁻¹ := by
      congr 1
      simpa only [add_comm t] using
        (integral_add_left_eq_self t (f := fun y : ℝ => (1 + y ^ 2)⁻¹))
    _ = 4 * x ^ 3 * Real.pi := by rw [integral_univ_inv_one_add_sq]

theorem bettinGonekJKernel_eq_poleRemoved_div (rho : ℂ) (t x : ℝ) (w : ℂ) :
    bettinGonekJKernel rho t x w =
      bettinGonekJKernelPoleRemoved t x w /
        (w - bettinGonekSelectedPole rho t) := by
  rw [bettinGonekJKernel, bettinGonekJKernelPoleRemoved, div_div]
  congr 1
  ring

theorem differentiableOn_bettinGonekJKernelPoleRemoved
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (bettinGonekJKernelPoleRemoved t x)
      bettinGonekAuxiliaryDomain := by
  intro w hw
  have hwAddOne : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    exact (by linarith : ¬ (-1 < w.re)) hw
  have hwAddItOne : w + t * Complex.I + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, Complex.mul_re] at hre
    exact (by linarith : ¬ (-1 < w.re)) hw
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) w :=
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hlinear : DifferentiableAt ℂ
      (fun z : ℂ => z - 3 / 2 + t * Complex.I) w := by
    fun_prop
  have hnum : DifferentiableAt ℂ
      (fun z : ℂ => (z - 3 / 2 + t * Complex.I) * (x : ℂ) ^ z) w :=
    hlinear.mul hpow
  have hden : DifferentiableAt ℂ
      (fun z : ℂ => (z + 1) ^ 2 * (z + t * Complex.I + 1) ^ 4) w := by
    fun_prop
  change DifferentiableWithinAt ℂ
    (fun z : ℂ =>
      ((z - 3 / 2 + t * Complex.I) * (x : ℂ) ^ z) /
        ((z + 1) ^ 2 * (z + t * Complex.I + 1) ^ 4))
    bettinGonekAuxiliaryDomain w
  exact (hnum.div hden
    (mul_ne_zero (pow_ne_zero 2 hwAddOne) (pow_ne_zero 4 hwAddItOne))).differentiableWithinAt

theorem bettinGonekJKernel_rectangleBoundaryIntegral
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    {T : ℝ} (hT : |(bettinGonekSelectedPole rho t).im| < T) :
    rectangleBoundaryIntegral (bettinGonekJKernel rho t x) 0 3 (-T) T =
      2 * (Real.pi : ℂ) * Complex.I * bettinGonekResidueCoefficient rho t x := by
  let U : Set ℂ := bettinGonekAuxiliaryDomain
  have hU : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hrect : [[(0 : ℝ), 3]] ×ℂ [[-T, T]] ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    change -1 < z.re
    have hz0 : 0 ≤ z.re := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] at hz
      exact hz.1.1
    linarith
  have hpoleRe : (bettinGonekSelectedPole rho t).re = rho.re + 1 / 2 := by
    simp [bettinGonekSelectedPole]
  have hpoleIm : (bettinGonekSelectedPole rho t).im = rho.im - t := by
    simp [bettinGonekSelectedPole]
  have hlocal := rectangleBoundaryIntegral_weighted_cauchyKernel_of_differentiableOn
    hU (differentiableOn_bettinGonekJKernelPoleRemoved t hx) hrect
    (show 0 < (bettinGonekSelectedPole rho t).re by
      rw [hpoleRe]
      linarith [nontrivial_zero_re_pos hrho])
    (show (bettinGonekSelectedPole rho t).re < 3 by
      rw [hpoleRe]
      linarith [nontrivial_zero_re_lt_one hrho])
    (show -T < (bettinGonekSelectedPole rho t).im by
      rw [neg_lt]
      exact (neg_le_abs _).trans_lt hT)
    (show (bettinGonekSelectedPole rho t).im < T by
      exact (le_abs_self _).trans_lt hT)
  rw [show bettinGonekJKernel rho t x = fun z =>
      bettinGonekJKernelPoleRemoved t x z /
        (z - bettinGonekSelectedPole rho t) by
      funext z
      exact bettinGonekJKernel_eq_poleRemoved_div rho t x z]
  simpa only [bettinGonekJKernelPoleRemoved_selectedPole] using hlocal

theorem bettinGonekJKernel_vertical_sub_residue_eq_left_add_horizontals
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    {T : ℝ} (hT : |(bettinGonekSelectedPole rho t).im| < T) :
    (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (3 + y * Complex.I)) -
        (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x =
      (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (y * Complex.I)) +
        Complex.I *
          ((∫ a : ℝ in 0..3,
              bettinGonekJKernel rho t x (a + (-T) * Complex.I)) -
            ∫ a : ℝ in 0..3,
              bettinGonekJKernel rho t x (a + T * Complex.I)) := by
  have hboundary := bettinGonekJKernel_rectangleBoundaryIntegral hrho t hx hT
  rw [rectangleBoundaryIntegral] at hboundary
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_neg] at hboundary
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_sub, mul_add]
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  linear_combination hboundary

private theorem norm_cpow_strip_le
    {x a v : ℝ} (hx : 0 < x) (ha : a ∈ Set.Icc (0 : ℝ) 3) :
    ‖(x : ℂ) ^ ((a : ℂ) + v * Complex.I)‖ ≤ max 1 (x ^ 3) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  by_cases hxone : 1 ≤ x
  · calc
      x ^ a ≤ x ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hxone ha.2
      _ = x ^ 3 := by norm_num
      _ ≤ max 1 (x ^ 3) := le_max_right _ _
  · calc
      x ^ a ≤ 1 := Real.rpow_le_one hx.le (le_of_not_ge hxone) ha.1
      _ ≤ max 1 (x ^ 3) := le_max_left _ _

theorem norm_bettinGonekJKernel_horizontal_le
    {rho : ℂ} (_hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    {a u : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 3)
    (huOne : 1 ≤ |u|) (huRho : 2 * |rho.im| ≤ |u|) :
    ‖bettinGonekJKernel rho t x (a + (u - t) * Complex.I)‖ ≤
      5 * max 1 (x ^ 3) / |u| ^ 4 := by
  let w : ℂ := a + (u - t) * Complex.I
  let U : ℝ := |u|
  let X : ℝ := max 1 (x ^ 3)
  have hUpos : 0 < U := lt_of_lt_of_le (by norm_num) huOne
  have hXnonneg : 0 ≤ X :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (x ^ 3))
  have hlinear : w - 3 / 2 + t * Complex.I = (a - 3 / 2 : ℝ) + u * Complex.I := by
    dsimp [w]
    push_cast
    ring
  have haAbs : |a - 3 / 2| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith [ha.1, ha.2]
  have hnum : ‖w - 3 / 2 + t * Complex.I‖ ≤ (5 / 2 : ℝ) * U := by
    rw [hlinear]
    calc
      ‖((a - 3 / 2 : ℝ) : ℂ) + u * Complex.I‖ ≤
          ‖((a - 3 / 2 : ℝ) : ℂ)‖ + ‖(u : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = |a - 3 / 2| + |u| := by
        simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one]
      _ ≤ 3 / 2 + U := by
        exact add_le_add haAbs le_rfl
      _ ≤ (5 / 2 : ℝ) * U := by
        dsimp [U]
        linarith
  have hpole : U / 2 ≤ ‖w - bettinGonekSelectedPole rho t‖ := by
    have him : (w - bettinGonekSelectedPole rho t).im = u - rho.im := by
      simp [w, bettinGonekSelectedPole]
    have htri : |u| ≤ |u - rho.im| + |rho.im| := by
      calc
        |u| = |(u - rho.im) + rho.im| := by ring_nf
        _ ≤ |u - rho.im| + |rho.im| := abs_add_le _ _
    have hdiff : U / 2 ≤ |u - rho.im| := by
      dsimp [U]
      linarith
    calc
      U / 2 ≤ |(w - bettinGonekSelectedPole rho t).im| := by simpa [him]
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ := abs_im_le_norm _
  have hone : 1 ≤ ‖w + 1‖ := by
    have hre : (w + 1).re = a + 1 := by simp [w]
    calc
      1 ≤ |(w + 1).re| := by
        rw [hre, abs_of_nonneg]
        · linarith [ha.1]
        · linarith [ha.1]
      _ ≤ ‖w + 1‖ := abs_re_le_norm _
  have hit : U ≤ ‖w + t * Complex.I + 1‖ := by
    have him : (w + t * Complex.I + 1).im = u := by
      simp [w]
    calc
      U = |(w + t * Complex.I + 1).im| := by rw [him]
      _ ≤ ‖w + t * Complex.I + 1‖ := abs_im_le_norm _
  have hpow : ‖(x : ℂ) ^ w‖ ≤ X := by
    dsimp [w, X]
    simpa only [Complex.ofReal_sub] using norm_cpow_strip_le (v := u - t) hx ha
  have hnumerator :
      ‖(w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w‖ ≤
        (5 / 2 : ℝ) * U * X := by
    rw [norm_mul]
    exact mul_le_mul hnum hpow (norm_nonneg _) (by positivity)
  have hitFourth : U ^ 4 ≤ ‖w + t * Complex.I + 1‖ ^ 4 := by
    gcongr
  have hdenLower :
      (U / 2) * U ^ 4 ≤
        ‖(w - bettinGonekSelectedPole rho t) *
          ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc
      (U / 2) * U ^ 4 ≤
          ‖w - bettinGonekSelectedPole rho t‖ * U ^ 4 :=
        mul_le_mul_of_nonneg_right hpole (by positivity)
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ *
          (‖w + 1‖ ^ 2 * U ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        have honeSq : 1 ≤ ‖w + 1‖ ^ 2 := by
          nlinarith [hone, norm_nonneg (w + 1)]
        simpa using mul_le_mul_of_nonneg_right honeSq (by positivity : 0 ≤ U ^ 4)
      _ ≤ ‖w - bettinGonekSelectedPole rho t‖ *
          (‖w + 1‖ ^ 2 * ‖w + t * Complex.I + 1‖ ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hitFourth (sq_nonneg _)
  have hdenPos :
      0 < ‖(w - bettinGonekSelectedPole rho t) *
        ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    have : 0 < (U / 2) * U ^ 4 := by positivity
    exact this.trans_le hdenLower
  have hnorm :
      ‖bettinGonekJKernel rho t x w‖ =
        ‖(w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w‖ /
          ‖(w - bettinGonekSelectedPole rho t) *
            ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ := by
    rw [bettinGonekJKernel, norm_div]
  change ‖bettinGonekJKernel rho t x w‖ ≤ 5 * X / U ^ 4
  rw [hnorm]
  apply (div_le_div_iff₀ hdenPos (pow_pos hUpos 4)).2
  calc
    ‖(w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w‖ * U ^ 4 ≤
        ((5 / 2 : ℝ) * U * X) * U ^ 4 :=
      mul_le_mul_of_nonneg_right hnumerator (by positivity)
    _ = (5 * X) * ((U / 2) * U ^ 4) := by ring
    _ ≤ (5 * X) *
        ‖(w - bettinGonekSelectedPole rho t) *
          ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)‖ :=
      mul_le_mul_of_nonneg_left hdenLower (by positivity)

theorem norm_integral_bettinGonekJKernel_horizontal_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    {u : ℝ} (huOne : 1 ≤ |u|) (huRho : 2 * |rho.im| ≤ |u|) :
    ‖∫ a : ℝ in 0..3,
        bettinGonekJKernel rho t x (a + (u - t) * Complex.I)‖ ≤
      15 * max 1 (x ^ 3) / |u| ^ 4 := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 3)
    (f := fun a : ℝ => bettinGonekJKernel rho t x (a + (u - t) * Complex.I))
    (C := 5 * max 1 (x ^ 3) / |u| ^ 4) (fun a ha => by
      apply norm_bettinGonekJKernel_horizontal_le hrho t hx
      · norm_num at ha
        exact ⟨ha.1.le, ha.2⟩
      · exact huOne
      · exact huRho)
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 - 0)] at hbound
  calc
    ‖∫ a : ℝ in 0..3,
        bettinGonekJKernel rho t x (a + (u - t) * Complex.I)‖ ≤
        (5 * max 1 (x ^ 3) / |u| ^ 4) * (3 - 0) := hbound
    _ = 15 * max 1 (x ^ 3) / |u| ^ 4 := by ring

theorem tendsto_integral_bettinGonekJKernel_horizontal_of_abs_atTop
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x)
    {v : ℝ → ℝ} (hv : Tendsto (fun T => |v T|) atTop atTop) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 0..3,
        bettinGonekJKernel rho t x (a + (v T - t) * Complex.I))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlarge : ∀ᶠ T : ℝ in atTop,
      max 1 (2 * |rho.im|) ≤ |v T| :=
    Filter.tendsto_atTop.1 hv (max 1 (2 * |rho.im|))
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ a : ℝ in 0..3,
          bettinGonekJKernel rho t x (a + (v T - t) * Complex.I)‖ ≤
        15 * max 1 (x ^ 3) / |v T| ^ 4 := by
    filter_upwards [hlarge] with T hT
    apply norm_integral_bettinGonekJKernel_horizontal_le hrho t hx
    · exact (le_max_left _ _).trans hT
    · exact (le_max_right _ _).trans hT
  have hpow : Tendsto (fun T : ℝ => |v T| ^ 4) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp hv
  have hinv : Tendsto (fun T : ℝ => (|v T| ^ 4)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hmajor : Tendsto
      (fun T : ℝ => 15 * max 1 (x ^ 3) / |v T| ^ 4) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => 15 * max 1 (x ^ 3)) atTop
        (nhds (15 * max 1 (x ^ 3))) := tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hconst.mul hinv
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hmajor

theorem tendsto_integral_bettinGonekJKernel_top_horizontal
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 0..3,
        bettinGonekJKernel rho t x (a + T * Complex.I))
      atTop (nhds 0) := by
  have hv : Tendsto (fun T : ℝ => |T + t|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp
      (tendsto_atTop_add_const_right atTop t tendsto_id)
  simpa only [Complex.ofReal_add, add_sub_cancel_right] using
    tendsto_integral_bettinGonekJKernel_horizontal_of_abs_atTop hrho t hx hv

theorem tendsto_integral_bettinGonekJKernel_bottom_horizontal
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 0..3,
        bettinGonekJKernel rho t x (a + (-T) * Complex.I))
      atTop (nhds 0) := by
  have hshift : Tendsto (fun T : ℝ => T - t) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-t) tendsto_id
  have hv' : Tendsto (fun T : ℝ => |T - t|) atTop atTop := by
    change Tendsto (abs ∘ fun T : ℝ => T - t) atTop atTop
    exact tendsto_abs_atTop_atTop.comp hshift
  have hv : Tendsto (fun T : ℝ => |t - T|) atTop atTop := by
    simpa only [abs_sub_comm] using hv'
  simpa only [Complex.ofReal_sub, sub_sub_cancel_left] using
    tendsto_integral_bettinGonekJKernel_horizontal_of_abs_atTop hrho t hx hv

theorem integral_bettinGonekJKernel_three_eq_zero_add_residue
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ y : ℝ, bettinGonekJKernel rho t x (3 + y * Complex.I)) =
      (∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I)) +
        (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x := by
  have hright := intervalIntegral_tendsto_integral
    (integrable_bettinGonekJKernel_three_line hrho t hx)
    tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral
    (integrable_bettinGonekJKernel_zero_line hrho t hx)
    tendsto_neg_atTop_atBot tendsto_id
  have hright' : Tendsto
      (fun T : ℝ => ∫ y : ℝ in -T..T,
        bettinGonekJKernel rho t x (3 + y * Complex.I)) atTop
      (nhds (∫ y : ℝ, bettinGonekJKernel rho t x (3 + y * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hright
  have hleft' : Tendsto
      (fun T : ℝ => ∫ y : ℝ in -T..T,
        bettinGonekJKernel rho t x (y * Complex.I)) atTop
      (nhds (∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hleft
  have hbottom := tendsto_integral_bettinGonekJKernel_bottom_horizontal hrho t hx
  have htop := tendsto_integral_bettinGonekJKernel_top_horizontal hrho t hx
  have hhoriz : Tendsto
      (fun T : ℝ => Complex.I *
        ((∫ a : ℝ in 0..3,
            bettinGonekJKernel rho t x (a + (-T) * Complex.I)) -
          ∫ a : ℝ in 0..3,
            bettinGonekJKernel rho t x (a + T * Complex.I)))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using
      (tendsto_const_nhds.mul (hbottom.sub htop) : Tendsto
        (fun T : ℝ => Complex.I *
          ((∫ a : ℝ in 0..3,
              bettinGonekJKernel rho t x (a + (-T) * Complex.I)) -
            ∫ a : ℝ in 0..3,
              bettinGonekJKernel rho t x (a + T * Complex.I)))
        atTop (nhds (Complex.I * (0 - 0))))
  have hfinite : ∀ᶠ T : ℝ in atTop,
      (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (3 + y * Complex.I)) -
          (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x =
        (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 0..3,
                bettinGonekJKernel rho t x (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 0..3,
                bettinGonekJKernel rho t x (a + T * Complex.I)) := by
    filter_upwards [eventually_gt_atTop |(bettinGonekSelectedPole rho t).im|] with T hT
    exact bettinGonekJKernel_vertical_sub_residue_eq_left_add_horizontals hrho t hx hT
  have hleftLimit : Tendsto
      (fun T : ℝ =>
        (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (3 + y * Complex.I)) -
          (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x)
      atTop
      (nhds ((∫ y : ℝ, bettinGonekJKernel rho t x (3 + y * Complex.I)) -
        (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x)) :=
    hright'.sub tendsto_const_nhds
  have hrightLimit : Tendsto
      (fun T : ℝ =>
        (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 0..3,
                bettinGonekJKernel rho t x (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 0..3,
                bettinGonekJKernel rho t x (a + T * Complex.I)))
      atTop (nhds ((∫ y : ℝ,
        bettinGonekJKernel rho t x (y * Complex.I)) + 0)) :=
    hleft'.add hhoriz
  have hfiniteSymm : ∀ᶠ T : ℝ in atTop,
      (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 0..3,
                bettinGonekJKernel rho t x (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 0..3,
                bettinGonekJKernel rho t x (a + T * Complex.I)) =
        (∫ y : ℝ in -T..T, bettinGonekJKernel rho t x (3 + y * Complex.I)) -
          (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x :=
    hfinite.mono fun _ h => h.symm
  have hlimits := tendsto_nhds_unique hleftLimit (hrightLimit.congr' hfiniteSymm)
  linear_combination hlimits

theorem bettinGonekJLineIntegral_three_eq_zero_add_residue
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    bettinGonekJLineIntegral rho t x 3 =
      bettinGonekJLineIntegral rho t x 0 +
        bettinGonekResidueCoefficient rho t x := by
  have hraw := integral_bettinGonekJKernel_three_eq_zero_add_residue hrho t hx
  rw [bettinGonekJLineIntegral, bettinGonekJLineIntegral]
  simp only [Complex.ofReal_zero, zero_add]
  calc
    (1 / (2 * Real.pi) : ℝ) *
        ∫ y : ℝ, bettinGonekJKernel rho t x (3 + y * Complex.I) =
      (1 / (2 * Real.pi) : ℝ) *
        ((∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I)) +
          (2 * Real.pi : ℂ) * bettinGonekResidueCoefficient rho t x) := by
        rw [hraw]
    _ = (1 / (2 * Real.pi) : ℝ) *
          (∫ y : ℝ, bettinGonekJKernel rho t x (y * Complex.I)) +
        bettinGonekResidueCoefficient rho t x := by
      push_cast
      field_simp [Real.pi_ne_zero]
      simp only [mul_comm]

theorem bettinGonekResidueScale_mul_rpow_le_JLineIntegral_three_add_two
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    bettinGonekResidueScale rho t * x ^ (rho.re + 1 / 2) ≤
      ‖bettinGonekJLineIntegral rho t x 3‖ + 2 := by
  rw [← norm_bettinGonekResidueCoefficient rho t hx]
  have hcontour := bettinGonekJLineIntegral_three_eq_zero_add_residue hrho t hx
  have hresidue :
      bettinGonekResidueCoefficient rho t x =
        bettinGonekJLineIntegral rho t x 3 -
          bettinGonekJLineIntegral rho t x 0 := by
    rw [hcontour]
    ring
  rw [hresidue]
  calc
    ‖bettinGonekJLineIntegral rho t x 3 -
        bettinGonekJLineIntegral rho t x 0‖ ≤
        ‖bettinGonekJLineIntegral rho t x 3‖ +
          ‖bettinGonekJLineIntegral rho t x 0‖ := norm_sub_le _ _
    _ ≤ ‖bettinGonekJLineIntegral rho t x 3‖ + 2 := by
      simpa only [add_comm] using
        add_le_add_left (norm_bettinGonekJLineIntegral_zero_le_two hrho t hx)
          ‖bettinGonekJLineIntegral rho t x 3‖

/-- The fixed H1 contour endpoint: literal source cancellation, an exact one-pole contour shift,
uniform control of the boundary line, and selected-zero residue growth. -/
theorem bettinGonekJContour_endpoint
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    (∀ w : ℂ, 3 / 2 < w.re →
      bettinGonekAuxiliaryG rho t w * bettinGonekH t w * (x : ℂ) ^ w =
        bettinGonekJKernel rho t x w) ∧
      Integrable (fun y : ℝ => bettinGonekJKernel rho t x (y * Complex.I)) ∧
      Integrable (fun y : ℝ => bettinGonekJKernel rho t x (3 + y * Complex.I)) ∧
      (∀ T : ℝ, |(bettinGonekSelectedPole rho t).im| < T →
        rectangleBoundaryIntegral (bettinGonekJKernel rho t x) 0 3 (-T) T =
          2 * (Real.pi : ℂ) * Complex.I * bettinGonekResidueCoefficient rho t x) ∧
      Tendsto
        (fun T : ℝ => ∫ a : ℝ in 0..3,
          bettinGonekJKernel rho t x (a + (-T) * Complex.I))
        atTop (nhds 0) ∧
      Tendsto
        (fun T : ℝ => ∫ a : ℝ in 0..3,
          bettinGonekJKernel rho t x (a + T * Complex.I))
        atTop (nhds 0) ∧
      bettinGonekJLineIntegral rho t x 3 =
        bettinGonekJLineIntegral rho t x 0 +
          bettinGonekResidueCoefficient rho t x ∧
      ‖bettinGonekJLineIntegral rho t x 0‖ ≤ 2 ∧
      0 < bettinGonekResidueScale rho t ∧
      ‖bettinGonekResidueCoefficient rho t x‖ =
        bettinGonekResidueScale rho t * x ^ (rho.re + 1 / 2) ∧
      bettinGonekResidueScale rho t * x ^ (rho.re + 1 / 2) ≤
        ‖bettinGonekJLineIntegral rho t x 3‖ + 2 :=
  ⟨fun _ hw => bettinGonekAuxiliary_mul_H_eq_JKernel hrho t x hw,
    integrable_bettinGonekJKernel_zero_line hrho t hx,
    integrable_bettinGonekJKernel_three_line hrho t hx,
    fun _ hT => bettinGonekJKernel_rectangleBoundaryIntegral hrho t hx hT,
    tendsto_integral_bettinGonekJKernel_bottom_horizontal hrho t hx,
    tendsto_integral_bettinGonekJKernel_top_horizontal hrho t hx,
    bettinGonekJLineIntegral_three_eq_zero_add_residue hrho t hx,
    norm_bettinGonekJLineIntegral_zero_le_two hrho t hx,
    bettinGonekResidueScale_pos hrho t,
    norm_bettinGonekResidueCoefficient rho t hx,
    bettinGonekResidueScale_mul_rpow_le_JLineIntegral_three_add_two hrho t hx⟩

end

end LeanLab.Riemann
