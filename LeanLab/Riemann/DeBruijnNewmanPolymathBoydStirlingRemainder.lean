import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelHeatTermEstimate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Boyd--Nemes scaled-Gamma remainder infrastructure

This module verifies the branch, reflection, Stokes-denominator, imaginary-axis boundary,
Phragmen--Lindelof propagation, and explicit-constant steps used in the Boyd `R_2` estimate cited
by Polymath Lemma 5.1(v). The Boyd resurgence representation and its contour estimate remain
separate analytic obligations.
-/

namespace LeanLab.Riemann

open Asymptotics Bornology Complex Filter MeasureTheory Real Set
open scoped ComplexConjugate Filter Real Topology

noncomputable section

/-- Boyd's coefficient `C_2 = (1 + zeta(2))/2`, after substituting `zeta(2) = pi^2/6`. -/
def deBruijnNewmanPolymathBoydC2 : ℝ :=
  (1 / 2) * (1 + Real.pi ^ 2 / 6)

/-- The uniform Boyd majorant used in Polymath Lemma 5.1(v). -/
def deBruijnNewmanPolymathBoydR2Majorant : ℝ :=
  ((2 * Real.sqrt 2 + 1) * deBruijnNewmanPolymathBoydC2) /
    ((2 * Real.pi) ^ 3 * (1 - Real.exp (-2 * Real.pi)))

/-- The scaled Gamma function in Boyd's and Nemes's normalization. -/
def deBruijnNewmanPolymathScaledGamma (z : ℂ) : ℂ :=
  Complex.Gamma z / deBruijnNewmanPolymathGammaStirlingMain z

theorem deBruijnNewmanPolymathGammaStirlingMain_conj
    {z : ℂ} (hz : z.im ≠ 0) :
    deBruijnNewmanPolymathGammaStirlingMain (conj z) =
      conj (deBruijnNewmanPolymathGammaStirlingMain z) := by
  have harg : z.arg ≠ Real.pi := by
    intro h
    exact hz (Complex.arg_eq_pi_iff.mp h).2
  unfold deBruijnNewmanPolymathGammaStirlingMain
  rw [Complex.log_conj z harg]
  simp only [map_mul, conj_ofReal]
  rw [← Complex.exp_conj]
  simp only [map_sub, map_mul, map_div₀, map_one, map_ofNat]

theorem deBruijnNewmanPolymathGammaStirlingR2_conj
    {z : ℂ} (hz : z.im ≠ 0) :
    deBruijnNewmanPolymathGammaStirlingR2 (conj z) =
      conj (deBruijnNewmanPolymathGammaStirlingR2 z) := by
  rw [deBruijnNewmanPolymathGammaStirlingR2,
    deBruijnNewmanPolymathGammaStirlingR2, Complex.Gamma_conj,
    deBruijnNewmanPolymathGammaStirlingMain_conj hz]
  simp only [map_sub, map_div₀, map_one, map_mul, map_ofNat]

theorem deBruijnNewmanPolymathGammaStirlingR2_norm_conj
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖deBruijnNewmanPolymathGammaStirlingR2 (conj z)‖ =
      ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ := by
  rw [deBruijnNewmanPolymathGammaStirlingR2_conj hz, norm_conj]

theorem complex_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - Real.pi * Complex.I := by
  rw [Complex.log, Complex.log, norm_neg,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
  push_cast
  ring

/-- The principal-power branch identity underlying Boyd's upper-half-plane continuation. -/
theorem deBruijnNewmanPolymathGammaStirlingMain_mul_neg
    {z : ℂ} (hz : 0 < z.im) :
    deBruijnNewmanPolymathGammaStirlingMain z *
        deBruijnNewmanPolymathGammaStirlingMain (-z) =
      2 * Real.pi * Complex.I * Complex.exp (Real.pi * Complex.I * z) / z := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  let A : ℂ := (z - 1 / 2) * Complex.log z - z
  let B : ℂ := (-z - 1 / 2) * Complex.log (-z) - (-z)
  have hAB : A + B = -Complex.log z + Real.pi * Complex.I * z +
      Real.pi / 2 * Complex.I := by
    dsimp [A, B]
    rw [complex_log_neg_of_im_pos hz]
    ring
  have hsqrt : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
      (Real.sqrt (2 * Real.pi) : ℂ) = (2 * Real.pi : ℝ) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by positivity)]
  rw [deBruijnNewmanPolymathGammaStirlingMain,
    deBruijnNewmanPolymathGammaStirlingMain]
  change ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp A *
      (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp B) = _
  rw [show ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp A *
      (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * Complex.exp B) =
      (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        (Real.sqrt (2 * Real.pi) : ℂ)) * Complex.exp (A + B) by
        rw [Complex.exp_add]
        ring]
  rw [hsqrt]
  push_cast
  rw [hAB, Complex.exp_add, Complex.exp_add, Complex.exp_neg,
    Complex.exp_log hz0, Complex.exp_pi_div_two_mul_I]
  field_simp

theorem deBruijnNewmanPolymathGammaStirlingMain_ne_zero (z : ℂ) :
    deBruijnNewmanPolymathGammaStirlingMain z ≠ 0 := by
  unfold deBruijnNewmanPolymathGammaStirlingMain
  exact mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne')
    (Complex.exp_ne_zero _)

theorem deBruijnNewmanPolymathGammaStirlingMain_differentiableAt
    {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    DifferentiableAt ℂ deBruijnNewmanPolymathGammaStirlingMain z := by
  have hlog := (Complex.hasDerivAt_log hz).differentiableAt
  have hinner := ((differentiableAt_id.sub_const (1 / 2 : ℂ)).mul hlog).sub
    differentiableAt_id
  exact hinner.cexp.const_mul (Real.sqrt (2 * Real.pi) : ℂ)

theorem deBruijnNewmanPolymathScaledGamma_inv_differentiableAt
    {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hnotpole : ∀ m : ℕ, z ≠ -m) :
    DifferentiableAt ℂ
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) z := by
  have hmain := deBruijnNewmanPolymathGammaStirlingMain_differentiableAt hz
  have hgamma := Complex.differentiableAt_Gamma z hnotpole
  have hscaled := hgamma.div hmain
    (deBruijnNewmanPolymathGammaStirlingMain_ne_zero z)
  have hscaledNe :
      Complex.Gamma z / deBruijnNewmanPolymathGammaStirlingMain z ≠ 0 := by
    exact div_ne_zero (Complex.Gamma_ne_zero hnotpole)
      (deBruijnNewmanPolymathGammaStirlingMain_ne_zero z)
  change DifferentiableAt ℂ (fun w : ℂ =>
    (1 : ℂ) / (Complex.Gamma w /
      deBruijnNewmanPolymathGammaStirlingMain w)) z
  exact (differentiableAt_const (c := (1 : ℂ))).div
    hscaled hscaledNe

theorem deBruijnNewmanPolymathScaledGamma_inv_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w)
      {w : ℂ | 0 < w.re} := by
  intro z hz
  change 0 < z.re at hz
  apply DifferentiableAt.differentiableWithinAt
  apply deBruijnNewmanPolymathScaledGamma_inv_differentiableAt (Or.inl hz)
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.natCast_re, Complex.neg_re] at hre
  have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

theorem deBruijnNewmanPolymathScaledGamma_inv_continuousOn_closedRightHalfPlane_of_zero
    (hzero : ContinuousAt
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) 0) :
    ContinuousOn
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w)
      {w : ℂ | 0 ≤ w.re} := by
  intro z hz
  change 0 ≤ z.re at hz
  by_cases hz0 : z = 0
  · simpa [hz0] using hzero.continuousWithinAt
  have hslit : z ∈ Complex.slitPlane := by
    rcases hz.eq_or_lt with hre | hre
    · right
      intro him
      exact hz0 (Complex.ext hre.symm (by simpa using him))
    · exact Or.inl hre
  have hnotpole : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have hre : z.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmReal : (m : ℝ) = 0 := by nlinarith
    have hmNat : m = 0 := Nat.cast_eq_zero.mp hmReal
    exact hz0 (by simpa [hmNat] using hm)
  exact (deBruijnNewmanPolymathScaledGamma_inv_differentiableAt
    hslit hnotpole).continuousAt.continuousWithinAt

theorem deBruijnNewmanPolymathScaledGamma_inv_diffContOnCl_of_zero
    (hzero : ContinuousAt
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) 0) :
    DiffContOnCl ℂ
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w)
      {w : ℂ | 0 < w.re} := by
  refine ⟨deBruijnNewmanPolymathScaledGamma_inv_differentiableOn_rightHalfPlane, ?_⟩
  rw [Complex.closure_setOf_lt_re]
  exact deBruijnNewmanPolymathScaledGamma_inv_continuousOn_closedRightHalfPlane_of_zero hzero

theorem deBruijnNewmanPolymathScaledGamma_ne_zero
    {z : ℂ} (hz : z.im ≠ 0) :
    deBruijnNewmanPolymathScaledGamma z ≠ 0 := by
  apply div_ne_zero
  · apply Complex.Gamma_ne_zero
    intro m h
    have him := congrArg Complex.im h
    exact hz (by simpa using him)
  · exact deBruijnNewmanPolymathGammaStirlingMain_ne_zero z

theorem deBruijnNewmanPolymathScaledGamma_conj
    {z : ℂ} (hz : z.im ≠ 0) :
    deBruijnNewmanPolymathScaledGamma (conj z) =
      conj (deBruijnNewmanPolymathScaledGamma z) := by
  rw [deBruijnNewmanPolymathScaledGamma,
    deBruijnNewmanPolymathScaledGamma, Complex.Gamma_conj,
    deBruijnNewmanPolymathGammaStirlingMain_conj hz]
  simp only [map_div₀]

theorem complex_Gamma_mul_neg_of_im_pos
    {z : ℂ} (hz : 0 < z.im) :
    Complex.Gamma z * Complex.Gamma (-z) =
      -(Real.pi : ℂ) / (z * Complex.sin (Real.pi * z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k
    apply_fun Complex.im
    rw [Complex.im_ofReal_mul, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]
    exact mul_ne_zero Real.pi_pos.ne' hz.ne'
  have hshift : Complex.Gamma (1 - z) =
      (-z) * Complex.Gamma (-z) := by
    rw [show (1 : ℂ) - z = -z + 1 by ring]
    exact Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz0)
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [hshift] at href
  field_simp [hz0, hsin] at href ⊢
  linear_combination -href

theorem one_sub_exp_two_pi_mul_I
    (z : ℂ) :
    1 - Complex.exp (2 * Real.pi * Complex.I * z) =
      -2 * Complex.I * Complex.exp (Real.pi * Complex.I * z) *
        Complex.sin (Real.pi * z) := by
  rw [Complex.sin]
  have harg : (Real.pi : ℂ) * z * Complex.I =
      Real.pi * Complex.I * z := by ring
  rw [harg]
  have hdouble : (2 : ℂ) * Real.pi * Complex.I * z =
      (Real.pi * Complex.I * z) + (Real.pi * Complex.I * z) := by ring
  rw [hdouble, Complex.exp_add]
  field_simp
  rw [Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  simp [Complex.I_sq]

/-- Nemes equation (28), with the principal-power branches proved from the project definitions. -/
theorem deBruijnNewmanPolymathScaledGamma_mul_neg
    {z : ℂ} (hz : 0 < z.im) :
    deBruijnNewmanPolymathScaledGamma z *
        deBruijnNewmanPolymathScaledGamma (-z) =
      1 / (1 - Complex.exp (2 * Real.pi * Complex.I * z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hsin : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k
    apply_fun Complex.im
    rw [Complex.im_ofReal_mul, ← Complex.ofReal_intCast, ← Complex.ofReal_mul,
      Complex.ofReal_im]
    exact mul_ne_zero Real.pi_pos.ne' hz.ne'
  have hexp : Complex.exp ((Real.pi : ℂ) * Complex.I * z) ≠ 0 :=
    Complex.exp_ne_zero _
  rw [deBruijnNewmanPolymathScaledGamma, deBruijnNewmanPolymathScaledGamma,
    div_mul_div_comm, complex_Gamma_mul_neg_of_im_pos hz,
    deBruijnNewmanPolymathGammaStirlingMain_mul_neg hz,
    one_sub_exp_two_pi_mul_I]
  field_simp [hz0, hsin, hexp]

theorem deBruijnNewmanPolymathScaledGamma_eq_continuation
    {z : ℂ} (hz : 0 < z.im) :
    deBruijnNewmanPolymathScaledGamma z =
      (1 / (1 - Complex.exp (2 * Real.pi * Complex.I * z))) /
        deBruijnNewmanPolymathScaledGamma (-z) := by
  apply (eq_div_iff (deBruijnNewmanPolymathScaledGamma_ne_zero
    (show (-z).im ≠ 0 by simpa using hz.ne'))).2
  exact deBruijnNewmanPolymathScaledGamma_mul_neg hz

theorem complex_exp_two_pi_I_mul_I (y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((y : ℂ) * Complex.I)) =
      (Real.exp (-2 * Real.pi * y) : ℝ) := by
  rw [show (2 : ℂ) * Real.pi * Complex.I * ((y : ℂ) * Complex.I) =
      ((-2 * Real.pi * y : ℝ) : ℂ) by
        calc
          (2 : ℂ) * Real.pi * Complex.I * ((y : ℂ) * Complex.I) =
              (2 * Real.pi * y : ℂ) * (Complex.I * Complex.I) := by ring
          _ = ((-2 * Real.pi * y : ℝ) : ℂ) := by
            rw [Complex.I_mul_I]
            push_cast
            ring]
  exact (Complex.ofReal_exp _).symm

/-- The exact boundary modulus in Nemes's proof of the scaled-Gamma ray estimate. -/
theorem deBruijnNewmanPolymathScaledGamma_norm_sq_I
    {y : ℝ} (hy : 0 < y) :
    ‖deBruijnNewmanPolymathScaledGamma ((y : ℂ) * Complex.I)‖ ^ 2 =
      1 / (1 - Real.exp (-2 * Real.pi * y)) := by
  let z : ℂ := (y : ℂ) * Complex.I
  have hz : 0 < z.im := by simp [z, hy]
  have hconjPoint : conj z = -z := by simp [z]
  have hconj := deBruijnNewmanPolymathScaledGamma_conj (z := z) hz.ne'
  rw [hconjPoint] at hconj
  have hprod := deBruijnNewmanPolymathScaledGamma_mul_neg hz
  rw [hconj, show Complex.exp (2 * Real.pi * Complex.I * z) =
      (Real.exp (-2 * Real.pi * y) : ℝ) by
        simpa [z] using complex_exp_two_pi_I_mul_I y] at hprod
  have hdenPos : 0 < 1 - Real.exp (-2 * Real.pi * y) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hdenNorm :
      ‖(1 : ℂ) - (Real.exp (-2 * Real.pi * y) : ℝ)‖ =
        1 - Real.exp (-2 * Real.pi * y) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_real,
      Real.norm_of_nonneg hdenPos.le]
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_conj, norm_div, norm_one, hdenNorm] at hnorm
  simpa [pow_two] using hnorm

theorem deBruijnNewmanPolymathScaledGamma_inv_norm_sq_I
    {y : ℝ} (hy : 0 < y) :
    ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma
        ((y : ℂ) * Complex.I)‖ ^ 2 =
      1 - Real.exp (-2 * Real.pi * y) := by
  have hdenPos : 0 < 1 - Real.exp (-2 * Real.pi * y) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  rw [norm_div, norm_one, div_pow, one_pow,
    deBruijnNewmanPolymathScaledGamma_norm_sq_I hy]
  field_simp [hdenPos.ne']

/-- Nemes equation (13)'s boundary estimate on the positive imaginary axis. -/
theorem deBruijnNewmanPolymathScaledGamma_inv_norm_I_le_one
    {y : ℝ} (hy : 0 < y) :
    ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma
        ((y : ℂ) * Complex.I)‖ ≤ 1 := by
  have hsquare := deBruijnNewmanPolymathScaledGamma_inv_norm_sq_I hy
  have hexpPos : 0 < Real.exp (-2 * Real.pi * y) := Real.exp_pos _
  nlinarith [norm_nonneg ((1 : ℂ) / deBruijnNewmanPolymathScaledGamma
    ((y : ℂ) * Complex.I))]

theorem deBruijnNewmanPolymathScaledGamma_inv_norm_mul_I_le_one
    (y : ℝ) :
    ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma
        ((y : ℂ) * Complex.I)‖ ≤ 1 := by
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hpos : 0 < -y := by linarith
    have hconj := deBruijnNewmanPolymathScaledGamma_conj
      (z := ((-y : ℝ) : ℂ) * Complex.I) (by simpa using hpos.ne')
    have hconjPoint : conj (((-y : ℝ) : ℂ) * Complex.I) =
        (y : ℂ) * Complex.I := by simp
    rw [hconjPoint] at hconj
    rw [hconj, norm_div, norm_one, norm_conj]
    simpa [norm_div] using
      (deBruijnNewmanPolymathScaledGamma_inv_norm_I_le_one hpos)
  · simp [deBruijnNewmanPolymathScaledGamma]
  · exact deBruijnNewmanPolymathScaledGamma_inv_norm_I_le_one hy

/-- Once the analytic growth hypotheses in Nemes's argument are supplied, mathlib's
Phragmen-Lindelof theorem propagates the compiled imaginary-axis bound through the closed right
half-plane. -/
theorem deBruijnNewmanPolymathScaledGamma_inv_norm_rightHalfPlane_le_one_of_growth
    (hd : DiffContOnCl ℂ
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w)
      {w : ℂ | 0 < w.re})
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) =O[
        cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
        fun w : ℂ => Real.exp (B * ‖w‖ ^ c))
    (hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ =>
      ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma (x : ℂ)‖)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma z‖ ≤ 1 := by
  exact PhragmenLindelof.right_half_plane_of_bounded_on_real
    (f := fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w)
    (C := (1 : ℝ)) (z := z) hd hexp hre
    deBruijnNewmanPolymathScaledGamma_inv_norm_mul_I_le_one hz

theorem deBruijnNewmanPolymathScaledGamma_inv_norm_rightHalfPlane_le_one_of_zero_growth
    (hzero : ContinuousAt
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) 0)
    (hexp : ∃ c < (2 : ℝ), ∃ B,
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) =O[
        cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
        fun w : ℂ => Real.exp (B * ‖w‖ ^ c))
    (hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ =>
      ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma (x : ℂ)‖)
    {z : ℂ} (hz : 0 ≤ z.re) :
    ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma z‖ ≤ 1 := by
  exact deBruijnNewmanPolymathScaledGamma_inv_norm_rightHalfPlane_le_one_of_growth
    (deBruijnNewmanPolymathScaledGamma_inv_diffContOnCl_of_zero hzero)
    hexp hre hz

theorem exp_neg_two_pi_lt_one_div_four_hundred :
    Real.exp (-2 * Real.pi) < 1 / 400 := by
  have hpi : 6 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hexp : Real.exp (-2 * Real.pi) < Real.exp (-6) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hbase : Real.exp (-1) < (46 / 125 : ℝ) :=
    Real.exp_neg_one_lt_d9.trans (by norm_num)
  have hpow : Real.exp (-1) ^ 6 < (46 / 125 : ℝ) ^ 6 :=
    pow_lt_pow_left₀ hbase (Real.exp_pos (-1)).le (by norm_num)
  have hexpSix : Real.exp (-6) = Real.exp (-1) ^ 6 := by
    simpa using (Real.exp_nat_mul (-1) 6)
  rw [hexpSix] at hexp
  exact hexp.trans (hpow.trans_le (by norm_num))

theorem deBruijnNewmanPolymathBoyd_stokesDenominator_lower_im
    (z : ℂ) :
    1 - Real.exp (-2 * Real.pi * z.im) ≤
      ‖1 - Complex.exp (2 * Real.pi * Complex.I * z)‖ := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I * z).re =
      -2 * Real.pi * z.im := by
    norm_num [Complex.mul_re]
  have hreverse := norm_sub_norm_le (1 : ℂ)
    (Complex.exp (2 * Real.pi * Complex.I * z))
  rw [norm_one, Complex.norm_exp, hre] at hreverse
  exact hreverse

/-- The reflection-formula part of Nemes's scaled-Gamma ray estimate. -/
theorem deBruijnNewmanPolymathScaledGamma_norm_le_stokes_of_mirror_inv
    {z : ℂ} (hz : 0 < z.im)
    (hinv : ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma (-conj z)‖ ≤ 1) :
    ‖deBruijnNewmanPolymathScaledGamma z‖ ≤
      1 / ‖1 - Complex.exp (2 * Real.pi * Complex.I * z)‖ := by
  have hmirrorIm : (-conj z).im ≠ 0 := by simpa using hz.ne'
  have hmirrorConj : conj (-conj z) = -z := by simp
  have hconj := deBruijnNewmanPolymathScaledGamma_conj
    (z := -conj z) hmirrorIm
  rw [hmirrorConj] at hconj
  have hmirrorNe := deBruijnNewmanPolymathScaledGamma_ne_zero hmirrorIm
  have hmirrorNormPos : 0 <
      ‖deBruijnNewmanPolymathScaledGamma (-conj z)‖ :=
    norm_pos_iff.mpr hmirrorNe
  have hprod := deBruijnNewmanPolymathScaledGamma_mul_neg hz
  have hnorm := congrArg norm hprod
  rw [norm_mul, hconj, norm_conj, norm_div, norm_one] at hnorm
  have heq : ‖deBruijnNewmanPolymathScaledGamma z‖ =
      (1 / ‖1 - Complex.exp (2 * Real.pi * Complex.I * z)‖) /
        ‖deBruijnNewmanPolymathScaledGamma (-conj z)‖ := by
    exact (eq_div_iff hmirrorNormPos.ne').2 hnorm
  have hinv' : 1 / ‖deBruijnNewmanPolymathScaledGamma (-conj z)‖ ≤ 1 := by
    simpa [norm_div] using hinv
  rw [heq, div_eq_mul_inv]
  exact mul_le_of_le_one_right (by positivity)
    (by simpa only [one_div] using hinv')

theorem deBruijnNewmanPolymathScaledGamma_norm_le_ray_of_mirror_inv
    {z : ℂ} (hz : 0 < z.im)
    (hinv : ‖(1 : ℂ) / deBruijnNewmanPolymathScaledGamma (-conj z)‖ ≤ 1) :
    ‖deBruijnNewmanPolymathScaledGamma z‖ ≤
      1 / (1 - Real.exp (-2 * Real.pi * z.im)) := by
  have hbase : 0 < 1 - Real.exp (-2 * Real.pi * z.im) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  exact (deBruijnNewmanPolymathScaledGamma_norm_le_stokes_of_mirror_inv
    hz hinv).trans (one_div_le_one_div_of_le hbase
      (deBruijnNewmanPolymathBoyd_stokesDenominator_lower_im z))

/-- The Stokes denominator in Boyd's left-half-plane continuation is uniformly separated from
zero one unit above the real axis. -/
theorem deBruijnNewmanPolymathBoyd_stokesDenominator_lower
    {z : ℂ} (hz : 1 ≤ z.im) :
    1 - Real.exp (-2 * Real.pi) ≤
      ‖1 - Complex.exp (2 * Real.pi * Complex.I * z)‖ := by
  have hre : (2 * (Real.pi : ℂ) * Complex.I * z).re = -2 * Real.pi * z.im := by
    norm_num [Complex.mul_re]
  have hnormExp : ‖Complex.exp (2 * Real.pi * Complex.I * z)‖ ≤
      Real.exp (-2 * Real.pi) := by
    rw [Complex.norm_exp, hre]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hreverse := norm_sub_norm_le (1 : ℂ)
    (Complex.exp (2 * Real.pi * Complex.I * z))
  rw [norm_one] at hreverse
  linarith

theorem deBruijnNewmanPolymathBoyd_stokesDenominator_lower_rational
    {z : ℂ} (hz : 1 ≤ z.im) :
    (399 / 400 : ℝ) < ‖1 - Complex.exp (2 * Real.pi * Complex.I * z)‖ := by
  have hden := deBruijnNewmanPolymathBoyd_stokesDenominator_lower hz
  have hexp := exp_neg_two_pi_lt_one_div_four_hundred
  linarith

theorem deBruijnNewmanPolymathBoydC2_le :
    deBruijnNewmanPolymathBoydC2 ≤
      (1 / 2 : ℝ) * (1 + (31416 / 10000 : ℝ) ^ 2 / 6) := by
  have hpiUpper : Real.pi ≤ (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h.le
  have hpiSq : Real.pi ^ 2 ≤ (31416 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ Real.pi_pos.le hpiUpper 2
  dsimp [deBruijnNewmanPolymathBoydC2]
  nlinarith

/-- The explicit Boyd coefficient used by Polymath is strictly below `0.0205`. -/
theorem deBruijnNewmanPolymathBoydR2Majorant_lt :
    deBruijnNewmanPolymathBoydR2Majorant < 41 / 2000 := by
  have hsqrt : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hfirst : 2 * Real.sqrt 2 + 1 ≤ 2 * (14143 / 10000 : ℝ) + 1 := by
    linarith
  have hc2 := deBruijnNewmanPolymathBoydC2_le
  have hc2Nonneg : 0 ≤ deBruijnNewmanPolymathBoydC2 := by
    dsimp [deBruijnNewmanPolymathBoydC2]
    nlinarith [sq_nonneg Real.pi]
  have hfirstBoundNonneg : 0 ≤ 2 * (14143 / 10000 : ℝ) + 1 := by norm_num
  have hnum :
      (2 * Real.sqrt 2 + 1) * deBruijnNewmanPolymathBoydC2 ≤
        (2 * (14143 / 10000 : ℝ) + 1) *
          ((1 / 2 : ℝ) * (1 + (31416 / 10000 : ℝ) ^ 2 / 6)) := by
    exact mul_le_mul hfirst hc2 hc2Nonneg hfirstBoundNonneg
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hpiCube : (2 * (31415 / 10000 : ℝ)) ^ 3 ≤ (2 * Real.pi) ^ 3 := by
    apply pow_le_pow_left₀ (by norm_num)
    nlinarith
  have hstokes : (399 / 400 : ℝ) ≤ 1 - Real.exp (-2 * Real.pi) := by
    linarith [exp_neg_two_pi_lt_one_div_four_hundred]
  have hden :
      (2 * (31415 / 10000 : ℝ)) ^ 3 * (399 / 400 : ℝ) ≤
        (2 * Real.pi) ^ 3 * (1 - Real.exp (-2 * Real.pi)) := by
    exact mul_le_mul hpiCube hstokes (by norm_num) (by positivity)
  have hdenPos : 0 <
      (2 * (31415 / 10000 : ℝ)) ^ 3 * (399 / 400 : ℝ) := by norm_num
  have hactualDenPos : 0 <
      (2 * Real.pi) ^ 3 * (1 - Real.exp (-2 * Real.pi)) :=
    lt_of_lt_of_le hdenPos hden
  have hnumNonneg : 0 ≤
      (2 * Real.sqrt 2 + 1) * deBruijnNewmanPolymathBoydC2 := by
    dsimp [deBruijnNewmanPolymathBoydC2]
    positivity
  have hnumBoundNonneg : 0 ≤
      (2 * (14143 / 10000 : ℝ) + 1) *
        ((1 / 2 : ℝ) * (1 + (31416 / 10000 : ℝ) ^ 2 / 6)) := by norm_num
  rw [deBruijnNewmanPolymathBoydR2Majorant]
  calc
    ((2 * Real.sqrt 2 + 1) * deBruijnNewmanPolymathBoydC2) /
          ((2 * Real.pi) ^ 3 * (1 - Real.exp (-2 * Real.pi))) ≤
        ((2 * (14143 / 10000 : ℝ) + 1) *
          ((1 / 2 : ℝ) * (1 + (31416 / 10000 : ℝ) ^ 2 / 6))) /
          ((2 * Real.pi) ^ 3 * (1 - Real.exp (-2 * Real.pi))) :=
      div_le_div_of_nonneg_right hnum hactualDenPos.le
    _ ≤ ((2 * (14143 / 10000 : ℝ) + 1) *
          ((1 / 2 : ℝ) * (1 + (31416 / 10000 : ℝ) ^ 2 / 6))) /
          ((2 * (31415 / 10000 : ℝ)) ^ 3 * (399 / 400 : ℝ)) :=
      div_le_div_of_nonneg_left hnumBoundNonneg hdenPos hden
    _ < 41 / 2000 := by norm_num

theorem deBruijnNewmanPolymathBoydR2Majorant_le :
    deBruijnNewmanPolymathBoydR2Majorant ≤ 41 / 2000 :=
  deBruijnNewmanPolymathBoydR2Majorant_lt.le

end

end LeanLab.Riemann
