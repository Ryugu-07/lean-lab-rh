import LeanLab.Riemann.WeilCompactLaplaceZeroCutoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The compact-smooth arithmetic side of Weil's explicit formula

This module evaluates the pole, real-place, and von-Mangoldt terms for the reflection-symmetrized
bilateral Laplace transform of a smooth compactly supported function on the logarithmic line.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval LSeries.notation
  RealInnerProductSpace Topology

namespace LeanLab.Riemann

noncomputable section

/-- The physical finite-place weight attached to a compact logarithmic test function. -/
def compactSymmetrizedVonMangoldtWeight (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
    (f (Real.log n) + f (-Real.log n) / (n : ℂ))

/-- The real-place contribution for a reflection-symmetrized compact Laplace weight. -/
def compactSymmetrizedXiArchimedeanIntegral (f : ℝ → ℂ) (c : ℝ) : ℂ :=
  ∫ y : ℝ,
    symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
      logDeriv Gammaℝ ((c : ℂ) + y * I)

/-- Multiplying a compact test by a real exponential produces the Fourier density of one
vertical Laplace branch. -/
def compactLaplaceFourierDensity (f : ℝ → ℂ) (c x : ℝ) : ℂ :=
  Complex.exp ((c : ℂ) * (x : ℂ)) * f x

theorem contDiff_compactLaplaceFourierDensity {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (compactLaplaceFourierDensity f c) := by
  unfold compactLaplaceFourierDensity
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).mul hf

theorem hasCompactSupport_compactLaplaceFourierDensity {f : ℝ → ℂ}
    (hfsupp : HasCompactSupport f) (c : ℝ) :
    HasCompactSupport (compactLaplaceFourierDensity f c) := by
  exact hfsupp.mul_left

/-- On a vertical line, a bilateral Laplace transform is the ordinary Fourier transform of its
exponentially weighted physical density at frequency `-y/(2*pi)`. -/
theorem compactLaplaceTransform_vertical_eq_fourier
    (f : ℝ → ℂ) (c y : ℝ) :
    compactLaplaceTransform f ((c : ℂ) + y * I) =
      𝓕 (compactLaplaceFourierDensity f c) (-y / (2 * Real.pi)) := by
  rw [Real.fourier_eq']
  unfold compactLaplaceTransform compactLaplaceFourierDensity
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  simp only [RCLike.inner_apply, conj_trivial, ofReal_mul, smul_eq_mul, mul_assoc]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf

/-- Fourier inversion for the exponentially weighted compact density, written with the explicit
real-line phase needed by the prime calculation. -/
theorem integral_fourier_compactLaplaceDensity_mul_exp
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c t : ℝ) :
    (∫ w : ℝ,
      𝓕 (compactLaplaceFourierDensity f c) w *
        Complex.exp (((2 * Real.pi * w * t : ℝ) : ℂ) * I)) =
      compactLaplaceFourierDensity f c t := by
  let g : SchwartzMap ℝ ℂ :=
    (hasCompactSupport_compactLaplaceFourierDensity hfsupp c).toSchwartzMap
      (contDiff_compactLaplaceFourierDensity hf c)
  have hgcoe : (g : ℝ → ℂ) = compactLaplaceFourierDensity f c := rfl
  have hcont : Continuous (compactLaplaceFourierDensity f c) :=
    (contDiff_compactLaplaceFourierDensity hf c).continuous
  have hint : Integrable (compactLaplaceFourierDensity f c) :=
    hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_compactLaplaceFourierDensity hfsupp c)
  have hfourier : Integrable (𝓕 (compactLaplaceFourierDensity f c)) := by
    rw [← hgcoe, ← SchwartzMap.fourier_coe]
    exact (𝓕 g).integrable
  have hinv := hint.fourierInv_fourier_eq hfourier hcont.continuousAt (v := t)
  rw [Real.fourierInv_eq'] at hinv
  simp only [RCLike.inner_apply, conj_trivial, ofReal_mul, smul_eq_mul] at hinv
  rw [← hinv]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with w
  rw [mul_comm]
  congr 2
  push_cast
  ring

theorem integrable_fourier_compactLaplaceDensity
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c : ℝ) :
    Integrable (𝓕 (compactLaplaceFourierDensity f c)) := by
  let g : SchwartzMap ℝ ℂ :=
    (hasCompactSupport_compactLaplaceFourierDensity hfsupp c).toSchwartzMap
      (contDiff_compactLaplaceFourierDensity hf c)
  have hgcoe : (g : ℝ → ℂ) = compactLaplaceFourierDensity f c := rfl
  rw [← hgcoe, ← SchwartzMap.fourier_coe]
  exact (𝓕 g).integrable

theorem integrable_compactLaplaceTransform_vertical_mul_exp_neg
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c t : ℝ) :
    Integrable (fun y : ℝ =>
      compactLaplaceTransform f ((c : ℂ) + y * I) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) := by
  let a : ℝ := -(2 * Real.pi)⁻¹
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hscaled : Integrable (fun y : ℝ =>
      𝓕 (compactLaplaceFourierDensity f c) (a * y)) :=
    (integrable_fourier_compactLaplaceDensity hf hfsupp c).comp_mul_left' ha
  have hphaseMeasurable : AEStronglyMeasurable (fun y : ℝ =>
      Complex.exp (-((y * t : ℝ) : ℂ) * I)) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      Complex.exp (-((y * t : ℝ) : ℂ) * I))).aestronglyMeasurable
  have hphaseBound : ∀ᶠ y : ℝ in ae volume,
      ‖Complex.exp (-((y * t : ℝ) : ℂ) * I)‖ ≤ 1 := by
    filter_upwards [] with y
    rw [Complex.norm_exp]
    norm_num [mul_re]
  have hproduct := hscaled.bdd_mul hphaseMeasurable hphaseBound
  apply hproduct.congr
  filter_upwards [] with y
  rw [compactLaplaceTransform_vertical_eq_fourier]
  rw [mul_comm]
  apply congrArg (fun z : ℂ => z * Complex.exp (-((y * t : ℝ) : ℂ) * I))
  apply congrArg (𝓕 (compactLaplaceFourierDensity f c))
  dsimp only [a]
  field_simp [Real.pi_ne_zero]

theorem integrable_compactLaplaceTransform_reflected_vertical_mul_exp_neg
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c t : ℝ) :
    Integrable (fun y : ℝ =>
      compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) := by
  let H : ℝ → ℂ := fun u =>
    compactLaplaceTransform f (((1 - c : ℝ) : ℂ) + u * I) *
      Complex.exp (-((u * (-t) : ℝ) : ℂ) * I)
  have hH : Integrable H := by
    simpa only [H] using
      integrable_compactLaplaceTransform_vertical_mul_exp_neg hf hfsupp (1 - c) (-t)
  have hHneg : Integrable (fun y : ℝ => H (-1 * y)) := hH.comp_mul_left' (by norm_num)
  apply hHneg.congr
  filter_upwards [] with y
  dsimp only [H]
  congr 2
  · push_cast
    ring
  · congr 1
    push_cast
    ring

/-- One von-Mangoldt L-series term multiplied by the symmetric compact weight. -/
def compactSymmetrizedXiPrimeLineTerm
    (f : ℝ → ℂ) (c : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
    LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((c : ℂ) + y * I) n

/-- Exact decomposition of one positive-index prime term into its two inverse-Fourier branches. -/
theorem compactSymmetrizedXiPrimeLineTerm_vertical
    {f : ℝ → ℂ} {c : ℝ} {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    compactSymmetrizedXiPrimeLineTerm f c n y =
      ((ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2) *
        (compactLaplaceTransform f ((c : ℂ) + y * I) *
            Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I) +
          compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
            Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)) := by
  rw [compactSymmetrizedXiPrimeLineTerm, vonMangoldtLSeriesTerm_vertical hn]
  unfold symmetrizedCompactLaplaceWeight
  have hexp :
      Complex.exp (-((c : ℂ) + y * I) * (Real.log n : ℂ)) =
        Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
          Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

theorem integrable_compactSymmetrizedXiPrimeLineTerm
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c : ℝ) (n : ℕ) :
    Integrable (compactSymmetrizedXiPrimeLineTerm f c n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : compactSymmetrizedXiPrimeLineTerm f c 0 = 0 := by
      funext y
      simp [compactSymmetrizedXiPrimeLineTerm, LSeries.term_zero]
    rw [hzero]
    exact MeasureTheory.integrable_zero ℝ ℂ volume
  let C : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2
  let A : ℝ → ℂ := fun y =>
    compactLaplaceTransform f ((c : ℂ) + y * I) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  let B : ℝ → ℂ := fun y =>
    compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  have hA : Integrable A := by
    simpa only [A] using
      integrable_compactLaplaceTransform_vertical_mul_exp_neg hf hfsupp c (Real.log n)
  have hB : Integrable B := by
    simpa only [B] using
      integrable_compactLaplaceTransform_reflected_vertical_mul_exp_neg
        hf hfsupp c (Real.log n)
  have hCAB : Integrable (fun y => C * (A y + B y)) := (hA.add hB).const_mul C
  apply hCAB.congr
  filter_upwards [] with y
  rw [compactSymmetrizedXiPrimeLineTerm_vertical hn]

/-- The first vertical Laplace branch has the exact inverse-Fourier normalization `2*pi`. -/
theorem integral_compactLaplaceTransform_vertical_mul_exp_neg
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c t : ℝ) :
    (∫ y : ℝ,
      compactLaplaceTransform f ((c : ℂ) + y * I) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) * compactLaplaceFourierDensity f c t := by
  let K : ℝ → ℂ := fun w =>
    𝓕 (compactLaplaceFourierDensity f c) w *
      Complex.exp (((2 * Real.pi * w * t : ℝ) : ℂ) * I)
  let a : ℝ := -(2 * Real.pi)⁻¹
  have hscale := Measure.integral_comp_mul_left K a
  have haInv : |a⁻¹| = 2 * Real.pi := by
    dsimp only [a]
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos]
    positivity
  have hK : (∫ w : ℝ, K w) = compactLaplaceFourierDensity f c t := by
    simpa only [K] using integral_fourier_compactLaplaceDensity_mul_exp hf hfsupp c t
  calc
    (∫ y : ℝ,
      compactLaplaceTransform f ((c : ℂ) + y * I) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
        ∫ y : ℝ, K (a * y) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      rw [compactLaplaceTransform_vertical_eq_fourier]
      dsimp only [K, a]
      congr 2
      · field_simp [Real.pi_ne_zero]
      · congr 1
        push_cast
        field_simp [Real.pi_ne_zero]
    _ = |a⁻¹| • ∫ w : ℝ, K w := hscale
    _ = ((2 * Real.pi : ℝ) : ℂ) * compactLaplaceFourierDensity f c t := by
      rw [haInv, hK]
      simp only [Complex.real_smul]

/-- Reflecting the vertical variable evaluates the second Laplace branch at the opposite physical
point. -/
theorem integral_compactLaplaceTransform_reflected_vertical_mul_exp_neg
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c t : ℝ) :
    (∫ y : ℝ,
      compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity f (1 - c) (-t) := by
  let H : ℝ → ℂ := fun u =>
    compactLaplaceTransform f (((1 - c : ℝ) : ℂ) + u * I) *
      Complex.exp (-((u * (-t) : ℝ) : ℂ) * I)
  have hneg := Measure.integral_comp_mul_left H (-1)
  have hneg' : (∫ y : ℝ, H (-y)) = ∫ u : ℝ, H u := by
    simpa only [neg_mul, one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] using hneg
  calc
    (∫ y : ℝ,
      compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
        ∫ y : ℝ, H (-y) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      dsimp only [H]
      congr 2
      · push_cast
        ring
      · congr 1
        push_cast
        ring
    _ = ∫ u : ℝ, H u := hneg'
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity f (1 - c) (-t) := by
      simpa only [H] using
        integral_compactLaplaceTransform_vertical_mul_exp_neg hf hfsupp (1 - c) (-t)

/-- One positive-index prime term evaluates to the exact two-branch physical weight. -/
theorem integral_compactSymmetrizedXiPrimeLineTerm
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c : ℝ) (n : ℕ) :
    (∫ y : ℝ, compactSymmetrizedXiPrimeLineTerm f c n y) =
      compactSymmetrizedVonMangoldtWeight f n := by
  by_cases hn : n = 0
  · subst n
    simp [compactSymmetrizedXiPrimeLineTerm, compactSymmetrizedVonMangoldtWeight,
      LSeries.term_zero]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let C : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2
  let A : ℝ → ℂ := fun y =>
    compactLaplaceTransform f ((c : ℂ) + y * I) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  let B : ℝ → ℂ := fun y =>
    compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  have hA : Integrable A := by
    simpa only [A] using
      integrable_compactLaplaceTransform_vertical_mul_exp_neg hf hfsupp c (Real.log n)
  have hB : Integrable B := by
    simpa only [B] using
      integrable_compactLaplaceTransform_reflected_vertical_mul_exp_neg
        hf hfsupp c (Real.log n)
  have hfirst :
      Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
          Complex.exp ((c : ℂ) * (Real.log n : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  have hsecond :
      Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
          Complex.exp (((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ)) =
        (n : ℂ)⁻¹ := by
    rw [← Complex.exp_add]
    have harg :
        ((-(c * Real.log n) : ℝ) : ℂ) +
            ((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ) =
          ((-Real.log n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hnpos]
    exact Complex.ofReal_inv (n : ℝ)
  have hterm : compactSymmetrizedXiPrimeLineTerm f c n = fun y => C * (A y + B y) := by
    funext y
    rw [compactSymmetrizedXiPrimeLineTerm_vertical hn]
  rw [hterm]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hA hB]
  rw [show (∫ y : ℝ, A y) = ((2 * Real.pi : ℝ) : ℂ) *
      compactLaplaceFourierDensity f c (Real.log n) by
    simpa only [A] using
      integral_compactLaplaceTransform_vertical_mul_exp_neg hf hfsupp c (Real.log n)]
  rw [show (∫ y : ℝ, B y) = ((2 * Real.pi : ℝ) : ℂ) *
      compactLaplaceFourierDensity f (1 - c) (-Real.log n) by
    simpa only [B] using
      integral_compactLaplaceTransform_reflected_vertical_mul_exp_neg
        hf hfsupp c (Real.log n)]
  unfold C compactLaplaceFourierDensity compactSymmetrizedVonMangoldtWeight
  calc
    ((ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2) *
        (((2 * Real.pi : ℝ) : ℂ) *
            (Complex.exp ((c : ℂ) * (Real.log n : ℂ)) * f (Real.log n)) +
          ((2 * Real.pi : ℝ) : ℂ) *
            (Complex.exp (((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ)) *
              f (-Real.log n))) =
        (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
              Complex.exp ((c : ℂ) * (Real.log n : ℂ))) * f (Real.log n) +
            (Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
              Complex.exp (((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ))) *
                f (-Real.log n)) := by
      push_cast
      ring
    _ = (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
        (f (Real.log n) + f (-Real.log n) / (n : ℂ)) := by
      rw [hfirst, hsecond]
      simp only [one_mul, div_eq_mul_inv]
      ring

theorem integrable_symmetrizedCompactLaplaceWeight_vertical
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (c : ℝ) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)) := by
  have hfirst : Integrable (fun y : ℝ =>
      compactLaplaceTransform f ((c : ℂ) + y * I)) := by
    simpa using
      integrable_compactLaplaceTransform_vertical_mul_exp_neg hf hfsupp c 0
  have hsecond : Integrable (fun y : ℝ =>
      compactLaplaceTransform f (1 - ((c : ℂ) + y * I))) := by
    simpa using
      integrable_compactLaplaceTransform_reflected_vertical_mul_exp_neg hf hfsupp c 0
  have hsum := (hfirst.add hsecond).div_const 2
  apply hsum.congr
  filter_upwards [] with y
  rfl

theorem norm_compactSymmetrizedXiPrimeLineTerm
    (f : ℝ → ℂ) (c : ℝ) (n : ℕ) (y : ℝ) :
    ‖compactSymmetrizedXiPrimeLineTerm f c n y‖ =
      ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
        ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (c : ℂ) n‖ := by
  unfold compactSymmetrizedXiPrimeLineTerm
  rw [norm_mul]
  congr 1
  simp [LSeries.norm_term_eq]

theorem integral_norm_compactSymmetrizedXiPrimeLineTerm
    (f : ℝ → ℂ) (c : ℝ) (n : ℕ) :
    (∫ y : ℝ, ‖compactSymmetrizedXiPrimeLineTerm f c n y‖) =
      (∫ y : ℝ,
        ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖) *
        ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (c : ℂ) n‖ := by
  simp_rw [norm_compactSymmetrizedXiPrimeLineTerm]
  rw [MeasureTheory.integral_mul_const]

theorem summable_integral_norm_compactSymmetrizedXiPrimeLineTerm
    {f : ℝ → ℂ} {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ =>
      ∫ y : ℝ, ‖compactSymmetrizedXiPrimeLineTerm f c n y‖) := by
  simp_rw [integral_norm_compactSymmetrizedXiPrimeLineTerm]
  exact Summable.mul_left
    (∫ y : ℝ, ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖)
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)).norm

/-- Absolute series/integral interchange identifies the whole compact prime line with its explicit
physical von-Mangoldt sum. -/
theorem hasSum_integral_compactSymmetrizedXiPrimeLineTerm
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    HasSum (compactSymmetrizedVonMangoldtWeight f)
      (∫ y : ℝ, ∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y) := by
  refine (MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n : ℕ => integrable_compactSymmetrizedXiPrimeLineTerm hf hfsupp c n)
    (summable_integral_norm_compactSymmetrizedXiPrimeLineTerm hc)).congr_fun ?_
  intro n
  exact (integral_compactSymmetrizedXiPrimeLineTerm hf hfsupp c n).symm

theorem tsum_compactSymmetrizedXiPrimeLineTerm (f : ℝ → ℂ) (c y : ℝ) :
    (∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y) =
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
  unfold compactSymmetrizedXiPrimeLineTerm LSeries
  exact tsum_mul_left

theorem summable_compactSymmetrizedVonMangoldtWeight
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Summable (compactSymmetrizedVonMangoldtWeight f) :=
  (hasSum_integral_compactSymmetrizedXiPrimeLineTerm hf hfsupp hc).summable

theorem tsum_compactSymmetrizedVonMangoldtWeight_eq_integral
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    (∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n) =
      ∫ y : ℝ,
        symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
  calc
    (∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n) =
        ∫ y : ℝ, ∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y :=
      (hasSum_integral_compactSymmetrizedXiPrimeLineTerm hf hfsupp hc).tsum_eq
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (tsum_compactSymmetrizedXiPrimeLineTerm f c)

theorem integrable_symmetrizedCompactLaplace_mul_vonMangoldtLSeries
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let S : ℝ := ∑' n : ℕ,
    ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (c : ℂ) n‖
  have hterms : ∀ n : ℕ,
      AEStronglyMeasurable (compactSymmetrizedXiPrimeLineTerm f c n) := fun n =>
    (integrable_compactSymmetrizedXiPrimeLineTerm hf hfsupp c n).aestronglyMeasurable
  have hsumMeasurable : AEStronglyMeasurable
      (fun y : ℝ => ∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y) :=
    MeasureTheory.AEStronglyMeasurable.tsum hterms
  have hpoint (y : ℝ) :
      ‖∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y‖ ≤
        S * ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ := by
    have hsum : Summable (fun n : ℕ => compactSymmetrizedXiPrimeLineTerm f c n y) := by
      unfold compactSymmetrizedXiPrimeLineTerm
      exact Summable.mul_left _
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    calc
      ‖∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y‖ ≤
          ∑' n : ℕ, ‖compactSymmetrizedXiPrimeLineTerm f c n y‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' n : ℕ,
          ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
            ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
              (c : ℂ) n‖ := by
        congr 1
        funext n
        rw [norm_compactSymmetrizedXiPrimeLineTerm]
      _ = ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ * S :=
        tsum_mul_left
      _ = S * ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ := by ring
  have hsumInt : Integrable
      (fun y : ℝ => ∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y) := by
    refine MeasureTheory.Integrable.mono'
      ((integrable_symmetrizedCompactLaplaceWeight_vertical hf hfsupp c).norm.const_mul S)
      hsumMeasurable (Filter.Eventually.of_forall hpoint)
  apply hsumInt.congr
  exact Filter.Eventually.of_forall (tsum_compactSymmetrizedXiPrimeLineTerm f c)

/-- Compact support on the logarithmic line makes the physical von-Mangoldt side a genuinely
finite sum. -/
theorem hasFiniteSupport_compactSymmetrizedVonMangoldtWeight
    {f : ℝ → ℂ} (hfsupp : HasCompactSupport f) :
    Function.HasFiniteSupport (compactSymmetrizedVonMangoldtWeight f) := by
  obtain ⟨R, hR⟩ := hfsupp.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp R)
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  change compactSymmetrizedVonMangoldtWeight f n ≠ 0 at hn
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    subst n
    exact hn (by simp [compactSymmetrizedVonMangoldtWeight])
  have hsum : f (Real.log n) + f (-Real.log n) / (n : ℂ) ≠ 0 := by
    intro hzero
    exact hn (by simp [compactSymmetrizedVonMangoldtWeight, hzero])
  have hor : f (Real.log n) ≠ 0 ∨ f (-Real.log n) ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (by simp [h.1, h.2])
  have hlogmem : Real.log n ∈ tsupport f ∨ -Real.log n ∈ tsupport f :=
    hor.imp (fun h => subset_tsupport f h) (fun h => subset_tsupport f h)
  have hlogle : Real.log n ≤ R := by
    rcases hlogmem with hlogmem | hneglogmem
    · exact (le_abs_self (Real.log n)).trans
        (by simpa [Real.norm_eq_abs] using hR hlogmem)
    · exact (le_abs_self (Real.log n)).trans
        (by simpa [Real.norm_eq_abs, abs_neg] using hR hneglogmem)
  have hnle : (n : ℝ) ≤ Real.exp R := by
    calc
      (n : ℝ) = Real.exp (Real.log n) :=
        (Real.exp_log (Nat.cast_pos.mpr hnpos)).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hlogle
  exact_mod_cast hnle.trans_lt hN

/-- The elementary pole pair inherits the inverse-sixth selected top-edge decay of the compact
Laplace weight. -/
theorem norm_compactSymmetrizedXiPoleTopHorizontalIntegral_le
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) (n : ℕ) :
    ‖selectedXiPoleTopHorizontalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c n‖ ≤
      (2 * (2 * c - 1) * compactLaplaceSixthDerivativeMass c f) *
        (gaussianXiHeightScale c n)⁻¹ ^ (6 : ℕ) := by
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  let M : ℝ := compactLaplaceSixthDerivativeMass c f
  have hRone : 1 ≤ R := by
    dsimp only [R, gaussianXiHeightScale]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hTone : 1 ≤ T := hRone.trans (gaussianXiSelectedHeight_spec c n).1.1.le
  have hpoint : ∀ x ∈ Ι (1 - c) c,
      ‖selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
          ((x : ℂ) + T * I)‖ ≤ 2 * (M * R⁻¹ ^ (6 : ℕ)) := by
    intro x hx
    calc
      ‖selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
          ((x : ℂ) + T * I)‖ ≤
          2 * ‖symmetrizedCompactLaplaceWeight f ((x : ℂ) + T * I)‖ :=
        norm_selectedXiPolePairIntegrandFor_horizontal_le hTone
      _ ≤ 2 * (M * R⁻¹ ^ (6 : ℕ)) := by
        gcongr
        simpa only [M, R, T] using
          norm_symmetrizedCompactLaplaceWeight_selectedTopEdge_le
            hf hfsupp hc n (Set.uIoc_subset_uIcc hx)
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [selectedXiPoleTopHorizontalIntegralFor]
  calc
    ‖∫ x : ℝ in 1 - c..c,
        selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
          ((x : ℂ) + T * I)‖ ≤
        (2 * (M * R⁻¹ ^ (6 : ℕ))) * |c - (1 - c)| := hintegral
    _ = (2 * (2 * c - 1) * compactLaplaceSixthDerivativeMass c f) *
        (gaussianXiHeightScale c n)⁻¹ ^ (6 : ℕ) := by
      rw [abs_of_pos (by linarith : 0 < c - (1 - c))]
      dsimp only [M, R]
      ring

theorem tendsto_compactSymmetrizedXiPoleTopHorizontalIntegral
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto (selectedXiPoleTopHorizontalIntegralFor
      (symmetrizedCompactLaplaceWeight f) c) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (gaussianXiHeightScale c n)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_gaussianXiHeightScale c)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      norm_compactSymmetrizedXiPoleTopHorizontalIntegral_le hf hfsupp hc n
  · simpa using (hinv.pow 6).const_mul
      (2 * (2 * c - 1) * compactLaplaceSixthDerivativeMass c f)

theorem tendsto_compactSymmetrizedXiPoleRightVerticalIntegral
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto (selectedXiPoleRightVerticalIntegralFor
      (symmetrizedCompactLaplaceWeight f) c) atTop
      (𝓝 (2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1)) := by
  have htop :=
    (tendsto_compactSymmetrizedXiPoleTopHorizontalIntegral hf hfsupp hc).const_mul (-I)
  have hconst : Tendsto (fun _ : ℕ => (Real.pi : ℂ) *
      (symmetrizedCompactLaplaceWeight f 0 + symmetrizedCompactLaplaceWeight f 1)) atTop
      (𝓝 ((Real.pi : ℂ) *
        (symmetrizedCompactLaplaceWeight f 0 + symmetrizedCompactLaplaceWeight f 1))) :=
    tendsto_const_nhds
  have hright := (htop.add hconst).congr' (Filter.Eventually.of_forall fun n =>
    (selectedXiPoleRightVerticalIntegral_eq_top_add_residues
      (differentiable_symmetrizedCompactLaplaceWeight hf.continuous hfsupp)
      (symmetrizedCompactLaplaceWeight_one_sub f) hc n).symm)
  have hzero_one : symmetrizedCompactLaplaceWeight f 0 =
      symmetrizedCompactLaplaceWeight f 1 := by
    simpa using symmetrizedCompactLaplaceWeight_one_sub f 1
  simpa only [mul_zero, zero_add, hzero_one, two_mul, add_mul, mul_add] using hright

theorem integrable_compactSymmetrizedXiPolePair
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ => selectedXiPolePairIntegrandFor
      (symmetrizedCompactLaplaceWeight f) ((c : ℂ) + y * I)) := by
  have hweight := integrable_symmetrizedCompactLaplaceWeight_vertical hf hfsupp c
  have hweightContinuous : Continuous (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)) :=
    (differentiable_symmetrizedCompactLaplaceWeight hf.continuous hfsupp).continuous.comp
      (by fun_prop)
  have hcontinuous : Continuous (fun y : ℝ => selectedXiPolePairIntegrandFor
      (symmetrizedCompactLaplaceWeight f) ((c : ℂ) + y * I)) := by
    unfold selectedXiPolePairIntegrandFor
    apply Continuous.add
    · apply Continuous.div hweightContinuous (by fun_prop)
      intro y hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
    · apply Continuous.div hweightContinuous (by fun_prop)
      intro y hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
  refine MeasureTheory.Integrable.mono'
    (hweight.norm.const_mul (c⁻¹ + (c - 1)⁻¹))
    hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  unfold selectedXiPolePairIntegrandFor
  simp only [sub_zero, div_eq_mul_inv]
  calc
    ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I)⁻¹ +
        symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I - 1)⁻¹‖ ≤
      ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
          ‖((c : ℂ) + y * I)⁻¹‖ +
        ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
          ‖((c : ℂ) + y * I - 1)⁻¹‖ := by
      simpa only [norm_mul] using norm_add_le
        (symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I)⁻¹)
        (symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I - 1)⁻¹)
    _ ≤ ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ * c⁻¹ +
        ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ * (c - 1)⁻¹ := by
      gcongr
      · simpa using norm_inv_vertical_sub_real_le (rho := 0) (y := y) (by linarith)
      · simpa using norm_inv_vertical_sub_real_le (rho := 1) (y := y) (by linarith)
    _ = (c⁻¹ + (c - 1)⁻¹) *
        ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ := by ring

/-- The compact pole pair contributes exactly the two elementary residues. -/
theorem integral_compactSymmetrizedXiPolePair_eq
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    (∫ y : ℝ, selectedXiPolePairIntegrandFor
      (symmetrizedCompactLaplaceWeight f) ((c : ℂ) + y * I)) =
      2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1 := by
  have hfull := tendsto_selectedGaussianXiSymmetricIntervalIntegral
    (c := c) (integrable_compactSymmetrizedXiPolePair hf hfsupp hc)
  exact tendsto_nhds_unique hfull
    (tendsto_compactSymmetrizedXiPoleRightVerticalIntegral hf hfsupp hc)

/-- The first absolute moment of every vertical compact Laplace branch is integrable. -/
theorem integrable_one_add_abs_mul_norm_compactLaplaceTransform_vertical
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f) (c : ℝ) :
    Integrable (fun y : ℝ =>
      (|y| + 1) * ‖compactLaplaceTransform f ((c : ℂ) + y * I)‖) := by
  let g : SchwartzMap ℝ ℂ :=
    (hasCompactSupport_compactLaplaceFourierDensity hfsupp c).toSchwartzMap
      (contDiff_compactLaplaceFourierDensity hf c)
  have hgcoe : (g : ℝ → ℂ) = compactLaplaceFourierDensity f c := rfl
  have hfourierWeighted : Integrable (fun w : ℝ =>
      |w| * ‖𝓕 (compactLaplaceFourierDensity f c) w‖) := by
    rw [← hgcoe, ← SchwartzMap.fourier_coe]
    apply ((𝓕 g).integrable_pow_mul volume 1).congr
    filter_upwards [] with w
    simp [Real.norm_eq_abs]
  let a : ℝ := -(2 * Real.pi)⁻¹
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have habsa : |a| ≠ 0 := abs_ne_zero.mpr ha
  have hscaledWeighted : Integrable (fun y : ℝ =>
      |a * y| * ‖𝓕 (compactLaplaceFourierDensity f c) (a * y)‖) :=
    hfourierWeighted.comp_mul_left' ha
  have hscaledAbs : Integrable (fun y : ℝ =>
      |y| * ‖𝓕 (compactLaplaceFourierDensity f c) (a * y)‖) := by
    apply (hscaledWeighted.const_mul |a|⁻¹).congr
    filter_upwards [] with y
    rw [abs_mul]
    field_simp [habsa]
  have hscaled : Integrable (fun y : ℝ =>
      ‖𝓕 (compactLaplaceFourierDensity f c) (a * y)‖) :=
    (integrable_fourier_compactLaplaceDensity hf hfsupp c).norm.comp_mul_left' ha
  apply (hscaledAbs.add hscaled).congr
  filter_upwards [] with y
  have harg : a * y = -y / (2 * Real.pi) := by
    dsimp only [a]
    field_simp [Real.pi_ne_zero]
  rw [compactLaplaceTransform_vertical_eq_fourier, ← harg]
  simp only [Pi.add_apply]
  ring_nf

theorem integrable_one_add_abs_mul_norm_compactLaplaceTransform_reflected_vertical
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f) (c : ℝ) :
    Integrable (fun y : ℝ =>
      (|y| + 1) * ‖compactLaplaceTransform f (1 - ((c : ℂ) + y * I))‖) := by
  let H : ℝ → ℝ := fun u =>
    (|u| + 1) *
      ‖compactLaplaceTransform f (((1 - c : ℝ) : ℂ) + u * I)‖
  have hH : Integrable H := by
    simpa only [H] using
      integrable_one_add_abs_mul_norm_compactLaplaceTransform_vertical
        hf hfsupp (1 - c)
  have hHneg : Integrable (fun y : ℝ => H (-1 * y)) :=
    hH.comp_mul_left' (by norm_num)
  apply hHneg.congr
  filter_upwards [] with y
  dsimp only [H]
  rw [abs_mul, abs_neg, abs_one, one_mul]
  congr 2
  push_cast
  ring_nf

/-- Reflection symmetrization preserves the integrable first absolute moment on every vertical
line. -/
theorem integrable_one_add_abs_mul_norm_symmetrizedCompactLaplaceWeight_vertical
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f) (c : ℝ) :
    Integrable (fun y : ℝ =>
      (|y| + 1) * ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖) := by
  have hfirst :=
    integrable_one_add_abs_mul_norm_compactLaplaceTransform_vertical hf hfsupp c
  have hsecond :=
    integrable_one_add_abs_mul_norm_compactLaplaceTransform_reflected_vertical
      hf hfsupp c
  have hmajorant := (hfirst.add hsecond).div_const 2
  have hcontinuous : Continuous (fun y : ℝ =>
      (|y| + 1) * ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖) :=
    (continuous_abs.add continuous_const).mul
      ((differentiable_symmetrizedCompactLaplaceWeight hf.continuous hfsupp).continuous.comp
        (by fun_prop)).norm
  refine MeasureTheory.Integrable.mono' hmajorant hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))]
  unfold symmetrizedCompactLaplaceWeight
  calc
    (|y| + 1) *
        ‖(compactLaplaceTransform f ((c : ℂ) + y * I) +
          compactLaplaceTransform f (1 - ((c : ℂ) + y * I))) / 2‖ ≤
      (|y| + 1) *
        ((‖compactLaplaceTransform f ((c : ℂ) + y * I)‖ +
          ‖compactLaplaceTransform f (1 - ((c : ℂ) + y * I))‖) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      let A : ℂ := compactLaplaceTransform f ((c : ℂ) + y * I)
      let B : ℂ := compactLaplaceTransform f (1 - ((c : ℂ) + y * I))
      calc
        ‖(A + B) / 2‖ = ‖A + B‖ / 2 := by rw [norm_div]; norm_num
        _ ≤ (‖A‖ + ‖B‖) / 2 :=
          div_le_div_of_nonneg_right (norm_add_le A B) (by norm_num)
    _ = ((|y| + 1) * ‖compactLaplaceTransform f ((c : ℂ) + y * I)‖ +
          (|y| + 1) *
            ‖compactLaplaceTransform f (1 - ((c : ℂ) + y * I))‖) / 2 := by ring

/-- The real-place logarithmic derivative is integrable against every reflection-symmetrized
smooth compact Laplace weight. -/
theorem integrable_compactSymmetrizedXiArchimedean
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  obtain ⟨C, hC, hdigamma⟩ :=
    exists_norm_digamma_div_two_le_log (a := c) (b := c) hc0
  have hlog (y : ℝ) : Real.log (|y| + 2) ≤ |y| + 1 := by
    calc
      Real.log (|y| + 2) ≤ (|y| + 2) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = |y| + 1 := by ring
  have hdigamma' (y : ℝ) :
      ‖digamma (((c : ℂ) + y * I) / 2)‖ ≤ C * (|y| + 1) := by
    calc
      ‖digamma (((c : ℂ) + y * I) / 2)‖ ≤ C * Real.log (|y| + 2) := by
        simpa using hdigamma ((c : ℂ) + y * I) (by simp) (by simp)
      _ ≤ C * (|y| + 1) := mul_le_mul_of_nonneg_left (hlog y) hC.le
  have hlogGamma (y : ℝ) :
      ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
        (|Real.log Real.pi| + C) * (|y| + 1) := by
    calc
      ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
          ‖-(Real.log Real.pi : ℂ) / 2‖ +
            ‖digamma (((c : ℂ) + y * I) / 2) / 2‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 +
          ‖digamma (((c : ℂ) + y * I) / 2)‖ / 2 := by
        simp [Real.norm_eq_abs]
      _ ≤ |Real.log Real.pi| / 2 + (C * (|y| + 1)) / 2 := by
        gcongr
        exact hdigamma' y
      _ ≤ (|Real.log Real.pi| + C) * (|y| + 1) := by
        nlinarith [abs_nonneg (Real.log Real.pi), abs_nonneg y,
          hC.le, mul_nonneg hC.le (by positivity : 0 ≤ |y| + 1)]
  have hdigammaContinuous : Continuous (fun y : ℝ =>
      digamma (((c : ℂ) + y * I) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_digamma_of_re_pos (by norm_num [div_re]; linarith)).comp
      (by fun_prop)
  have hweightContinuous : Continuous (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)) :=
    (differentiable_symmetrizedCompactLaplaceWeight hf.continuous hfsupp).continuous.comp
      (by fun_prop)
  have hrewritten :
      (fun y : ℝ =>
        symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          logDeriv Gammaℝ ((c : ℂ) + y * I)) =
      (fun y : ℝ =>
        symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          (-(Real.log Real.pi : ℂ) / 2 +
            digamma (((c : ℂ) + y * I) / 2) / 2)) := by
    funext y
    rw [logDeriv_GammaR_eq_digamma (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      exact hc0)]
  rw [hrewritten]
  refine MeasureTheory.Integrable.mono'
    ((integrable_one_add_abs_mul_norm_symmetrizedCompactLaplaceWeight_vertical
      hf hfsupp c).const_mul (|Real.log Real.pi| + C))
    (hweightContinuous.mul
      (continuous_const.add (hdigammaContinuous.div_const (2 : ℂ)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  calc
    ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
        ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
      ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
        ((|Real.log Real.pi| + C) * (|y| + 1)) := by
      gcongr
      exact hlogGamma y
    _ = (|Real.log Real.pi| + C) *
        ((|y| + 1) *
          ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖) := by ring

/-- On every selected finite right edge, the compact xi integral splits into its pole,
real-place, and von-Mangoldt contributions. -/
theorem compactSymmetrizedXiRightVerticalIntegral_eq_arithmetic_truncations
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) (n : ℕ) :
    selectedXiRightVerticalIntegralFor (symmetrizedCompactLaplaceWeight f) c n =
      selectedXiPoleRightVerticalIntegralFor
          (symmetrizedCompactLaplaceWeight f) c n +
        (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let T : ℝ := gaussianXiSelectedHeight c n
  have hpole : IntervalIntegrable (fun y : ℝ =>
      selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
        ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_compactSymmetrizedXiPolePair hf hfsupp hc).intervalIntegrable
  have harch : IntervalIntegrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_compactSymmetrizedXiArchimedean hf hfsupp hc).intervalIntegrable
  have hprime : IntervalIntegrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_symmetrizedCompactLaplace_mul_vonMangoldtLSeries
      hf hfsupp hc).intervalIntegrable
  have hpoint (y : ℝ) :
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
          logDeriv riemannXi ((c : ℂ) + y * I) =
        selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
            ((c : ℂ) + y * I) +
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
    rw [logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
      (by simpa using hc)]
    unfold selectedXiPolePairIntegrandFor
    simp only [sub_zero, div_eq_mul_inv]
    ring
  rw [selectedXiRightVerticalIntegralFor, selectedXiPoleRightVerticalIntegralFor]
  change
    (∫ y : ℝ in -T..T,
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) = _
  calc
    (∫ y : ℝ in -T..T,
      symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) =
      ∫ y : ℝ in -T..T,
        selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
            ((c : ℂ) + y * I) +
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = (∫ y : ℝ in -T..T,
          selectedXiPolePairIntegrandFor (symmetrizedCompactLaplaceWeight f)
            ((c : ℂ) + y * I)) +
        (∫ y : ℝ in -T..T,
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -T..T,
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
      rw [intervalIntegral.integral_sub (hpole.add harch) hprime,
        intervalIntegral.integral_add hpole harch]

theorem tendsto_selectedCompactSymmetrizedXiArchimedeanIntegral
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I))
      atTop (𝓝 (compactSymmetrizedXiArchimedeanIntegral f c)) := by
  simpa only [compactSymmetrizedXiArchimedeanIntegral] using
    tendsto_selectedGaussianXiSymmetricIntervalIntegral
      (integrable_compactSymmetrizedXiArchimedean hf hfsupp hc)

theorem tendsto_selectedCompactSymmetrizedXiPrimeIntegral
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))
      atTop (𝓝 (∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n)) := by
  rw [tsum_compactSymmetrizedVonMangoldtWeight_eq_integral hf hfsupp hc]
  exact tendsto_selectedGaussianXiSymmetricIntervalIntegral
    (integrable_symmetrizedCompactLaplace_mul_vonMangoldtLSeries hf hfsupp hc)

/-- Weil's arithmetic explicit formula for every smooth compactly supported logarithmic test
function after reflection symmetrization. -/
theorem symmetrizedCompactLaplaceXi_arithmetic_explicit_formula
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hfsupp : HasCompactSupport f) {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) * ∑' p : RiemannXiDivisorZeroIndex,
        symmetrizedCompactLaplaceWeight f
          (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1 +
        compactSymmetrizedXiArchimedeanIntegral f c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n := by
  have hpole := tendsto_compactSymmetrizedXiPoleRightVerticalIntegral
    hf hfsupp hc
  have harch := tendsto_selectedCompactSymmetrizedXiArchimedeanIntegral
    hf hfsupp hc
  have hprime := tendsto_selectedCompactSymmetrizedXiPrimeIntegral
    hf hfsupp hc
  have harithmetic := (hpole.add harch).sub hprime
  have hright : Tendsto
      (selectedXiRightVerticalIntegralFor (symmetrizedCompactLaplaceWeight f) c)
      atTop
      (𝓝 (2 * (Real.pi : ℂ) * symmetrizedCompactLaplaceWeight f 1 +
        compactSymmetrizedXiArchimedeanIntegral f c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight f n)) := by
    apply harithmetic.congr'
    exact Filter.Eventually.of_forall fun n =>
      (compactSymmetrizedXiRightVerticalIntegral_eq_arithmetic_truncations
        hf hfsupp hc n).symm
  exact tendsto_nhds_unique
    (tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral hf hfsupp hc) hright

end

end LeanLab.Riemann
