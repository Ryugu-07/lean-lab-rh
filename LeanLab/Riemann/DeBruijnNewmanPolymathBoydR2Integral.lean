import LeanLab.Riemann.DeBruijnNewmanPolymathBoydStirlingRemainder
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Boyd's integral representation for the second scaled-Gamma remainder

This module specializes the Boyd--Nemes resurgence kernels to `N = 2`.  It first records the
denominator geometry and the exact imaginary-axis norm identity needed to justify the two
Bochner integrals in Nemes equation (15).  The equality with the project's `R_2` remains the
contour-deformation obligation of the active proof campaign.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory Real Set
open scoped ComplexConjugate Real Topology

noncomputable section

/-- The positive-imaginary-axis kernel in Boyd--Nemes equation (15), specialized to `N = 2`. -/
def deBruijnNewmanPolymathBoydR2PlusIntegrand (z : ℂ) (s : ℝ) : ℂ :=
  (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
      deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I)) /
    (1 - (s : ℂ) * Complex.I / z)

/-- The negative-imaginary-axis kernel in Boyd--Nemes equation (15), specialized to `N = 2`. -/
def deBruijnNewmanPolymathBoydR2MinusIntegrand (z : ℂ) (s : ℝ) : ℂ :=
  (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
      deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I)) /
    (1 + (s : ℂ) * Complex.I / z)

/-- The source-exact right-hand side of Boyd--Nemes equation (15) at `N = 2`. -/
def deBruijnNewmanPolymathBoydR2Integral (z : ℂ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) * (Complex.I ^ 2 / z ^ 2) *
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2PlusIntegrand z s) -
    (1 / (2 * Real.pi * Complex.I)) * ((-Complex.I) ^ 2 / z ^ 2) *
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2MinusIntegrand z s)

/-- The exact statement still requiring Boyd's contour deformation. -/
def deBruijnNewmanPolymathBoydR2RepresentationAt (z : ℂ) : Prop :=
  deBruijnNewmanPolymathGammaStirlingR2 z =
    deBruijnNewmanPolymathBoydR2Integral z

theorem deBruijnNewmanPolymathBoydR2Integral_eq
    (z : ℂ) :
    deBruijnNewmanPolymathBoydR2Integral z =
      ((∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2MinusIntegrand z s) -
        (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2PlusIntegrand z s)) /
          (2 * Real.pi * Complex.I * z ^ 2) := by
  have hnegI : (-Complex.I) ^ 2 = (-1 : ℂ) := by
    calc
      (-Complex.I) ^ 2 = Complex.I ^ 2 := by ring
      _ = -1 := Complex.I_sq
  unfold deBruijnNewmanPolymathBoydR2Integral
  rw [Complex.I_sq, hnegI]
  ring

theorem deBruijnNewmanPolymathScaledGamma_differentiableAt
    {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (hnotpole : ∀ m : ℕ, z ≠ -m) :
    DifferentiableAt ℂ deBruijnNewmanPolymathScaledGamma z := by
  unfold deBruijnNewmanPolymathScaledGamma
  exact (Complex.differentiableAt_Gamma z hnotpole).div
    (deBruijnNewmanPolymathGammaStirlingMain_differentiableAt hz)
    (deBruijnNewmanPolymathGammaStirlingMain_ne_zero z)

theorem deBruijnNewmanPolymathScaledGamma_I_continuousAt
    {s : ℝ} (hs : 0 < s) :
    ContinuousAt
      (fun t : ℝ => deBruijnNewmanPolymathScaledGamma ((t : ℂ) * Complex.I)) s := by
  have harg : ContinuousAt (fun t : ℝ => (t : ℂ) * Complex.I) s :=
    (Complex.continuous_ofReal.mul continuous_const).continuousAt
  have hscaled : ContinuousAt deBruijnNewmanPolymathScaledGamma
      ((s : ℂ) * Complex.I) := by
    apply (deBruijnNewmanPolymathScaledGamma_differentiableAt
      (Or.inr (by simpa using hs.ne')) ?_).continuousAt
    intro m hm
    have him := congrArg Complex.im hm
    exact hs.ne' (by simpa using him)
  exact ContinuousAt.comp' (f := fun t : ℝ => (t : ℂ) * Complex.I) hscaled harg

theorem deBruijnNewmanPolymathScaledGamma_neg_I_continuousAt
    {s : ℝ} (hs : 0 < s) :
    ContinuousAt
      (fun t : ℝ => deBruijnNewmanPolymathScaledGamma (-(t : ℂ) * Complex.I)) s := by
  have harg : ContinuousAt (fun t : ℝ => -(t : ℂ) * Complex.I) s :=
    (Complex.continuous_ofReal.neg.mul continuous_const).continuousAt
  have hscaled : ContinuousAt deBruijnNewmanPolymathScaledGamma
      (-(s : ℂ) * Complex.I) := by
    apply (deBruijnNewmanPolymathScaledGamma_differentiableAt
      (Or.inr (by simpa using hs.ne')) ?_).continuousAt
    intro m hm
    have him := congrArg Complex.im hm
    exact hs.ne' (by simpa using him)
  exact ContinuousAt.comp' (f := fun t : ℝ => -(t : ℂ) * Complex.I) hscaled harg

theorem deBruijnNewmanPolymathBoydR2_one_sub_eq_div
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    (1 : ℂ) - (s : ℂ) * Complex.I / z =
      (z - (s : ℂ) * Complex.I) / z := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  field_simp

theorem deBruijnNewmanPolymathBoydR2_one_add_eq_div
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    (1 : ℂ) + (s : ℂ) * Complex.I / z =
      (z + (s : ℂ) * Complex.I) / z := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  field_simp

/-- On the right half-plane, neither Boyd kernel denominator can approach zero along its ray. -/
theorem deBruijnNewmanPolymathBoydR2_re_div_norm_le_norm_one_sub
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    z.re / ‖z‖ ≤ ‖(1 : ℂ) - (s : ℂ) * Complex.I / z‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  rw [deBruijnNewmanPolymathBoydR2_one_sub_eq_div hz, norm_div]
  apply (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hz0)).2
  simpa using Complex.re_le_norm (z - (s : ℂ) * Complex.I)

theorem deBruijnNewmanPolymathBoydR2_re_div_norm_le_norm_one_add
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    z.re / ‖z‖ ≤ ‖(1 : ℂ) + (s : ℂ) * Complex.I / z‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  rw [deBruijnNewmanPolymathBoydR2_one_add_eq_div hz, norm_div]
  apply (div_le_div_iff_of_pos_right (norm_pos_iff.mpr hz0)).2
  simpa using Complex.re_le_norm (z + (s : ℂ) * Complex.I)

theorem deBruijnNewmanPolymathBoydR2_one_sub_ne_zero
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    (1 : ℂ) - (s : ℂ) * Complex.I / z ≠ 0 := by
  have hpos : 0 < z.re / ‖z‖ := div_pos hz (norm_pos_iff.mpr (by
    intro h
    simp [h] at hz))
  exact norm_ne_zero_iff.mp (ne_of_gt
    (hpos.trans_le (deBruijnNewmanPolymathBoydR2_re_div_norm_le_norm_one_sub hz s)))

theorem deBruijnNewmanPolymathBoydR2_one_add_ne_zero
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    (1 : ℂ) + (s : ℂ) * Complex.I / z ≠ 0 := by
  have hpos : 0 < z.re / ‖z‖ := div_pos hz (norm_pos_iff.mpr (by
    intro h
    simp [h] at hz))
  exact norm_ne_zero_iff.mp (ne_of_gt
    (hpos.trans_le (deBruijnNewmanPolymathBoydR2_re_div_norm_le_norm_one_add hz s)))

theorem deBruijnNewmanPolymathBoydR2_one_sub_inv_norm_le
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    ‖((1 : ℂ) - (s : ℂ) * Complex.I / z)⁻¹‖ ≤ ‖z‖ / z.re := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hnormz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hdenNe := deBruijnNewmanPolymathBoydR2_one_sub_ne_zero hz s
  have hdenNorm : 0 < ‖(1 : ℂ) - (s : ℂ) * Complex.I / z‖ :=
    norm_pos_iff.mpr hdenNe
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ hdenNorm).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hz).2
  simpa [mul_comm] using (div_le_iff₀ hnormz).1
    (deBruijnNewmanPolymathBoydR2_re_div_norm_le_norm_one_sub hz s)

theorem deBruijnNewmanPolymathBoydR2_one_add_inv_norm_le
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    ‖((1 : ℂ) + (s : ℂ) * Complex.I / z)⁻¹‖ ≤ ‖z‖ / z.re := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hnormz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hdenNe := deBruijnNewmanPolymathBoydR2_one_add_ne_zero hz s
  have hdenNorm : 0 < ‖(1 : ℂ) + (s : ℂ) * Complex.I / z‖ :=
    norm_pos_iff.mpr hdenNe
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ hdenNorm).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hz).2
  simpa [mul_comm] using (div_le_iff₀ hnormz).1
    (deBruijnNewmanPolymathBoydR2_re_div_norm_le_norm_one_add hz s)

/-- Exact cancellation of the apparent singularity in the `N = 2` ray weight. -/
theorem deBruijnNewmanPolymathBoydR2_weight_norm_sq
    {s : ℝ} (hs : 0 < s) :
    ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ ^ 2 =
      (s * Real.exp (-2 * Real.pi * s)) ^ 2 /
        (1 - Real.exp (-2 * Real.pi * s)) := by
  rw [norm_mul, norm_real, Real.norm_of_nonneg (mul_nonneg hs.le (Real.exp_pos _).le),
    mul_pow, deBruijnNewmanPolymathScaledGamma_norm_sq_I hs]
  simp only [div_eq_mul_inv, one_mul]

theorem real_mul_exp_neg_le_one_sub_exp_neg (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have hmul : (x + 1) * Real.exp (-x) ≤ 1 := by
    calc
      (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add]; simp
  linarith [Real.exp_pos (-x)]

theorem deBruijnNewmanPolymathBoydR2_weight_sq_le
    {s : ℝ} (hs : 0 < s) :
    ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ ^ 2 ≤
      s * Real.exp (-2 * Real.pi * s) := by
  have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hscale :
      s * Real.exp (-2 * Real.pi * s) ≤
        (2 * Real.pi * s) * Real.exp (-(2 * Real.pi * s)) := by
    rw [show -2 * Real.pi * s = -(2 * Real.pi * s) by ring]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)
  have hdenLower :
      s * Real.exp (-2 * Real.pi * s) ≤
        1 - Real.exp (-2 * Real.pi * s) := by
    exact hscale.trans (by
      simpa [mul_assoc] using real_mul_exp_neg_le_one_sub_exp_neg (2 * Real.pi * s))
  have hdenPos : 0 < 1 - Real.exp (-2 * Real.pi * s) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  rw [deBruijnNewmanPolymathBoydR2_weight_norm_sq hs]
  apply (div_le_iff₀ hdenPos).2
  have hweightNonneg : 0 ≤ s * Real.exp (-2 * Real.pi * s) :=
    mul_nonneg hs.le (Real.exp_pos _).le
  nlinarith

/-- The ray weight is globally dominated by an elementary integrable function. -/
theorem deBruijnNewmanPolymathBoydR2_weight_norm_le
    {s : ℝ} (hs : 0 < s) :
    ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ ≤
      Real.sqrt s * Real.exp (-Real.pi * s) := by
  have hsquare := deBruijnNewmanPolymathBoydR2_weight_sq_le hs
  have hrhsSq :
      (Real.sqrt s * Real.exp (-Real.pi * s)) ^ 2 =
        s * Real.exp (-2 * Real.pi * s) := by
    rw [mul_pow, Real.sq_sqrt hs.le, pow_two, ← Real.exp_add]
    congr 2
    ring
  have hrhsNonneg : 0 ≤ Real.sqrt s * Real.exp (-Real.pi * s) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  exact (sq_le_sq₀ (norm_nonneg _) hrhsNonneg).mp (hsquare.trans_eq hrhsSq.symm)

theorem deBruijnNewmanPolymathBoydR2_majorant_integrableOn :
    IntegrableOn (fun s : ℝ => Real.sqrt s * Real.exp (-Real.pi * s)) (Ioi 0) := by
  simpa [Real.sqrt_eq_rpow, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (1 / 2 : ℝ)) (p := (1 : ℝ)) (b := Real.pi)
      (by norm_num) (by norm_num) Real.pi_pos)

theorem deBruijnNewmanPolymathBoydR2_plusWeight_continuousOn :
    ContinuousOn
      (fun s : ℝ => (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))) (Ioi 0) := by
  intro s hs
  have hspos : 0 < s := hs
  have hscalar : ContinuousAt
      (fun t : ℝ => ((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ)) s := by
    fun_prop
  exact (hscalar.mul
    (deBruijnNewmanPolymathScaledGamma_I_continuousAt hspos)).continuousWithinAt

theorem deBruijnNewmanPolymathBoydR2_minusWeight_continuousOn :
    ContinuousOn
      (fun s : ℝ => (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I))) (Ioi 0) := by
  intro s hs
  have hspos : 0 < s := hs
  have hscalar : ContinuousAt
      (fun t : ℝ => ((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ)) s := by
    fun_prop
  exact (hscalar.mul
    (deBruijnNewmanPolymathScaledGamma_neg_I_continuousAt hspos)).continuousWithinAt

theorem deBruijnNewmanPolymathBoydR2_minusWeight_norm_eq
    {s : ℝ} (hs : 0 < s) :
    ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I))‖ =
      ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ := by
  have hconj := deBruijnNewmanPolymathScaledGamma_conj
    (z := (s : ℂ) * Complex.I) (by simpa using hs.ne')
  rw [show conj ((s : ℂ) * Complex.I) = -(s : ℂ) * Complex.I by simp] at hconj
  rw [hconj, norm_mul, norm_mul, norm_conj]

theorem deBruijnNewmanPolymathBoydR2_plusWeight_integrableOn :
    IntegrableOn
      (fun s : ℝ => (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))) (Ioi 0) := by
  refine deBruijnNewmanPolymathBoydR2_majorant_integrableOn.mono'
    (deBruijnNewmanPolymathBoydR2_plusWeight_continuousOn.aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact deBruijnNewmanPolymathBoydR2_weight_norm_le hs

theorem deBruijnNewmanPolymathBoydR2_minusWeight_integrableOn :
    IntegrableOn
      (fun s : ℝ => (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I))) (Ioi 0) := by
  refine deBruijnNewmanPolymathBoydR2_majorant_integrableOn.mono'
    (deBruijnNewmanPolymathBoydR2_minusWeight_continuousOn.aestronglyMeasurable
      measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [deBruijnNewmanPolymathBoydR2_minusWeight_norm_eq hs]
  exact deBruijnNewmanPolymathBoydR2_weight_norm_le hs

theorem deBruijnNewmanPolymathBoydR2PlusIntegrand_continuousOn
    {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (deBruijnNewmanPolymathBoydR2PlusIntegrand z) (Ioi 0) := by
  intro s hs
  have hspos : 0 < s := hs
  have hscalar : ContinuousAt
      (fun t : ℝ => ((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ)) s := by
    fun_prop
  have hnum := hscalar.mul
    (deBruijnNewmanPolymathScaledGamma_I_continuousAt hspos)
  have hden : ContinuousAt
      (fun t : ℝ => (1 : ℂ) - (t : ℂ) * Complex.I / z) s := by
    fun_prop
  exact (hnum.div hden
    (deBruijnNewmanPolymathBoydR2_one_sub_ne_zero hz s)).continuousWithinAt

theorem deBruijnNewmanPolymathBoydR2MinusIntegrand_continuousOn
    {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (deBruijnNewmanPolymathBoydR2MinusIntegrand z) (Ioi 0) := by
  intro s hs
  have hspos : 0 < s := hs
  have hscalar : ContinuousAt
      (fun t : ℝ => ((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ)) s := by
    fun_prop
  have hnum := hscalar.mul
    (deBruijnNewmanPolymathScaledGamma_neg_I_continuousAt hspos)
  have hden : ContinuousAt
      (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I / z) s := by
    fun_prop
  exact (hnum.div hden
    (deBruijnNewmanPolymathBoydR2_one_add_ne_zero hz s)).continuousWithinAt

theorem deBruijnNewmanPolymathBoydR2PlusIntegrand_norm_le
    {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    ‖deBruijnNewmanPolymathBoydR2PlusIntegrand z s‖ ≤
      (‖z‖ / z.re) * (Real.sqrt s * Real.exp (-Real.pi * s)) := by
  rw [deBruijnNewmanPolymathBoydR2PlusIntegrand, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
          deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ *
        (‖z‖ / z.re) :=
      mul_le_mul_of_nonneg_left
        (deBruijnNewmanPolymathBoydR2_one_sub_inv_norm_le hz s) (norm_nonneg _)
    _ ≤ (Real.sqrt s * Real.exp (-Real.pi * s)) * (‖z‖ / z.re) :=
      mul_le_mul_of_nonneg_right
        (deBruijnNewmanPolymathBoydR2_weight_norm_le hs) (by positivity)
    _ = _ := by ring

theorem deBruijnNewmanPolymathBoydR2MinusIntegrand_norm_le
    {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    ‖deBruijnNewmanPolymathBoydR2MinusIntegrand z s‖ ≤
      (‖z‖ / z.re) * (Real.sqrt s * Real.exp (-Real.pi * s)) := by
  rw [deBruijnNewmanPolymathBoydR2MinusIntegrand, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
          deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I))‖ *
        (‖z‖ / z.re) :=
      mul_le_mul_of_nonneg_left
        (deBruijnNewmanPolymathBoydR2_one_add_inv_norm_le hz s) (norm_nonneg _)
    _ = ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
          deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ *
        (‖z‖ / z.re) := by
      rw [deBruijnNewmanPolymathBoydR2_minusWeight_norm_eq hs]
    _ ≤ (Real.sqrt s * Real.exp (-Real.pi * s)) * (‖z‖ / z.re) :=
      mul_le_mul_of_nonneg_right
        (deBruijnNewmanPolymathBoydR2_weight_norm_le hs) (by positivity)
    _ = _ := by ring

/-- Both actual `N = 2` Boyd kernels are Bochner integrable on the positive ray. -/
theorem deBruijnNewmanPolymathBoydR2_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathBoydR2PlusIntegrand z) (Ioi 0) ∧
      IntegrableOn (deBruijnNewmanPolymathBoydR2MinusIntegrand z) (Ioi 0) := by
  have hmajor : IntegrableOn
      (fun s : ℝ => (‖z‖ / z.re) *
        (Real.sqrt s * Real.exp (-Real.pi * s))) (Ioi 0) :=
    deBruijnNewmanPolymathBoydR2_majorant_integrableOn.const_mul (‖z‖ / z.re)
  constructor
  · refine hmajor.mono'
      ((deBruijnNewmanPolymathBoydR2PlusIntegrand_continuousOn hz).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact deBruijnNewmanPolymathBoydR2PlusIntegrand_norm_le hz hs
  · refine hmajor.mono'
      ((deBruijnNewmanPolymathBoydR2MinusIntegrand_continuousOn hz).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact deBruijnNewmanPolymathBoydR2MinusIntegrand_norm_le hz hs

theorem deBruijnNewmanPolymathBoydR2MinusIntegrand_ofReal
    {x s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathBoydR2MinusIntegrand (x : ℂ) s =
      conj (deBruijnNewmanPolymathBoydR2PlusIntegrand (x : ℂ) s) := by
  have hconj := deBruijnNewmanPolymathScaledGamma_conj
    (z := (s : ℂ) * Complex.I) (by simpa using hs.ne')
  rw [show conj ((s : ℂ) * Complex.I) = -(s : ℂ) * Complex.I by simp] at hconj
  unfold deBruijnNewmanPolymathBoydR2MinusIntegrand
    deBruijnNewmanPolymathBoydR2PlusIntegrand
  rw [hconj]
  simp only [map_div₀, map_mul, conj_ofReal, map_sub, map_one, conj_I]
  ring

theorem deBruijnNewmanPolymathBoydR2_minusIntegral_ofReal (x : ℝ) :
    (∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2MinusIntegrand (x : ℂ) s) =
      conj (∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2PlusIntegrand (x : ℂ) s) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact deBruijnNewmanPolymathBoydR2MinusIntegrand_ofReal hs

/-- On the positive real axis, the two-ray Boyd expression is one real scalar integral. -/
theorem deBruijnNewmanPolymathBoydR2Integral_ofReal (x : ℝ) :
    deBruijnNewmanPolymathBoydR2Integral (x : ℂ) =
      -(((∫ s : ℝ in Ioi 0,
          deBruijnNewmanPolymathBoydR2PlusIntegrand (x : ℂ) s).im : ℝ) : ℂ) /
        (Real.pi * (x : ℂ) ^ 2) := by
  let P : ℂ := ∫ s : ℝ in Ioi 0,
    deBruijnNewmanPolymathBoydR2PlusIntegrand (x : ℂ) s
  have hconjSub : conj P - P = -2 * (P.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [deBruijnNewmanPolymathBoydR2Integral_eq,
    deBruijnNewmanPolymathBoydR2_minusIntegral_ofReal]
  change (conj P - P) / (2 * Real.pi * Complex.I * (x : ℂ) ^ 2) =
    -(P.im : ℂ) / (Real.pi * (x : ℂ) ^ 2)
  rw [hconjSub]
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring_nf
  rw [Complex.I_sq]
  ring

end

end LeanLab.Riemann
