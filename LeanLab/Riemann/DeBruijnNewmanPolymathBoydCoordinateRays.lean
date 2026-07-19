import LeanLab.Riemann.DeBruijnNewmanPolymathBoydAdjacentContour
import Mathlib.Topology.Algebra.Field

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Radial coordinate lifts of the adjacent Boyd contours

This module proves that the normalized principal Boyd coordinate maps the two adjacent phase
contours onto the radial segments ending at the first two critical images. It does not construct a
two-dimensional saddle domain or a disk-wide inverse branch.
-/

namespace LeanLab.Riemann

open Complex Filter Set
open scoped Topology

noncomputable section

/-- Radial scaling of an integer critical image by phase magnitude. -/
def deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (n : ℤ) (t : ℝ) : ℂ :=
  ((Real.sqrt t / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    deBruijnNewmanPolymathBoydComplexSaddleImage n

/-- The actual normalized coordinate evaluated on the upper adjacent phase lift. -/
def deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift (t : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))

/-- The actual normalized coordinate evaluated on the lower adjacent phase lift. -/
def deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift (t : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_re_of_phase_eq_mul_I
    {u : ℂ} {s : ℝ} (hu : u ≠ 0)
    (hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = (s : ℂ) * I) :
    (deBruijnNewmanPolymathBoydComplexSaddleFactor u).re =
      4 * s * u.re * u.im / Complex.normSq (u ^ 2) := by
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor, if_neg hu, hphase,
    Complex.div_re]
  simp [Complex.normSq, pow_two]
  ring

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_re_nonpos (s : ℝ) :
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift s).re ≤ 0 := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
    deBruijnNewmanPolymathBoydAdjacentContourPlus_re]
  exact deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos _

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_im_nonneg (s : ℝ) :
    0 ≤ (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift s).im := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
    deBruijnNewmanPolymathBoydAdjacentContourPlus_im]
  exact (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem s).1

theorem deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_re_nonpos (s : ℝ) :
    (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift s).re ≤ 0 := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift]
  simpa using deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_re_nonpos (-s)

theorem deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_im_nonpos (s : ℝ) :
    (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift s).im ≤ 0 := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift]
  simpa using neg_nonpos.mpr
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_im_nonneg (-s))

theorem deBruijnNewmanPolymathBoydAdjacentContourUpper_factor_re_nonneg
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    0 ≤ (deBruijnNewmanPolymathBoydComplexSaddleFactor
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))).re := by
  let u := deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)
  change 0 ≤ (deBruijnNewmanPolymathBoydComplexSaddleFactor u).re
  by_cases hu : u = 0
  · simp [hu]
  have hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = ((-t : ℝ) : ℂ) * I := by
    exact deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPhaseLift
      ⟨by linarith [ht.2], neg_nonpos.mpr ht.1⟩
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor_re_of_phase_eq_mul_I hu hphase]
  apply div_nonneg
  · have htr : 0 ≤ (-t) * u.re :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ht.1)
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_re_nonpos (-t))
    have him : 0 ≤ u.im :=
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_im_nonneg (-t)
    nlinarith
  · exact Complex.normSq_nonneg _

theorem deBruijnNewmanPolymathBoydAdjacentContourLower_factor_re_nonneg
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    0 ≤ (deBruijnNewmanPolymathBoydComplexSaddleFactor
      (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)).re := by
  let u := deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t
  change 0 ≤ (deBruijnNewmanPolymathBoydComplexSaddleFactor u).re
  by_cases hu : u = 0
  · simp [hu]
  have hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = (t : ℂ) * I :=
    deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourNegativePhaseLift ht
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor_re_of_phase_eq_mul_I hu hphase]
  apply div_nonneg
  · have hxy : 0 ≤ u.re * u.im :=
      mul_nonneg_of_nonpos_of_nonpos
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_re_nonpos t)
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_im_nonpos t)
    nlinarith [ht.1]
  · exact Complex.normSq_nonneg _

theorem continuousAt_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_of_factor_re_nonneg
    {u : ℂ}
    (hfactor : 0 ≤ (deBruijnNewmanPolymathBoydComplexSaddleFactor u).re) :
    ContinuousAt deBruijnNewmanPolymathBoydComplexSaddleCoordinate u := by
  have hfactorContinuous :
      ContinuousAt deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
    by_cases hu : u = 0
    · simpa [hu] using
        deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_zero.continuousAt
    · exact
        (deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_of_ne hu).continuousAt
  have hsqrt : ContinuousAt Complex.sqrt
      (deBruijnNewmanPolymathBoydComplexSaddleFactor u) :=
    Complex.continuousAt_sqrt (Or.inl hfactor)
  unfold deBruijnNewmanPolymathBoydComplexSaddleCoordinate
  unfold deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor
  exact continuousAt_id.mul (hsqrt.comp hfactorContinuous)

theorem continuousOn_deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift :
    ContinuousOn deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift
      (Icc 0 (2 * Real.pi)) := by
  intro t ht
  change ContinuousWithinAt
    (fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)))
    (Icc 0 (2 * Real.pi)) t
  have hcoordinate :=
    continuousAt_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_of_factor_re_nonneg
      (deBruijnNewmanPolymathBoydAdjacentContourUpper_factor_re_nonneg ht)
  have hlift : ContinuousAt
      (fun r : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) t :=
    (continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift.comp
      continuous_id.neg).continuousAt
  have hcomp : ContinuousAt
      (fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r))) t :=
    ContinuousAt.comp' (f := fun r : ℝ =>
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) hcoordinate hlift
  exact hcomp.continuousWithinAt

theorem continuousOn_deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift :
    ContinuousOn deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift
      (Icc 0 (2 * Real.pi)) := by
  intro t ht
  change ContinuousWithinAt
    (fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r))
    (Icc 0 (2 * Real.pi)) t
  have hcoordinate :=
    continuousAt_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_of_factor_re_nonneg
      (deBruijnNewmanPolymathBoydAdjacentContourLower_factor_re_nonneg ht)
  exact (ContinuousAt.comp'
    (f := deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift) hcoordinate
      continuous_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift.continuousAt).continuousWithinAt

theorem continuous_deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (n : ℤ) :
    Continuous (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay n) := by
  unfold deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
  fun_prop

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_zero (n : ℤ) :
    deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay n 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay]

theorem deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_two_pi (n : ℤ) :
    deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay n (2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddleImage n := by
  have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  unfold deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
  rw [div_self hsqrt]
  simp

theorem deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_one_sq
    {t : ℝ} (ht : 0 ≤ t) :
    deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t ^ 2 =
      ((-2 * t : ℝ) : ℂ) * I := by
  have hscale : (Real.sqrt t / Real.sqrt (2 * Real.pi)) ^ 2 =
      t / (2 * Real.pi) := by
    rw [div_pow, Real.sq_sqrt ht,
      Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  rw [deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay, mul_pow,
    ← Complex.ofReal_pow, hscale, deBruijnNewmanPolymathBoydComplexSaddleImage,
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle_explicit]
  norm_num
  field_simp [Real.pi_ne_zero]
  ring

theorem deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_neg_one_sq
    {t : ℝ} (ht : 0 ≤ t) :
    deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t ^ 2 =
      ((2 * t : ℝ) : ℂ) * I := by
  have hscale : (Real.sqrt t / Real.sqrt (2 * Real.pi)) ^ 2 =
      t / (2 * Real.pi) := by
    rw [div_pow, Real.sq_sqrt ht,
      Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
  rw [deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay, mul_pow,
    ← Complex.ofReal_pow, hscale, deBruijnNewmanPolymathBoydComplexSaddleImage,
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle_explicit]
  norm_num
  field_simp [Real.pi_ne_zero]
  ring

theorem deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_sq
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift t ^ 2 =
      ((-2 * t : ℝ) : ℂ) * I := by
  have hphase := deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPhaseLift
    (s := -t) ⟨by linarith [ht.2], neg_nonpos.mpr ht.1⟩
  have hcoordinate := deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))
  rw [hphase] at hcoordinate
  unfold deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift
  push_cast at hcoordinate ⊢
  linear_combination 2 * hcoordinate

theorem deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_sq
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift t ^ 2 =
      ((2 * t : ℝ) : ℂ) * I := by
  have hphase :=
    deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourNegativePhaseLift ht
  have hcoordinate := deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq
    (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)
  rw [hphase] at hcoordinate
  unfold deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift
  push_cast at hcoordinate ⊢
  linear_combination 2 * hcoordinate

theorem deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift (2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddleImage 1 := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift,
    show -(2 * Real.pi) = -2 * Real.pi by ring,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_two_pi]
  rfl

theorem deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift (2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddleImage (-1) := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift,
    deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_two_pi]
  rfl

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_zero :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter 0 = 0 := by
  apply deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_strictMonoOn.injOn
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem 0)
    (by exact ⟨le_rfl, (mul_pos two_pos Real.pi_pos).le⟩)
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_liftParameter]
  simp [Real.pi_pos.le]

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_zero :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLift 0 = 0 := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_zero,
    deBruijnNewmanPolymathBoydAdjacentContourPlus_zero]

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_zero :
    deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift]

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_zero :
    deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift]

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_zero :
    deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift]

theorem deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_eq_radialRay
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift t =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t := by
  rcases eq_or_lt_of_le ht.1 with ht0 | htpos
  · subst t
    simp
  · have hsub : Icc t (2 * Real.pi) ⊆ Icc 0 (2 * Real.pi) := by
      intro r hr
      exact ⟨ht.1.trans hr.1, hr.2⟩
    have hsq : Set.EqOn
        (deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift ^ 2)
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 ^ 2)
        (Icc t (2 * Real.pi)) := by
      intro r hr
      change deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift r ^ 2 =
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 r ^ 2
      rw [deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_sq (hsub hr),
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_one_sq (hsub hr).1]
    have hray_ne : ∀ {r : ℝ}, r ∈ Icc t (2 * Real.pi) →
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 r ≠ 0 := by
      intro r hr
      have hrpos : 0 < r := htpos.trans_le hr.1
      have hscale : Real.sqrt r / Real.sqrt (2 * Real.pi) ≠ 0 :=
        div_ne_zero (Real.sqrt_ne_zero'.mpr hrpos) (by positivity)
      unfold deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
      exact mul_ne_zero (by exact_mod_cast hscale)
        (deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero (by norm_num))
    have hend :
        deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift (2 * Real.pi) =
          deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 (2 * Real.pi) := by
      rw [deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_two_pi,
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_two_pi]
    have hall := isPreconnected_Icc.eq_of_sq_eq
      (continuousOn_deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift.mono hsub)
      (continuous_deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1).continuousOn
      hsq hray_ne (show 2 * Real.pi ∈ Icc t (2 * Real.pi) from ⟨ht.2, le_rfl⟩) hend
    exact hall ⟨le_rfl, ht.2⟩

theorem deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_eq_radialRay
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift t =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t := by
  rcases eq_or_lt_of_le ht.1 with ht0 | htpos
  · subst t
    simp
  · have hsub : Icc t (2 * Real.pi) ⊆ Icc 0 (2 * Real.pi) := by
      intro r hr
      exact ⟨ht.1.trans hr.1, hr.2⟩
    have hsq : Set.EqOn
        (deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift ^ 2)
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) ^ 2)
        (Icc t (2 * Real.pi)) := by
      intro r hr
      change deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift r ^ 2 =
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) r ^ 2
      rw [deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_sq (hsub hr),
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_neg_one_sq (hsub hr).1]
    have hray_ne : ∀ {r : ℝ}, r ∈ Icc t (2 * Real.pi) →
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) r ≠ 0 := by
      intro r hr
      have hrpos : 0 < r := htpos.trans_le hr.1
      have hscale : Real.sqrt r / Real.sqrt (2 * Real.pi) ≠ 0 :=
        div_ne_zero (Real.sqrt_ne_zero'.mpr hrpos) (by positivity)
      unfold deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
      exact mul_ne_zero (by exact_mod_cast hscale)
        (deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero (by norm_num))
    have hend :
        deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift (2 * Real.pi) =
          deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) (2 * Real.pi) := by
      rw [deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_two_pi,
        deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_two_pi]
    have hall := isPreconnected_Icc.eq_of_sq_eq
      (continuousOn_deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift.mono hsub)
      (continuous_deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1)).continuousOn
      hsq hray_ne (show 2 * Real.pi ∈ Icc t (2 * Real.pi) from ⟨ht.2, le_rfl⟩) hend
    exact hall ⟨le_rfl, ht.2⟩

theorem norm_deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_sq
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    ‖deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift t‖ ^ 2 = 2 * t := by
  rw [← norm_pow,
    deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_sq ht]
  simp [abs_of_nonneg ht.1]

theorem norm_deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_sq
    {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    ‖deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift t‖ ^ 2 = 2 * t := by
  rw [← norm_pow,
    deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_sq ht]
  simp [abs_of_nonneg ht.1]

end

end LeanLab.Riemann
