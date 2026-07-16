import LeanLab.Riemann.DeBruijnNewmanHeat
import LeanLab.Riemann.LiScaffold

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Reverse-heat Li transfer audit

This module gives an exact polynomial countermodel to generic backward transfer of positive-time
critical-line zeros or Li positivity. It does not model the theta kernel and does not address RH.
-/

open Complex

namespace LeanLab.Riemann

noncomputable section

/-- A reflection-symmetric polynomial family satisfying the heat equation in the `s` variable. -/
def h6AuditHeatXiQuadratic (t s : ℂ) : ℂ :=
  (s - 1 / 2) ^ 2 - 1 / 16 + t / 2

/-- The standard second Li expression, written through the logarithmic derivative at `1`. -/
def h6AuditSecondLiValue (f : ℂ → ℂ) : ℂ :=
  2 * logDeriv f 1 + deriv (logDeriv f) 1

theorem hasDerivAt_h6AuditHeatXiQuadratic_time (t s : ℂ) :
    HasDerivAt (fun u : ℂ ↦ h6AuditHeatXiQuadratic u s) (1 / 2) t := by
  simpa [h6AuditHeatXiQuadratic, id_eq] using
    ((hasDerivAt_id t).div_const (2 : ℂ)).const_add
      ((s - 1 / 2) ^ 2 - 1 / 16)

theorem differentiable_h6AuditHeatXiQuadratic_time (s : ℂ) :
    Differentiable ℂ (fun t : ℂ ↦ h6AuditHeatXiQuadratic t s) :=
  fun t ↦ (hasDerivAt_h6AuditHeatXiQuadratic_time t s).differentiableAt

theorem hasDerivAt_h6AuditHeatXiQuadratic_spatial (t s : ℂ) :
    HasDerivAt (h6AuditHeatXiQuadratic t) (2 * (s - 1 / 2)) s := by
  have hraw := (((((hasDerivAt_id s).sub_const (1 / 2)).pow 2).sub_const
    (1 / 16)).add_const (t / 2))
  unfold h6AuditHeatXiQuadratic
  refine (hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ ?_)).congr_deriv ?_
  · simp only [Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

theorem differentiable_h6AuditHeatXiQuadratic_spatial (t : ℂ) :
    Differentiable ℂ (h6AuditHeatXiQuadratic t) :=
  fun s ↦ (hasDerivAt_h6AuditHeatXiQuadratic_spatial t s).differentiableAt

theorem deriv_h6AuditHeatXiQuadratic_spatial (t s : ℂ) :
    deriv (h6AuditHeatXiQuadratic t) s = 2 * (s - 1 / 2) :=
  (hasDerivAt_h6AuditHeatXiQuadratic_spatial t s).deriv

theorem deriv_deriv_h6AuditHeatXiQuadratic_spatial (t s : ℂ) :
    deriv (deriv (h6AuditHeatXiQuadratic t)) s = 2 := by
  have hderiv : deriv (h6AuditHeatXiQuadratic t) = fun z : ℂ ↦ 2 * (z - 1 / 2) := by
    funext z
    exact deriv_h6AuditHeatXiQuadratic_spatial t z
  rw [hderiv]
  simp

theorem h6AuditHeatXiQuadratic_reflection (t s : ℂ) :
    h6AuditHeatXiQuadratic t (1 - s) = h6AuditHeatXiQuadratic t s := by
  simp only [h6AuditHeatXiQuadratic]
  ring

theorem h6AuditHeatXiQuadratic_heatEquation (t s : ℂ) :
    deriv (fun u : ℂ ↦ h6AuditHeatXiQuadratic u s) t =
      (1 / 4) * deriv (deriv (h6AuditHeatXiQuadratic t)) s := by
  rw [(hasDerivAt_h6AuditHeatXiQuadratic_time t s).deriv,
    deriv_deriv_h6AuditHeatXiQuadratic_spatial]
  norm_num

theorem h6AuditHeatXiQuadratic_one_ne_zero_of_nonneg
    (t : ℝ) (ht : 0 ≤ t) :
    h6AuditHeatXiQuadratic t 1 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  norm_num [h6AuditHeatXiQuadratic] at hre
  linarith

theorem h6AuditHeatXiQuadratic_one_allZerosOnCriticalLine :
    ∀ s : ℂ, h6AuditHeatXiQuadratic 1 s = 0 → OnCriticalLine s := by
  intro s hs
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  norm_num [h6AuditHeatXiQuadratic, pow_two, Complex.mul_re, Complex.mul_im] at hre him
  have hprod : (s.re - 1 / 2) * s.im = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hprod with hreal | himag
  · rw [OnCriticalLine]
    linarith
  · have hsq : 0 ≤ (s.re - 1 / 2) ^ 2 := sq_nonneg _
    nlinarith

theorem h6AuditHeatXiQuadratic_zero_offLine_witness :
    h6AuditHeatXiQuadratic 0 (3 / 4) = 0 ∧ ¬ OnCriticalLine (3 / 4 : ℂ) := by
  constructor
  · norm_num [h6AuditHeatXiQuadratic]
  · norm_num [OnCriticalLine]

private theorem h6AuditHeatXiQuadratic_one_value (t : ℂ) :
    h6AuditHeatXiQuadratic t 1 = 3 / 16 + t / 2 := by
  simp only [h6AuditHeatXiQuadratic]
  ring

private theorem logDeriv_h6AuditHeatXiQuadratic (t s : ℂ) :
    logDeriv (h6AuditHeatXiQuadratic t) s =
      (2 * (s - 1 / 2)) / h6AuditHeatXiQuadratic t s := by
  rw [logDeriv_apply, deriv_h6AuditHeatXiQuadratic_spatial]

private theorem hasDerivAt_logDeriv_h6AuditHeatXiQuadratic_one
    (t : ℂ) (ht : 3 / 16 + t / 2 ≠ 0) :
    HasDerivAt (logDeriv (h6AuditHeatXiQuadratic t))
      ((2 * (3 / 16 + t / 2) - 1) / (3 / 16 + t / 2) ^ 2) 1 := by
  have hnum : HasDerivAt (fun s : ℂ ↦ 2 * (s - 1 / 2)) 2 1 := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (1 : ℂ)).sub_const (1 / 2)).const_mul (2 : ℂ)
  have hden := hasDerivAt_h6AuditHeatXiQuadratic_spatial t 1
  have hdenNe : h6AuditHeatXiQuadratic t 1 ≠ 0 := by
    rw [h6AuditHeatXiQuadratic_one_value]
    exact ht
  have hquot := hnum.div hden hdenNe
  have heq : logDeriv (h6AuditHeatXiQuadratic t) =
      fun s : ℂ ↦ (2 * (s - 1 / 2)) / h6AuditHeatXiQuadratic t s := by
    funext s
    exact logDeriv_h6AuditHeatXiQuadratic t s
  rw [heq]
  have hcoeff :
      ((2 * h6AuditHeatXiQuadratic t 1 -
          2 * (1 - 1 / 2) * (2 * (1 - 1 / 2))) /
        h6AuditHeatXiQuadratic t 1 ^ 2) =
        ((2 * (3 / 16 + t / 2) - 1) / (3 / 16 + t / 2) ^ 2) := by
    rw [h6AuditHeatXiQuadratic_one_value]
    norm_num
  rw [← hcoeff]
  exact hquot

private theorem h6AuditSecondLiValue_eq
    (t : ℂ) (ht : 3 / 16 + t / 2 ≠ 0) :
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic t) =
      (2 * t - 1 / 4) / (3 / 16 + t / 2) ^ 2 := by
  rw [h6AuditSecondLiValue,
    (hasDerivAt_logDeriv_h6AuditHeatXiQuadratic_one t ht).deriv,
    logDeriv_h6AuditHeatXiQuadratic, h6AuditHeatXiQuadratic_one_value]
  field_simp [ht]
  ring

theorem h6AuditSecondLiValue_zero :
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 0) = -64 / 9 := by
  rw [h6AuditSecondLiValue_eq]
  · norm_num
  · norm_num

theorem h6AuditSecondLiValue_one :
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 1) = 448 / 121 := by
  rw [h6AuditSecondLiValue_eq]
  · norm_num
  · norm_num

/-- The registered polynomial satisfies all generic structural premises but reverses Li sign. -/
theorem h6AuditHeatXiQuadratic_falsifies_reverseLiTransfer :
    (∀ s : ℂ, Differentiable ℂ (fun t : ℂ ↦ h6AuditHeatXiQuadratic t s)) ∧
    (∀ t : ℂ, Differentiable ℂ (h6AuditHeatXiQuadratic t)) ∧
    (∀ t s : ℂ, h6AuditHeatXiQuadratic t (1 - s) = h6AuditHeatXiQuadratic t s) ∧
    (∀ t s : ℂ, deriv (fun u : ℂ ↦ h6AuditHeatXiQuadratic u s) t =
      (1 / 4) * deriv (deriv (h6AuditHeatXiQuadratic t)) s) ∧
    (∀ t : ℝ, 0 ≤ t → h6AuditHeatXiQuadratic t 1 ≠ 0) ∧
    (∀ s : ℂ, h6AuditHeatXiQuadratic 1 s = 0 → OnCriticalLine s) ∧
    (h6AuditHeatXiQuadratic 0 (3 / 4) = 0 ∧ ¬ OnCriticalLine (3 / 4 : ℂ)) ∧
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 0) = -64 / 9 ∧
    h6AuditSecondLiValue (h6AuditHeatXiQuadratic 1) = 448 / 121 := by
  exact ⟨differentiable_h6AuditHeatXiQuadratic_time,
    differentiable_h6AuditHeatXiQuadratic_spatial,
    h6AuditHeatXiQuadratic_reflection,
    h6AuditHeatXiQuadratic_heatEquation,
    h6AuditHeatXiQuadratic_one_ne_zero_of_nonneg,
    h6AuditHeatXiQuadratic_one_allZerosOnCriticalLine,
    h6AuditHeatXiQuadratic_zero_offLine_witness,
    h6AuditSecondLiValue_zero,
    h6AuditSecondLiValue_one⟩

end

end LeanLab.Riemann
