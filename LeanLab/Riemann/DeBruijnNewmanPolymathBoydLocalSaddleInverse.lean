import LeanLab.Riemann.DeBruijnNewmanPolymathBoydLogSaddleIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.SqrtDeriv

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The normalized local Boyd saddle coordinate

This module removes the double zero of `exp u - u - 1`, constructs the normalized principal
square-root coordinate, and applies the analytic inverse-function theorem at the origin. It makes
no global branch-continuation or resurgence claim.
-/

namespace LeanLab.Riemann

open Complex Filter Set
open scoped Topology

noncomputable section

/-- Boyd's complex saddle phase after the logarithmic Gamma coordinate. -/
def deBruijnNewmanPolymathBoydComplexSaddlePhase (u : ℂ) : ℂ :=
  Complex.exp u - u - 1

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt (u : ℂ) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddlePhase u := by
  unfold deBruijnNewmanPolymathBoydComplexSaddlePhase
  fun_prop

@[simp]
theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_zero :
    deBruijnNewmanPolymathBoydComplexSaddlePhase 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydComplexSaddlePhase]

theorem deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase :
    deriv deBruijnNewmanPolymathBoydComplexSaddlePhase = fun u : ℂ => Complex.exp u - 1 := by
  funext u
  unfold deBruijnNewmanPolymathBoydComplexSaddlePhase
  rw [deriv_sub_const]
  calc
    deriv (fun z : ℂ => Complex.exp z - z) u =
        deriv (fun z : ℂ => Complex.exp z) u - deriv (fun z : ℂ => z) u :=
      deriv_fun_sub (by fun_prop) (by fun_prop)
    _ = Complex.exp u - 1 := by
      rw [(Complex.hasDerivAt_exp u).deriv, deriv_id'']

@[simp]
theorem deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_zero :
    deriv deBruijnNewmanPolymathBoydComplexSaddlePhase 0 = 0 := by
  rw [deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase]
  simp

@[simp]
theorem deriv_deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_zero :
    deriv (deriv deBruijnNewmanPolymathBoydComplexSaddlePhase) 0 = 1 := by
  rw [deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase]
  simp

theorem exists_deBruijnNewmanPolymathBoydComplexSaddleTaylorFactor :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ ∀ u : ℂ,
      deBruijnNewmanPolymathBoydComplexSaddlePhase u = u ^ 2 / 2 + u ^ 3 * F u := by
  obtain ⟨F, hF, hEq⟩ :=
    (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt 0).exists_eq_sum_add_pow_mul 3
  refine ⟨F, hF, fun u => ?_⟩
  rw [hEq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.factorial_two, Nat.cast_one, Nat.cast_ofNat, div_one,
    iteratedDeriv_zero, iteratedDeriv_succ', smul_eq_mul]
  simp

/-- The normalized removable factor of the complex saddle phase at its double zero. -/
def deBruijnNewmanPolymathBoydComplexSaddleFactor (u : ℂ) : ℂ :=
  if u = 0 then 1 else
    2 * deBruijnNewmanPolymathBoydComplexSaddlePhase u / u ^ 2

@[simp]
theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_zero :
    deBruijnNewmanPolymathBoydComplexSaddleFactor 0 = 1 := by
  simp [deBruijnNewmanPolymathBoydComplexSaddleFactor]

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_sq_mul_factor (u : ℂ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase u =
      u ^ 2 / 2 * deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [deBruijnNewmanPolymathBoydComplexSaddleFactor, if_neg hu]
    field_simp [hu]

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_zero :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleFactor 0 := by
  obtain ⟨F, hF, hEq⟩ := exists_deBruijnNewmanPolymathBoydComplexSaddleTaylorFactor
  have hfactor : deBruijnNewmanPolymathBoydComplexSaddleFactor =
      fun u : ℂ => 1 + 2 * u * F u := by
    funext u
    by_cases hu : u = 0
    · simp [hu]
    · rw [deBruijnNewmanPolymathBoydComplexSaddleFactor, if_neg hu, hEq]
      field_simp [hu]
  rw [hfactor]
  fun_prop

/-- The normalized principal square-root factor at the double saddle. -/
def deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor (u : ℂ) : ℂ :=
  Complex.sqrt (deBruijnNewmanPolymathBoydComplexSaddleFactor u)

@[simp]
theorem deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_zero :
    deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor 0 = 1 := by
  simp [deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor]

theorem deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_sq (u : ℂ) :
    deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u ^ 2 =
      deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
  simp [deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor, Complex.sqrt]

theorem deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_analyticAt_zero :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor 0 := by
  have hsqrt : AnalyticAt ℂ Complex.sqrt 1 :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane)
  change AnalyticAt ℂ
    (Complex.sqrt ∘ deBruijnNewmanPolymathBoydComplexSaddleFactor) 0
  exact hsqrt.comp_of_eq
    deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_zero
    deBruijnNewmanPolymathBoydComplexSaddleFactor_zero

/-- The normalized local Boyd coordinate satisfying `w(u)^2 / 2 = exp(u) - u - 1`. -/
def deBruijnNewmanPolymathBoydComplexSaddleCoordinate (u : ℂ) : ℂ :=
  u * deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u

@[simp]
theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero :
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydComplexSaddleCoordinate]

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq (u : ℂ) :
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate u ^ 2 / 2 =
      deBruijnNewmanPolymathBoydComplexSaddlePhase u := by
  rw [deBruijnNewmanPolymathBoydComplexSaddleCoordinate, mul_pow,
    deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_sq,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_sq_mul_factor]
  ring

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0 := by
  unfold deBruijnNewmanPolymathBoydComplexSaddleCoordinate
  exact analyticAt_id.mul
    deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_analyticAt_zero

theorem deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero :
    deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0 = 1 := by
  unfold deBruijnNewmanPolymathBoydComplexSaddleCoordinate
  rw [deriv_fun_mul]
  · simp [deriv_id'']
  · fun_prop
  · exact deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_analyticAt_zero.differentiableAt

theorem deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero_ne :
    deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0 ≠ 0 := by
  rw [deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero]
  exact one_ne_zero

/-- The analytic inverse branch of the normalized Boyd coordinate at the origin. -/
def deBruijnNewmanPolymathBoydComplexSaddleLocalInverse : ℂ → ℂ :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero.hasStrictDerivAt.localInverse
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0) 0
    deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero_ne

theorem deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_analyticAt_zero :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleLocalInverse 0 := by
  simpa [deBruijnNewmanPolymathBoydComplexSaddleLocalInverse] using
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero.analyticAt_localInverse
      deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero_ne

theorem deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_left :
    ∀ᶠ u in 𝓝 0,
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse
        (deBruijnNewmanPolymathBoydComplexSaddleCoordinate u) = u := by
  simpa [deBruijnNewmanPolymathBoydComplexSaddleLocalInverse] using
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero.hasStrictDerivAt.eventually_left_inverse
      deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero_ne

theorem deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_right :
    ∀ᶠ z in 𝓝 0,
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydComplexSaddleLocalInverse z) = z := by
  simpa [deBruijnNewmanPolymathBoydComplexSaddleLocalInverse] using
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero.hasStrictDerivAt.eventually_right_inverse
      deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero_ne

end

end LeanLab.Riemann
