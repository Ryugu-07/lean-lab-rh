import LeanLab.Riemann.DeBruijnNewmanPolymathBoydR2Integral

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The positive-real saddle integral for the scaled Gamma function

This module derives the first exact steepest-descent representation upstream of Boyd's resurgence
formula directly from Euler's Gamma integral.  It does not assume the Boyd--Nemes remainder
identity.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory Real Set
open scoped Real Topology

noncomputable section

/-- The real saddle phase obtained after scaling Euler's Gamma integral to its critical point. -/
def deBruijnNewmanPolymathBoydSaddlePhase (t : ℝ) : ℝ :=
  t - 1 - Real.log t

/-- The positive-real saddle integrand for the scaled Gamma function. -/
def deBruijnNewmanPolymathBoydSaddleIntegrand (x t : ℝ) : ℝ :=
  Real.exp (-x * deBruijnNewmanPolymathBoydSaddlePhase t) / t

theorem deBruijnNewmanPolymathBoydSaddleIntegrand_eq
    {x t : ℝ} (ht : 0 < t) :
    deBruijnNewmanPolymathBoydSaddleIntegrand x t =
      Real.exp x * (t ^ (x - 1) * Real.exp (-(x * t))) := by
  rw [deBruijnNewmanPolymathBoydSaddleIntegrand,
    deBruijnNewmanPolymathBoydSaddlePhase, Real.rpow_sub_one ht.ne' x,
    Real.rpow_def_of_pos ht x]
  field_simp
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem deBruijnNewmanPolymathBoydSaddleIntegrand_integrableOn
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn (deBruijnNewmanPolymathBoydSaddleIntegrand x) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ (x - 1) * Real.exp (-(x * t))) (Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := x - 1) (p := (1 : ℝ)) (b := x) (by linarith) (by norm_num) hx)
  refine IntegrableOn.congr_fun (hbase.const_mul (Real.exp x)) (fun t ht => ?_)
    measurableSet_Ioi
  exact (deBruijnNewmanPolymathBoydSaddleIntegrand_eq ht).symm

theorem integral_deBruijnNewmanPolymathBoydSaddleIntegrand
    {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ in Ioi 0, deBruijnNewmanPolymathBoydSaddleIntegrand x t) =
      Real.exp x * (1 / x) ^ x * Real.Gamma x := by
  calc
    (∫ t : ℝ in Ioi 0, deBruijnNewmanPolymathBoydSaddleIntegrand x t) =
        ∫ t : ℝ in Ioi 0,
          Real.exp x * (t ^ (x - 1) * Real.exp (-(x * t))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact deBruijnNewmanPolymathBoydSaddleIntegrand_eq ht
    _ = Real.exp x *
        ∫ t : ℝ in Ioi 0, t ^ (x - 1) * Real.exp (-(x * t)) := by
      rw [integral_const_mul]
    _ = Real.exp x * (1 / x) ^ x * Real.Gamma x := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hx hx]
      ring

theorem deBruijnNewmanPolymathGammaStirlingMain_ofReal
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathGammaStirlingMain (x : ℂ) =
      ((Real.sqrt (2 * Real.pi) *
        Real.exp ((x - 1 / 2) * Real.log x - x) : ℝ) : ℂ) := by
  unfold deBruijnNewmanPolymathGammaStirlingMain
  rw [show Complex.log (x : ℂ) = (Real.log x : ℂ) by
    exact (Complex.ofReal_log hx.le).symm]
  push_cast
  rfl

theorem deBruijnNewmanPolymathBoydSaddle_normalization_factor
    {x : ℝ} (hx : 0 < x) :
    1 / (Real.sqrt (2 * Real.pi) *
        Real.exp ((x - 1 / 2) * Real.log x - x)) =
      Real.sqrt (x / (2 * Real.pi)) * Real.exp x * (1 / x) ^ x := by
  have hsqrtx : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  have hinvrpow : (1 / x) ^ x = Real.exp (-x * Real.log x) := by
    rw [Real.rpow_def_of_pos (one_div_pos.mpr hx),
      Real.log_div one_ne_zero hx.ne', Real.log_one]
    congr 1
    ring
  have hsqrtDen : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [Real.sqrt_div hx.le, hsqrtx, hinvrpow]
  field_simp [hsqrtDen, Real.exp_ne_zero]
  rw [← Real.exp_add, ← Real.exp_add]
  convert Real.exp_zero.symm using 1
  rw [← Real.exp_add]
  congr 1
  ring

/-- The exact positive-real saddle representation of the project's scaled Gamma function. -/
theorem deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydSaddleIntegral
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : ℂ) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        (∫ t : ℝ in Ioi 0,
          deBruijnNewmanPolymathBoydSaddleIntegrand x t) : ℝ) : ℂ) := by
  rw [deBruijnNewmanPolymathScaledGamma, Complex.Gamma_ofReal,
    deBruijnNewmanPolymathGammaStirlingMain_ofReal hx,
    integral_deBruijnNewmanPolymathBoydSaddleIntegrand hx]
  norm_cast
  calc
    Real.Gamma x /
        (Real.sqrt (2 * Real.pi) * Real.exp ((x - 1 / 2) * Real.log x - x)) =
      (1 / (Real.sqrt (2 * Real.pi) *
        Real.exp ((x - 1 / 2) * Real.log x - x))) * Real.Gamma x := by ring
    _ = (Real.sqrt (x / (2 * Real.pi)) * Real.exp x * (1 / x) ^ x) *
        Real.Gamma x := by
      rw [deBruijnNewmanPolymathBoydSaddle_normalization_factor hx]
    _ = Real.sqrt (x / (2 * Real.pi)) *
        (Real.exp x * (1 / x) ^ x * Real.Gamma x) := by ring

end

end LeanLab.Riemann
