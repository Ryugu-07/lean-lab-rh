import LeanLab.Riemann.DeBruijnNewmanPolymathBoydSaddleIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The logarithmic saddle coordinate for the scaled Gamma function

This module applies the global one-dimensional Jacobian theorem to the positive-real saddle
integral. It does not assume the Boyd--Nemes remainder identity.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory Real Set
open scoped Real Topology

noncomputable section

/-- The scaled-Gamma saddle integrand after the global coordinate `t = exp u`. -/
def deBruijnNewmanPolymathBoydLogSaddleIntegrand (x u : ℝ) : ℝ :=
  Real.exp (-x * (Real.exp u - u - 1))

theorem deBruijnNewmanPolymathBoyd_exp_image_univ :
    Real.exp '' (Set.univ : Set ℝ) = Ioi 0 := by
  rw [Set.image_univ, Real.range_exp]

theorem deBruijnNewmanPolymathBoydLogSaddleIntegrand_eq_jacobian
    (x u : ℝ) :
    |Real.exp u| • deBruijnNewmanPolymathBoydSaddleIntegrand x (Real.exp u) =
      deBruijnNewmanPolymathBoydLogSaddleIntegrand x u := by
  rw [abs_of_pos (Real.exp_pos u)]
  simp only [smul_eq_mul, deBruijnNewmanPolymathBoydSaddleIntegrand,
    deBruijnNewmanPolymathBoydSaddlePhase, Real.log_exp,
    deBruijnNewmanPolymathBoydLogSaddleIntegrand]
  field_simp [Real.exp_ne_zero]
  congr 1
  ring

theorem deBruijnNewmanPolymathBoydLogSaddleIntegrand_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (deBruijnNewmanPolymathBoydLogSaddleIntegrand x) := by
  have himage : IntegrableOn
      (deBruijnNewmanPolymathBoydSaddleIntegrand x)
      (Real.exp '' (Set.univ : Set ℝ)) := by
    rw [deBruijnNewmanPolymathBoyd_exp_image_univ]
    exact deBruijnNewmanPolymathBoydSaddleIntegrand_integrableOn hx
  have hjac : IntegrableOn
      (fun u : ℝ => |Real.exp u| •
        deBruijnNewmanPolymathBoydSaddleIntegrand x (Real.exp u)) Set.univ :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun u _hu => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      Real.exp_injective.injOn
      (deBruijnNewmanPolymathBoydSaddleIntegrand x)).mp himage
  exact (integrableOn_univ.mp hjac).congr (Filter.Eventually.of_forall fun u =>
    deBruijnNewmanPolymathBoydLogSaddleIntegrand_eq_jacobian x u)

theorem integral_deBruijnNewmanPolymathBoydLogSaddleIntegrand
    (x : ℝ) :
    (∫ u : ℝ, deBruijnNewmanPolymathBoydLogSaddleIntegrand x u) =
      ∫ t : ℝ in Ioi 0, deBruijnNewmanPolymathBoydSaddleIntegrand x t := by
  have hchange := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun u _hu => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn
    (deBruijnNewmanPolymathBoydSaddleIntegrand x)
  rw [deBruijnNewmanPolymathBoyd_exp_image_univ] at hchange
  calc
    (∫ u : ℝ, deBruijnNewmanPolymathBoydLogSaddleIntegrand x u) =
        ∫ u : ℝ, |Real.exp u| •
          deBruijnNewmanPolymathBoydSaddleIntegrand x (Real.exp u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        (deBruijnNewmanPolymathBoydLogSaddleIntegrand_eq_jacobian x u).symm
    _ = ∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydSaddleIntegrand x t := by
      simpa only [Measure.restrict_univ] using hchange.symm

/-- The exact logarithmic-coordinate saddle representation of the project's scaled Gamma. -/
theorem deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydLogSaddleIntegral
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : ℂ) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        (∫ u : ℝ, deBruijnNewmanPolymathBoydLogSaddleIntegrand x u) : ℝ) : ℂ) := by
  rw [deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydSaddleIntegral hx,
    integral_deBruijnNewmanPolymathBoydLogSaddleIntegrand]

end

end LeanLab.Riemann
