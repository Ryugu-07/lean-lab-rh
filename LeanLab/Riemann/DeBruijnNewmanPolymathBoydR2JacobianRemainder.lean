import LeanLab.Riemann.DeBruijnNewmanPolymathBoydAdjacentLandingJacobian
import LeanLab.Riemann.DeBruijnNewmanPolymathBoydR2Integral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The Boyd `R_2` inverse-Jacobian remainder

This module rewrites the positive-real second scaled-Gamma remainder as the exact Gaussian
integral of the normalized Boyd inverse Jacobian after subtracting its first three terms.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Real Topology

noncomputable section

/-- The quadratic subtraction fixed by the normalized Boyd inverse germ. -/
def deBruijnNewmanPolymathBoydR2JacobianPolynomial (w : ℝ) : ℝ :=
  1 - w / 3 + w ^ 2 / 12

/-- The real inverse-Jacobian remainder in the normalized Gaussian saddle coordinate. -/
def deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand (x w : ℝ) : ℝ :=
  (deriv deBruijnNewmanPolymathBoydRealSaddleInverse w -
      deBruijnNewmanPolymathBoydR2JacobianPolynomial w) *
    Real.exp (-x * w ^ 2 / 2)

theorem deBruijnNewmanPolymathBoydGaussian_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun w : ℝ => Real.exp (-x * w ^ 2 / 2)) := by
  convert integrable_exp_neg_mul_sq (by positivity : 0 < x / 2) using 1
  ext w
  congr 1
  ring

theorem deBruijnNewmanPolymathBoydGaussian_mul_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun w : ℝ => w * Real.exp (-x * w ^ 2 / 2)) := by
  convert integrable_mul_exp_neg_mul_sq (by positivity : 0 < x / 2) using 1
  ext w
  congr 2
  ring

theorem deBruijnNewmanPolymathBoydGaussian_sq_mul_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun w : ℝ => w ^ 2 * Real.exp (-x * w ^ 2 / 2)) := by
  convert integrable_rpow_mul_exp_neg_mul_sq
      (by positivity : 0 < x / 2) (by norm_num : (-1 : ℝ) < 2) using 1
  ext w
  rw [Real.rpow_two]
  congr 2
  ring

/-- The normalized centered Gaussian has total mass one. -/
theorem deBruijnNewmanPolymathBoyd_normalizedGaussian_integral
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, Real.exp (-x * w ^ 2 / 2)) = 1 := by
  have hIntegral :
      (∫ w : ℝ, Real.exp (-x * w ^ 2 / 2)) =
        Real.sqrt (Real.pi / (x / 2)) := by
    calc
      (∫ w : ℝ, Real.exp (-x * w ^ 2 / 2)) =
          ∫ w : ℝ, Real.exp (-(x / 2) * w ^ 2) := by
        apply integral_congr_ae
        filter_upwards with w
        congr 1
        ring
      _ = Real.sqrt (Real.pi / (x / 2)) := integral_gaussian (x / 2)
  rw [hIntegral]
  have ha : 0 ≤ x / (2 * Real.pi) := by positivity
  have hb : 0 ≤ Real.pi / (x / 2) := by positivity
  have hab : (x / (2 * Real.pi)) * (Real.pi / (x / 2)) = 1 := by
    field_simp [hx.ne', Real.pi_ne_zero]
  have hprod : 0 ≤ Real.sqrt (x / (2 * Real.pi)) *
      Real.sqrt (Real.pi / (x / 2)) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsquare :
      (Real.sqrt (x / (2 * Real.pi)) *
          Real.sqrt (Real.pi / (x / 2))) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, hab]
  nlinarith

/-- The normalized centered Gaussian first moment vanishes. -/
theorem deBruijnNewmanPolymathBoyd_normalizedGaussian_firstMoment
    {x : ℝ} (_hx : 0 < x) :
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, w * Real.exp (-x * w ^ 2 / 2)) = 0 := by
  let f : ℝ → ℝ := fun w => w * Real.exp (-x * w ^ 2 / 2)
  have hneg : (fun w : ℝ => f (-w)) = fun w => -f w := by
    funext w
    dsimp [f]
    rw [neg_sq]
    ring
  have hsymm : (∫ w : ℝ, f (-w)) = ∫ w : ℝ, f w :=
    integral_neg_eq_self f volume
  rw [hneg, integral_neg] at hsymm
  have hz : (∫ w : ℝ, f w) = 0 := by linarith
  rw [hz, mul_zero]

/-- The centered Gaussian with variance `1/x` has normalized second moment `1/x`. -/
theorem deBruijnNewmanPolymathBoyd_normalizedGaussian_secondMoment
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, w ^ 2 * Real.exp (-x * w ^ 2 / 2)) = 1 / x := by
  let v : ℝ≥0 := ⟨x⁻¹, inv_nonneg.mpr hx.le⟩
  have hv : v ≠ 0 := by
    intro h
    have hcoe := congrArg ((↑) : ℝ≥0 → ℝ) h
    simp only [v, NNReal.coe_zero] at hcoe
    exact inv_ne_zero hx.ne' hcoe
  have hdensity (w : ℝ) :
      gaussianPDFReal 0 v w =
        Real.sqrt (x / (2 * Real.pi)) * Real.exp (-x * w ^ 2 / 2) := by
    unfold gaussianPDFReal
    simp only [sub_zero]
    have hconstant :
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ =
          Real.sqrt (x / (2 * Real.pi)) := by
      change (Real.sqrt (2 * Real.pi * x⁻¹))⁻¹ =
        Real.sqrt (x / (2 * Real.pi))
      rw [← Real.sqrt_inv]
      congr 1
      field_simp [hx.ne', Real.pi_ne_zero]
    rw [hconstant]
    congr 1
    apply congrArg Real.exp
    change -w ^ 2 / (2 * x⁻¹) = -x * w ^ 2 / 2
    field_simp [hx.ne']
  have hvariance := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at hvariance
  simp only [integral_id_gaussianReal, sub_zero] at hvariance
  have hdensityIntegral :=
    integral_gaussianReal_eq_integral_smul (E := ℝ) (μ := 0) (v := v)
      (f := fun w : ℝ => w ^ 2) hv
  simp only [smul_eq_mul] at hdensityIntegral
  calc
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, w ^ 2 * Real.exp (-x * w ^ 2 / 2)) =
        ∫ w : ℝ, Real.sqrt (x / (2 * Real.pi)) *
          (w ^ 2 * Real.exp (-x * w ^ 2 / 2)) := by
      rw [integral_const_mul]
    _ = ∫ w : ℝ, gaussianPDFReal 0 v w * w ^ 2 := by
      apply integral_congr_ae
      filter_upwards with w
      rw [hdensity]
      ring
    _ = ∫ w : ℝ, w ^ 2 ∂gaussianReal 0 v := hdensityIntegral.symm
    _ = (v : ℝ) := hvariance
    _ = 1 / x := by
      change x⁻¹ = 1 / x
      simp [one_div]

theorem deBruijnNewmanPolymathBoydR2JacobianPolynomial_mul_gaussian_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun w : ℝ =>
      deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
        Real.exp (-x * w ^ 2 / 2)) := by
  have h0 := deBruijnNewmanPolymathBoydGaussian_integrable hx
  have h1 := deBruijnNewmanPolymathBoydGaussian_mul_integrable hx
  have h2 := deBruijnNewmanPolymathBoydGaussian_sq_mul_integrable hx
  have hcomb : Integrable (fun w : ℝ =>
      Real.exp (-x * w ^ 2 / 2) -
        (w * Real.exp (-x * w ^ 2 / 2)) / 3 +
        (w ^ 2 * Real.exp (-x * w ^ 2 / 2)) / 12) :=
    (h0.sub (h1.div_const 3)).add (h2.div_const 12)
  exact hcomb.congr (Filter.Eventually.of_forall fun w => by
    simp only [deBruijnNewmanPolymathBoydR2JacobianPolynomial]
    ring)

/-- Integrating the subtraction polynomial gives the first two scaled-Gamma terms exactly. -/
theorem deBruijnNewmanPolymathBoyd_normalizedGaussian_jacobianPolynomial
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
          Real.exp (-x * w ^ 2 / 2)) =
      1 + 1 / (12 * x) := by
  let g0 : ℝ → ℝ := fun w => Real.exp (-x * w ^ 2 / 2)
  let g1 : ℝ → ℝ := fun w => w * Real.exp (-x * w ^ 2 / 2)
  let g2 : ℝ → ℝ := fun w => w ^ 2 * Real.exp (-x * w ^ 2 / 2)
  have h0 : Integrable g0 := deBruijnNewmanPolymathBoydGaussian_integrable hx
  have h1 : Integrable g1 := deBruijnNewmanPolymathBoydGaussian_mul_integrable hx
  have h2 : Integrable g2 := deBruijnNewmanPolymathBoydGaussian_sq_mul_integrable hx
  have hfun : (fun w : ℝ =>
      deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
        Real.exp (-x * w ^ 2 / 2)) =
      fun w => g0 w - g1 w / 3 + g2 w / 12 := by
    funext w
    simp only [deBruijnNewmanPolymathBoydR2JacobianPolynomial, g0, g1, g2]
    ring
  have hIntegral :
      (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
          Real.exp (-x * w ^ 2 / 2)) =
        (∫ w : ℝ, g0 w) - (∫ w : ℝ, g1 w) / 3 + (∫ w : ℝ, g2 w) / 12 := by
    rw [hfun]
    calc
      (∫ w : ℝ, g0 w - g1 w / 3 + g2 w / 12) =
          (∫ w : ℝ, g0 w - g1 w / 3) + (∫ w : ℝ, g2 w / 12) := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_add (h0.sub (h1.div_const 3)) (h2.div_const 12)
      _ = ((∫ w : ℝ, g0 w) - (∫ w : ℝ, g1 w / 3)) +
          (∫ w : ℝ, g2 w / 12) := by
        rw [integral_sub h0 (h1.div_const 3)]
      _ = _ := by rw [integral_div, integral_div]
  rw [hIntegral]
  have hm0 := deBruijnNewmanPolymathBoyd_normalizedGaussian_integral hx
  have hm1 := deBruijnNewmanPolymathBoyd_normalizedGaussian_firstMoment hx
  have hm2 := deBruijnNewmanPolymathBoyd_normalizedGaussian_secondMoment hx
  have hx0 : x ≠ 0 := hx.ne'
  calc
    Real.sqrt (x / (2 * Real.pi)) *
        ((∫ w : ℝ, g0 w) - (∫ w : ℝ, g1 w) / 3 + (∫ w : ℝ, g2 w) / 12) =
      Real.sqrt (x / (2 * Real.pi)) * (∫ w : ℝ, g0 w) -
        (Real.sqrt (x / (2 * Real.pi)) * (∫ w : ℝ, g1 w)) / 3 +
        (Real.sqrt (x / (2 * Real.pi)) * (∫ w : ℝ, g2 w)) / 12 := by ring
    _ = 1 - 0 / 3 + (1 / x) / 12 := by rw [hm0, hm1, hm2]
    _ = 1 + 1 / (12 * x) := by field_simp; ring

theorem deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x) := by
  have hJ := deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_integrable hx
  have hP :=
    deBruijnNewmanPolymathBoydR2JacobianPolynomial_mul_gaussian_integrable hx
  refine (hJ.sub hP).congr (Filter.Eventually.of_forall fun w => ?_)
  change deriv deBruijnNewmanPolymathBoydRealSaddleInverse w *
        Real.exp (-x * w ^ 2 / 2) -
      deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
        Real.exp (-x * w ^ 2 / 2) =
    (deriv deBruijnNewmanPolymathBoydRealSaddleInverse w -
      deBruijnNewmanPolymathBoydR2JacobianPolynomial w) *
        Real.exp (-x * w ^ 2 / 2)
  ring

/-- The normalized remainder integral is the normalized full Jacobian integral minus the first
two scaled-Gamma terms. -/
theorem deBruijnNewmanPolymathBoyd_normalizedJacobianRemainderIntegral
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x w) =
      Real.sqrt (x / (2 * Real.pi)) *
          (∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) -
        1 - 1 / (12 * x) := by
  have hJ := deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_integrable hx
  have hP :=
    deBruijnNewmanPolymathBoydR2JacobianPolynomial_mul_gaussian_integrable hx
  have hrem :
      (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x w) =
        (∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) -
          ∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
            Real.exp (-x * w ^ 2 / 2) := by
    rw [← integral_sub hJ hP]
    apply integral_congr_ae
    filter_upwards with w
    simp only [deBruijnNewmanPolymathBoydGaussianSaddleIntegrand,
      deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand]
    ring
  rw [hrem]
  have hPnorm := deBruijnNewmanPolymathBoyd_normalizedGaussian_jacobianPolynomial hx
  calc
    Real.sqrt (x / (2 * Real.pi)) *
        ((∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) -
          ∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
            Real.exp (-x * w ^ 2 / 2)) =
      Real.sqrt (x / (2 * Real.pi)) *
          (∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) -
        Real.sqrt (x / (2 * Real.pi)) *
          (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianPolynomial w *
            Real.exp (-x * w ^ 2 / 2)) := by ring
    _ = _ := by rw [hPnorm]; ring

/-- On the positive real axis, the project's actual `R_2` is exactly the normalized Gaussian
integral of the inverse-Jacobian remainder. -/
theorem deBruijnNewmanPolymathGammaStirlingR2_ofReal_eq_boydJacobianRemainder
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathGammaStirlingR2 (x : ℂ) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x w) : ℝ) : ℂ) := by
  have hscaled :=
    deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydGaussianSaddleIntegral hx
  have hrem := deBruijnNewmanPolymathBoyd_normalizedJacobianRemainderIntegral hx
  rw [deBruijnNewmanPolymathGammaStirlingR2]
  change deBruijnNewmanPolymathScaledGamma (x : ℂ) - 1 - 1 / (12 * (x : ℂ)) = _
  rw [hscaled, hrem]
  push_cast
  ring

/-- The global complex Boyd inverse takes the normalized value zero at the origin. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse 0 = 0 := by
  have hlocal :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local.self_of_nhds
  rw [hlocal]
  have hleft :=
    deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_left.self_of_nhds
  simpa using hleft

/-- The first derivative of `(exp(U)-1)U'`, on the actual analytic inverse disk. -/
theorem deriv_deBruijnNewmanPolymathBoyd_inverseJacobianProduct
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deriv (fun z : ℂ =>
        (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z) - 1) *
          deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z) w =
      Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) *
          deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w ^ 2 +
        (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) - 1) *
          deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) w := by
  have hU :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hw
  have hU' := hU.deriv
  have hExp : HasDerivAt
      (fun z : ℂ => Complex.exp
        (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z))
      (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) *
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) w :=
    (Complex.hasDerivAt_exp
      (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w)).comp w
        hU.differentiableAt.hasDerivAt
  have hProduct := (hExp.sub_const 1).mul hU'.differentiableAt.hasDerivAt
  change deriv ((fun z : ℂ =>
      Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z) - 1) *
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) w = _
  rw [hProduct.deriv]
  ring

/-- The normalized inverse has second derivative `-1/3` at the active saddle. -/
theorem deriv_deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero :
    deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) 0 =
      -(1 : ℂ) / 3 := by
  let U : ℂ → ℂ := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
  let A : ℂ → ℂ := fun z => (Complex.exp (U z) - 1) * deriv U z
  let A1 : ℂ → ℂ :=
    (fun z => Complex.exp (U z)) * deriv U ^ 2 +
      (fun z => Complex.exp (U z) - 1) * deriv (deriv U)
  have hzero : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskZero.property
  have hopen : IsOpen deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact Metric.isOpen_ball
  have hU : AnalyticAt ℂ U 0 :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hzero
  have hEq : A =ᶠ[𝓝 0] fun z : ℂ => z := by
    filter_upwards [hopen.mem_nhds hzero] with z hz
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverseJacobian_phase hz
  have hAderiv : deriv A =ᶠ[𝓝 0] A1 := by
    filter_upwards [hopen.mem_nhds hzero] with z hz
    exact deriv_deBruijnNewmanPolymathBoyd_inverseJacobianProduct hz
  have hA1zero : deriv A1 0 = 0 := by
    calc
      deriv A1 0 = deriv (deriv A) 0 := hAderiv.deriv_eq.symm
      _ = deriv (deriv (fun z : ℂ => z)) 0 := hEq.deriv.deriv_eq
      _ = 0 := by simp
  have hExp : HasDerivAt (fun z : ℂ => Complex.exp (U z))
      (Complex.exp (U 0) * deriv U 0) 0 :=
    (Complex.hasDerivAt_exp (U 0)).comp 0 hU.differentiableAt.hasDerivAt
  have hDU : HasDerivAt (deriv U) (deriv (deriv U) 0) 0 :=
    hU.deriv.differentiableAt.hasDerivAt
  have hD2U : HasDerivAt (deriv (deriv U))
      (deriv (deriv (deriv U)) 0) 0 :=
    hU.deriv.deriv.differentiableAt.hasDerivAt
  have hA1 := (hExp.mul (hDU.pow 2)).add ((hExp.sub_const 1).mul hD2U)
  have hformula : deriv A1 0 =
      1 + 3 * deriv (deriv U) 0 := by
    change deriv
      ((fun z => Complex.exp (U z)) * deriv U ^ 2 +
        (fun z => Complex.exp (U z) - 1) * deriv (deriv U)) 0 = _
    rw [hA1.deriv]
    dsimp only [U]
    simp only [deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      Complex.exp_zero]
    norm_num
    rw [deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero]
    ring
  rw [hformula] at hA1zero
  change deriv (deriv U) 0 = -(1 : ℂ) / 3
  linear_combination (1 / 3 : ℂ) * hA1zero

/-- The second derivative of `(exp(U)-1)U'`, written in terms of the first three derivatives of
the actual inverse. -/
theorem deriv_deBruijnNewmanPolymathBoyd_inverseJacobianProductFirstDerivative
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deriv (fun z : ℂ =>
        Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z) *
            deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z ^ 2 +
          (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse z) - 1) *
            deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) z) w =
      Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) *
          deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w ^ 3 +
        3 * Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) *
          deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w *
            deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) w +
        (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) - 1) *
          deriv (deriv (deriv
            deBruijnNewmanPolymathBoydNormalizedCoordinateInverse)) w := by
  let U : ℂ → ℂ := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
  have hU : AnalyticAt ℂ U w :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hw
  have hExp : HasDerivAt (fun z : ℂ => Complex.exp (U z))
      (Complex.exp (U w) * deriv U w) w :=
    (Complex.hasDerivAt_exp (U w)).comp w hU.differentiableAt.hasDerivAt
  have hDU : HasDerivAt (deriv U) (deriv (deriv U) w) w :=
    hU.deriv.differentiableAt.hasDerivAt
  have hD2U : HasDerivAt (deriv (deriv U))
      (deriv (deriv (deriv U)) w) w :=
    hU.deriv.deriv.differentiableAt.hasDerivAt
  have hraw := (hExp.mul (hDU.pow 2)).add ((hExp.sub_const 1).mul hD2U)
  change deriv
      ((fun z => Complex.exp (U z)) * deriv U ^ 2 +
        (fun z => Complex.exp (U z) - 1) * deriv (deriv U)) w = _
  rw [hraw.deriv]
  simp only [Pi.pow_apply]
  ring

/-- The normalized inverse has third derivative `1/6` at the active saddle. -/
theorem deriv_deriv_deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero :
    deriv (deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse)) 0 =
      (1 : ℂ) / 6 := by
  let U : ℂ → ℂ := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
  let A : ℂ → ℂ := fun z => (Complex.exp (U z) - 1) * deriv U z
  let A1 : ℂ → ℂ :=
    (fun z => Complex.exp (U z)) * deriv U ^ 2 +
      (fun z => Complex.exp (U z) - 1) * deriv (deriv U)
  let A2 : ℂ → ℂ :=
    (fun z => Complex.exp (U z)) * deriv U ^ 3 +
      (fun z => 3 * (((fun y => Complex.exp (U y)) * deriv U *
        deriv (deriv U)) z)) +
      (fun z => Complex.exp (U z) - 1) * deriv (deriv (deriv U))
  have hzero : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskZero.property
  have hopen : IsOpen deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact Metric.isOpen_ball
  have hU : AnalyticAt ℂ U 0 :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hzero
  have hEq : A =ᶠ[𝓝 0] fun z : ℂ => z := by
    filter_upwards [hopen.mem_nhds hzero] with z hz
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverseJacobian_phase hz
  have hAderiv : deriv A =ᶠ[𝓝 0] A1 := by
    filter_upwards [hopen.mem_nhds hzero] with z hz
    exact deriv_deBruijnNewmanPolymathBoyd_inverseJacobianProduct hz
  have hA1deriv : deriv A1 =ᶠ[𝓝 0] A2 := by
    filter_upwards [hopen.mem_nhds hzero] with z hz
    have hUz : AnalyticAt ℂ U z :=
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hz
    have hExpz : HasDerivAt (fun y : ℂ => Complex.exp (U y))
        (Complex.exp (U z) * deriv U z) z :=
      (Complex.hasDerivAt_exp (U z)).comp z hUz.differentiableAt.hasDerivAt
    have hDUz : HasDerivAt (deriv U) (deriv (deriv U) z) z :=
      hUz.deriv.differentiableAt.hasDerivAt
    have hD2Uz : HasDerivAt (deriv (deriv U))
        (deriv (deriv (deriv U)) z) z :=
      hUz.deriv.deriv.differentiableAt.hasDerivAt
    have hraw := (hExpz.mul (hDUz.pow 2)).add ((hExpz.sub_const 1).mul hD2Uz)
    dsimp only [A1, A2]
    rw [hraw.deriv]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  have hA2zero : deriv A2 0 = 0 := by
    calc
      deriv A2 0 = deriv (deriv A1) 0 := hA1deriv.deriv_eq.symm
      _ = deriv (deriv (deriv A)) 0 := hAderiv.deriv.deriv_eq.symm
      _ = deriv (deriv (deriv (fun z : ℂ => z))) 0 := hEq.deriv.deriv.deriv_eq
      _ = 0 := by simp
  have hExp : HasDerivAt (fun z : ℂ => Complex.exp (U z))
      (Complex.exp (U 0) * deriv U 0) 0 :=
    (Complex.hasDerivAt_exp (U 0)).comp 0 hU.differentiableAt.hasDerivAt
  have hDU : HasDerivAt (deriv U) (deriv (deriv U) 0) 0 :=
    hU.deriv.differentiableAt.hasDerivAt
  have hD2U : HasDerivAt (deriv (deriv U))
      (deriv (deriv (deriv U)) 0) 0 :=
    hU.deriv.deriv.differentiableAt.hasDerivAt
  have hD3U : HasDerivAt (deriv (deriv (deriv U)))
      (deriv (deriv (deriv (deriv U))) 0) 0 :=
    hU.deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hA2 :=
    (hExp.mul (hDU.pow 3)).add
      (((hExp.mul hDU).mul hD2U).const_mul 3) |>.add
        ((hExp.sub_const 1).mul hD3U)
  have hformula : deriv A2 0 =
      1 + 6 * deriv (deriv U) 0 +
        3 * deriv (deriv U) 0 ^ 2 +
          4 * deriv (deriv (deriv U)) 0 := by
    change deriv
      ((fun z => Complex.exp (U z)) * deriv U ^ 3 +
        (fun z => 3 * (((fun y => Complex.exp (U y)) * deriv U *
          deriv (deriv U)) z)) +
        (fun z => Complex.exp (U z) - 1) * deriv (deriv (deriv U))) 0 = _
    rw [hA2.deriv]
    dsimp only [U]
    simp only [deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      deriv_deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      Complex.exp_zero]
    norm_num
    rw [deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero]
    norm_num
    ring
  rw [hformula] at hA2zero
  have hU2 : deriv (deriv U) 0 = -(1 : ℂ) / 3 :=
    deriv_deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero
  rw [hU2] at hA2zero
  change deriv (deriv (deriv U)) 0 = (1 : ℂ) / 6
  linear_combination (1 / 4 : ℂ) * hA2zero

/-- The quadratic subtraction polynomial is the Taylor polynomial of the actual inverse Jacobian
through degree two. -/
theorem deBruijnNewmanPolymathBoydR2JacobianPolynomial_eq_inverseJacobianTaylor
    (w : ℝ) :
    (deBruijnNewmanPolymathBoydR2JacobianPolynomial w : ℂ) =
      deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse 0 +
        deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) 0 * (w : ℂ) +
        deriv (deriv (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse)) 0 /
          2 * (w : ℂ) ^ 2 := by
  rw [deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
    deriv_deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
    deriv_deriv_deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero]
  simp only [deBruijnNewmanPolymathBoydR2JacobianPolynomial]
  norm_num
  ring

/-- Near the active saddle, the actual complex disk inverse restricted to the real axis is the
complexification of the global real saddle inverse. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_ofReal_eventually_eq_realInverse :
    (fun w : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (w : ℂ)) =ᶠ[𝓝 0]
      fun w : ℝ =>
        (deBruijnNewmanPolymathBoydRealSaddleInverse w : ℂ) := by
  have hRzero : deBruijnNewmanPolymathBoydRealSaddleInverse 0 = 0 := by
    simpa only [deBruijnNewmanPolymathBoydRealSaddleCoordinate_zero] using
      deBruijnNewmanPolymathBoydRealSaddleInverse_coordinate 0
  have hRtendsto : Filter.Tendsto
      (fun w : ℝ =>
        (deBruijnNewmanPolymathBoydRealSaddleInverse w : ℂ))
      (𝓝 0) (𝓝 0) := by
    have hreal : ContinuousAt deBruijnNewmanPolymathBoydRealSaddleInverse 0 :=
      deBruijnNewmanPolymathBoydRealSaddleInverse_continuous.continuousAt
    have hcomplex := Complex.continuous_ofReal.continuousAt.comp hreal
    change Filter.Tendsto
      (fun w : ℝ => (deBruijnNewmanPolymathBoydRealSaddleInverse w : ℂ))
      (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydRealSaddleInverse 0 : ℂ)) at hcomplex
    simpa only [hRzero, ofReal_zero] using hcomplex
  have hlocalReal :
      (fun w : ℝ => deBruijnNewmanPolymathBoydComplexSaddleLocalInverse (w : ℂ)) =ᶠ[𝓝 0]
        fun w : ℝ =>
          (deBruijnNewmanPolymathBoydRealSaddleInverse w : ℂ) := by
    have hleft := hRtendsto
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_left
    filter_upwards [hleft] with w hw
    change deBruijnNewmanPolymathBoydComplexSaddleLocalInverse
        (deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydRealSaddleInverse w : ℂ)) =
      (deBruijnNewmanPolymathBoydRealSaddleInverse w : ℂ) at hw
    rw [deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ofReal,
      deBruijnNewmanPolymathBoydRealSaddleCoordinate_inverse] at hw
    exact hw
  have hofReal : Filter.Tendsto (fun w : ℝ => (w : ℂ)) (𝓝 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt
  have hglobalLocal :
      (fun w : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (w : ℂ)) =ᶠ[𝓝 0]
        fun w : ℝ => deBruijnNewmanPolymathBoydComplexSaddleLocalInverse (w : ℂ) :=
    hofReal deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local
  exact hglobalLocal.trans hlocalReal

/-- The positive-ray kernel after removing its parameter denominator quotient. -/
def deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand (z : ℂ) (s : ℝ) : ℂ :=
  (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
      deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I)) *
    z / (z - (s : ℂ) * Complex.I)

/-- Parameter derivative of the positive-ray Stieltjes kernel. -/
def deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative (z : ℂ) (s : ℝ) : ℂ :=
  (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
      deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I)) *
    (-((s : ℂ) * Complex.I)) / (z - (s : ℂ) * Complex.I) ^ 2

theorem deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand_eq
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand z s =
      deBruijnNewmanPolymathBoydR2PlusIntegrand z s := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hden : z - (s : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [deBruijnNewmanPolymathBoydR2PlusIntegrand,
    deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand,
    deBruijnNewmanPolymathBoydR2_one_sub_eq_div hz]
  field_simp

theorem hasDerivAt_deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    HasDerivAt (fun w : ℂ => deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand w s)
      (deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative z s) z := by
  have hden : z - (s : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  let weight : ℂ := (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
    deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))
  have hquot := (hasDerivAt_id z).div
    ((hasDerivAt_id z).sub_const ((s : ℂ) * Complex.I)) hden
  have hraw := hquot.const_mul weight
  unfold deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand
    deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative
  dsimp only [weight] at hraw
  convert hraw using 1 <;> try rfl
  · funext w
    simp only [Pi.div_apply, id_eq, div_eq_mul_inv]
    ring
  · simp only [id_eq, one_mul, mul_one]
    ring

theorem deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand z) (Ioi 0) := by
  exact (deBruijnNewmanPolymathBoydR2_integrableOn hz).1.congr_fun
    (fun s hs => (deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand_eq hz s).symm)
    measurableSet_Ioi

theorem deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative_continuousOn
    {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative z) (Ioi 0) := by
  intro s hs
  have hspos : 0 < s := hs
  have hweight : ContinuousAt
      (fun t : ℝ => (((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma ((t : ℂ) * Complex.I))) s := by
    have hscalar : ContinuousAt
        (fun t : ℝ => ((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ)) s := by
      fun_prop
    exact hscalar.mul (deBruijnNewmanPolymathScaledGamma_I_continuousAt hspos)
  have hden : ContinuousAt (fun t : ℝ => z - (t : ℂ) * Complex.I) s := by fun_prop
  have hdenNe : z - (s : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  unfold deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative
  exact ((hweight.mul (by fun_prop)).div (hden.pow 2) (pow_ne_zero 2 hdenNe)).continuousWithinAt

private theorem deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball
    {z w : ℂ} (_hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2)) :
    z.re / 2 < w.re := by
  have hdist : ‖w - z‖ < z.re / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hreAbs : |w.re - z.re| ≤ ‖w - z‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
  linarith [neg_abs_le (w.re - z.re)]

private theorem deBruijnNewmanPolymathBoyd_half_re_le_stieltjesDenominator
    {z w : ℂ} (hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2)) (s : ℝ) :
    z.re / 2 ≤ ‖w - (s : ℂ) * Complex.I‖ := by
  have hwre := deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball hz hw
  calc
    z.re / 2 ≤ w.re := hwre.le
    _ = |(w - (s : ℂ) * Complex.I).re| := by simp [abs_of_pos (lt_trans (by positivity) hwre)]
    _ ≤ ‖w - (s : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _

/-- An elementary integrable majorant for the parameter derivative of either Stieltjes kernel. -/
def deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant (z : ℂ) (s : ℝ) : ℝ :=
  (1 / (z.re / 2) ^ 2) *
    (s ^ (3 / 2 : ℝ) * Real.exp (-Real.pi * s))

theorem deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant_integrableOn
    {z : ℂ} (_hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun s : ℝ => s ^ (3 / 2 : ℝ) * Real.exp (-Real.pi * s)) (Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (3 / 2 : ℝ)) (p := (1 : ℝ)) (b := Real.pi)
        (by norm_num) (by norm_num) Real.pi_pos)
  change IntegrableOn
    (fun s : ℝ => (1 / (z.re / 2) ^ 2) *
      (s ^ (3 / 2 : ℝ) * Real.exp (-Real.pi * s))) (Ioi 0)
  exact hbase.const_mul (1 / (z.re / 2) ^ 2)

private theorem deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative_norm_le
    {z w : ℂ} (hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2))
    {s : ℝ} (hs : 0 < s) :
    ‖deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative w s‖ ≤
      deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z s := by
  have hrpos : 0 < z.re / 2 := by positivity
  have hdenLower :=
    deBruijnNewmanPolymathBoyd_half_re_le_stieltjesDenominator hz hw s
  have hdenSq : (z.re / 2) ^ 2 ≤ ‖w - (s : ℂ) * Complex.I‖ ^ 2 := by
    nlinarith [sq_nonneg (‖w - (s : ℂ) * Complex.I‖ - z.re / 2)]
  have hrecip : 1 / ‖w - (s : ℂ) * Complex.I‖ ^ 2 ≤ 1 / (z.re / 2) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hrpos) hdenSq
  have hrpow : Real.sqrt s * s = s ^ (3 / 2 : ℝ) := by
    calc
      Real.sqrt s * s = s ^ (1 / 2 : ℝ) * s := by rw [Real.sqrt_eq_rpow]
      _ = s ^ (1 / 2 : ℝ) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hs _ _).symm
      _ = s ^ (3 / 2 : ℝ) := by congr 1; ring
  have hsi : ‖(s : ℂ) * Complex.I‖ = s := by
    rw [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  unfold deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative
  rw [norm_div, norm_mul, norm_neg, hsi, norm_pow, div_eq_mul_inv]
  calc
    ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
          deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I))‖ * s *
        (‖w - (s : ℂ) * Complex.I‖ ^ 2)⁻¹ ≤
      (Real.sqrt s * Real.exp (-Real.pi * s)) * s *
        (‖w - (s : ℂ) * Complex.I‖ ^ 2)⁻¹ := by
      gcongr
      exact deBruijnNewmanPolymathBoydR2_weight_norm_le hs
    _ ≤ (Real.sqrt s * Real.exp (-Real.pi * s)) * s *
        ((z.re / 2) ^ 2)⁻¹ := by
      gcongr
    _ = deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z s := by
      rw [deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant]
      rw [show Real.sqrt s * Real.exp (-Real.pi * s) * s =
        (Real.sqrt s * s) * Real.exp (-Real.pi * s) by ring, hrpow]
      ring

/-- The positive Boyd ray integral is holomorphic in its right-half-plane parameter. -/
theorem deBruijnNewmanPolymathBoydR2PlusStieltjesIntegral_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt
      (fun w : ℂ => ∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand w s)
      (∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative z s) z := by
  let F : ℂ → ℝ → ℂ := deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand
  let F' : ℂ → ℝ → ℂ := deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative
  let bound : ℝ → ℝ := deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z
  have hball : Metric.ball z (z.re / 2) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (by positivity)
  have hFmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [hball] with w hw
    have hwre : 0 < w.re :=
      lt_trans (by positivity) (deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball hz hw)
    exact (deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand_integrableOn hwre).aestronglyMeasurable
  have hFint : Integrable (F z) (volume.restrict (Ioi 0)) :=
    deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand_integrableOn hz
  have hF'meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    (deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative_continuousOn hz).aestronglyMeasurable
      measurableSet_Ioi
  have hbound : ∀ᵐ s ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z (z.re / 2), ‖F' w s‖ ≤ bound s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    exact deBruijnNewmanPolymathBoydR2PlusStieltjesDerivative_norm_le hz hw hs
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z (z.re / 2), HasDerivAt (F · s) (F' w s) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have hwre : 0 < w.re :=
      lt_trans (by positivity) (deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball hz hw)
    exact hasDerivAt_deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand hwre s
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F') (bound := bound)
    (s := Metric.ball z (z.re / 2)) (x₀ := z) hball hFmeas hFint hF'meas hbound
    (deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant_integrableOn hz) hdiff
  exact hmain.2

/-- The negative-ray kernel after removing its parameter denominator quotient. -/
def deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand (z : ℂ) (s : ℝ) : ℂ :=
  (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
      deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I)) *
    z / (z + (s : ℂ) * Complex.I)

/-- Parameter derivative of the negative-ray Stieltjes kernel. -/
def deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative (z : ℂ) (s : ℝ) : ℂ :=
  (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
      deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I)) *
    ((s : ℂ) * Complex.I) / (z + (s : ℂ) * Complex.I) ^ 2

theorem deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand_eq
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand z s =
      deBruijnNewmanPolymathBoydR2MinusIntegrand z s := by
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hden : z + (s : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  rw [deBruijnNewmanPolymathBoydR2MinusIntegrand,
    deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand,
    deBruijnNewmanPolymathBoydR2_one_add_eq_div hz]
  field_simp

theorem hasDerivAt_deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    HasDerivAt (fun w : ℂ => deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand w s)
      (deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative z s) z := by
  have hden : z + (s : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  let weight : ℂ := (((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
    deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I))
  have hquot := (hasDerivAt_id z).div
    ((hasDerivAt_id z).add_const ((s : ℂ) * Complex.I)) hden
  have hraw := hquot.const_mul weight
  unfold deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand
    deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative
  dsimp only [weight] at hraw
  convert hraw using 1 <;> try rfl
  · funext w
    simp only [Pi.div_apply, id_eq, div_eq_mul_inv]
    ring
  · simp only [id_eq, one_mul, mul_one]
    ring

theorem deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand z) (Ioi 0) := by
  exact (deBruijnNewmanPolymathBoydR2_integrableOn hz).2.congr_fun
    (fun s hs => (deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand_eq hz s).symm)
    measurableSet_Ioi

theorem deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative_continuousOn
    {z : ℂ} (hz : 0 < z.re) :
    ContinuousOn (deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative z) (Ioi 0) := by
  intro s hs
  have hspos : 0 < s := hs
  have hweight : ContinuousAt
      (fun t : ℝ => (((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ) *
        deBruijnNewmanPolymathScaledGamma (-(t : ℂ) * Complex.I))) s := by
    have hscalar : ContinuousAt
        (fun t : ℝ => ((t * Real.exp (-2 * Real.pi * t) : ℝ) : ℂ)) s := by
      fun_prop
    exact hscalar.mul (deBruijnNewmanPolymathScaledGamma_neg_I_continuousAt hspos)
  have hden : ContinuousAt (fun t : ℝ => z + (t : ℂ) * Complex.I) s := by fun_prop
  have hdenNe : z + (s : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  unfold deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative
  exact ((hweight.mul (by fun_prop)).div (hden.pow 2) (pow_ne_zero 2 hdenNe)).continuousWithinAt

private theorem deBruijnNewmanPolymathBoyd_half_re_le_negativeStieltjesDenominator
    {z w : ℂ} (hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2)) (s : ℝ) :
    z.re / 2 ≤ ‖w + (s : ℂ) * Complex.I‖ := by
  have hwre := deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball hz hw
  calc
    z.re / 2 ≤ w.re := hwre.le
    _ = |(w + (s : ℂ) * Complex.I).re| := by simp [abs_of_pos (lt_trans (by positivity) hwre)]
    _ ≤ ‖w + (s : ℂ) * Complex.I‖ := Complex.abs_re_le_norm _

private theorem deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative_norm_le
    {z w : ℂ} (hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2))
    {s : ℝ} (hs : 0 < s) :
    ‖deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative w s‖ ≤
      deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z s := by
  have hrpos : 0 < z.re / 2 := by positivity
  have hdenLower :=
    deBruijnNewmanPolymathBoyd_half_re_le_negativeStieltjesDenominator hz hw s
  have hdenSq : (z.re / 2) ^ 2 ≤ ‖w + (s : ℂ) * Complex.I‖ ^ 2 := by
    nlinarith [sq_nonneg (‖w + (s : ℂ) * Complex.I‖ - z.re / 2)]
  have hrecip : 1 / ‖w + (s : ℂ) * Complex.I‖ ^ 2 ≤ 1 / (z.re / 2) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hrpos) hdenSq
  have hrpow : Real.sqrt s * s = s ^ (3 / 2 : ℝ) := by
    calc
      Real.sqrt s * s = s ^ (1 / 2 : ℝ) * s := by rw [Real.sqrt_eq_rpow]
      _ = s ^ (1 / 2 : ℝ) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hs _ _).symm
      _ = s ^ (3 / 2 : ℝ) := by congr 1; ring
  have hsi : ‖(s : ℂ) * Complex.I‖ = s := by
    rw [norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hs]
  unfold deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative
  rw [norm_div, norm_mul, hsi, norm_pow, div_eq_mul_inv]
  calc
    ‖(((s * Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) *
          deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I))‖ * s *
        (‖w + (s : ℂ) * Complex.I‖ ^ 2)⁻¹ ≤
      (Real.sqrt s * Real.exp (-Real.pi * s)) * s *
        (‖w + (s : ℂ) * Complex.I‖ ^ 2)⁻¹ := by
      gcongr
      rw [deBruijnNewmanPolymathBoydR2_minusWeight_norm_eq hs]
      exact deBruijnNewmanPolymathBoydR2_weight_norm_le hs
    _ ≤ (Real.sqrt s * Real.exp (-Real.pi * s)) * s *
        ((z.re / 2) ^ 2)⁻¹ := by
      gcongr
    _ = deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z s := by
      rw [deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant]
      rw [show Real.sqrt s * Real.exp (-Real.pi * s) * s =
        (Real.sqrt s * s) * Real.exp (-Real.pi * s) by ring, hrpow]
      ring

/-- The negative Boyd ray integral is holomorphic in its right-half-plane parameter. -/
theorem deBruijnNewmanPolymathBoydR2MinusStieltjesIntegral_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt
      (fun w : ℂ => ∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand w s)
      (∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative z s) z := by
  let F : ℂ → ℝ → ℂ := deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand
  let F' : ℂ → ℝ → ℂ := deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative
  let bound : ℝ → ℝ := deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant z
  have hball : Metric.ball z (z.re / 2) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (by positivity)
  have hFmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [hball] with w hw
    have hwre : 0 < w.re :=
      lt_trans (by positivity) (deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball hz hw)
    exact (deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand_integrableOn hwre).aestronglyMeasurable
  have hFint : Integrable (F z) (volume.restrict (Ioi 0)) :=
    deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand_integrableOn hz
  have hF'meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    (deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative_continuousOn hz).aestronglyMeasurable
      measurableSet_Ioi
  have hbound : ∀ᵐ s ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z (z.re / 2), ‖F' w s‖ ≤ bound s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    exact deBruijnNewmanPolymathBoydR2MinusStieltjesDerivative_norm_le hz hw hs
  have hdiff : ∀ᵐ s ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z (z.re / 2), HasDerivAt (F · s) (F' w s) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs w hw
    have hwre : 0 < w.re :=
      lt_trans (by positivity) (deBruijnNewmanPolymathBoyd_half_re_lt_re_of_mem_ball hz hw)
    exact hasDerivAt_deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand hwre s
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F') (bound := bound)
    (s := Metric.ball z (z.re / 2)) (x₀ := z) hball hFmeas hFint hF'meas hbound
    (deBruijnNewmanPolymathBoydR2StieltjesDerivativeMajorant_integrableOn hz) hdiff
  exact hmain.2

/-- Stieltjes form of the complete two-ray Boyd expression. -/
def deBruijnNewmanPolymathBoydR2StieltjesIntegral (z : ℂ) : ℂ :=
  ((∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand z s) -
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand z s)) /
    (2 * Real.pi * Complex.I * z ^ 2)

theorem deBruijnNewmanPolymathBoydR2Integral_eq_stieltjes
    {z : ℂ} (hz : 0 < z.re) :
    deBruijnNewmanPolymathBoydR2Integral z =
      deBruijnNewmanPolymathBoydR2StieltjesIntegral z := by
  have hplus :
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2PlusIntegrand z s) =
        ∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand z s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (deBruijnNewmanPolymathBoydR2PlusStieltjesIntegrand_eq hz s).symm
  have hminus :
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2MinusIntegrand z s) =
        ∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand z s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (deBruijnNewmanPolymathBoydR2MinusStieltjesIntegrand_eq hz s).symm
  rw [deBruijnNewmanPolymathBoydR2Integral_eq, hplus, hminus]
  rfl

theorem deBruijnNewmanPolymathBoydR2StieltjesIntegral_differentiableAt
    {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ deBruijnNewmanPolymathBoydR2StieltjesIntegral z := by
  have hplus :=
    (deBruijnNewmanPolymathBoydR2PlusStieltjesIntegral_hasDerivAt hz).differentiableAt
  have hminus :=
    (deBruijnNewmanPolymathBoydR2MinusStieltjesIntegral_hasDerivAt hz).differentiableAt
  have hden : DifferentiableAt ℂ (fun w : ℂ => 2 * Real.pi * Complex.I * w ^ 2) z := by
    fun_prop
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hden0 : 2 * Real.pi * Complex.I * z ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num [Real.pi_ne_zero]) Complex.I_ne_zero)
      (pow_ne_zero 2 hz0)
  unfold deBruijnNewmanPolymathBoydR2StieltjesIntegral
  exact (hminus.sub hplus).div hden hden0

/-- The source-exact Boyd right-hand side is holomorphic on the open right half-plane. -/
theorem deBruijnNewmanPolymathBoydR2Integral_differentiableAt
    {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ deBruijnNewmanPolymathBoydR2Integral z := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have heq : deBruijnNewmanPolymathBoydR2Integral =ᶠ[𝓝 z]
      deBruijnNewmanPolymathBoydR2StieltjesIntegral := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact deBruijnNewmanPolymathBoydR2Integral_eq_stieltjes hw
  exact (deBruijnNewmanPolymathBoydR2StieltjesIntegral_differentiableAt hz).congr_of_eventuallyEq
    heq

theorem deBruijnNewmanPolymathBoydR2Integral_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathBoydR2Integral {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (deBruijnNewmanPolymathBoydR2Integral_differentiableAt hz).differentiableWithinAt

/-- The actual project Stirling remainder is holomorphic on the open right half-plane. -/
theorem deBruijnNewmanPolymathGammaStirlingR2_differentiableAt
    {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ deBruijnNewmanPolymathGammaStirlingR2 z := by
  have hnotpole : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num at hre
    linarith
  have hscaled := deBruijnNewmanPolymathScaledGamma_differentiableAt (Or.inl hz) hnotpole
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hfrac : DifferentiableAt ℂ (fun w : ℂ => 1 / (12 * w)) z := by
    exact (differentiableAt_const (c := (1 : ℂ))).div (by fun_prop)
      (mul_ne_zero (by norm_num) hz0)
  unfold deBruijnNewmanPolymathGammaStirlingR2
  exact (hscaled.sub (differentiableAt_const (c := (1 : ℂ)))).sub hfrac

theorem deBruijnNewmanPolymathGammaStirlingR2_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathGammaStirlingR2 {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (deBruijnNewmanPolymathGammaStirlingR2_differentiableAt hz).differentiableWithinAt

/-- The first remaining contour statement after the exact positive-real Jacobian reduction. -/
def deBruijnNewmanPolymathBoydR2PositiveRealContourEquality : Prop :=
  ∀ x : ℝ, 0 < x →
    ((Real.sqrt (x / (2 * Real.pi)) *
      ∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x w : ℝ) : ℂ) =
      deBruijnNewmanPolymathBoydR2Integral (x : ℂ)

/-- Real-scalar form of the remaining contour equality, using conjugacy of the two Boyd rays. -/
def deBruijnNewmanPolymathBoydR2PositiveRealScalarContourEquality : Prop :=
  ∀ x : ℝ, 0 < x →
    Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, deBruijnNewmanPolymathBoydR2JacobianRemainderIntegrand x w) =
      -((∫ s : ℝ in Ioi 0,
        deBruijnNewmanPolymathBoydR2PlusIntegrand (x : ℂ) s).im) /
        (Real.pi * x ^ 2)

theorem deBruijnNewmanPolymathBoydR2_positiveRealContourEquality_iff_scalar :
    deBruijnNewmanPolymathBoydR2PositiveRealContourEquality ↔
      deBruijnNewmanPolymathBoydR2PositiveRealScalarContourEquality := by
  constructor
  · intro h x hx
    have hc := h x hx
    rw [deBruijnNewmanPolymathBoydR2Integral_ofReal] at hc
    exact Complex.ofReal_inj.mp (hc.trans (by
      push_cast
      ring))
  · intro h x hx
    rw [deBruijnNewmanPolymathBoydR2Integral_ofReal]
    rw [h x hx]
    push_cast
    ring

/-- Equality on the positive real ray propagates to the complete right half-plane. -/
theorem deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_of_forall_pos_ofReal
    (hreal : ∀ x : ℝ, 0 < x →
      deBruijnNewmanPolymathGammaStirlingR2 (x : ℂ) =
        deBruijnNewmanPolymathBoydR2Integral (x : ℂ))
    {z : ℂ} (hz : 0 < z.re) :
    deBruijnNewmanPolymathGammaStirlingR2 z =
      deBruijnNewmanPolymathBoydR2Integral z := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hR2Analytic : AnalyticOnNhd ℂ deBruijnNewmanPolymathGammaStirlingR2 U :=
    (analyticOnNhd_iff_differentiableOn hopen).2
      deBruijnNewmanPolymathGammaStirlingR2_differentiableOn_rightHalfPlane
  have hBoydAnalytic : AnalyticOnNhd ℂ deBruijnNewmanPolymathBoydR2Integral U :=
    (analyticOnNhd_iff_differentiableOn hopen).2
      deBruijnNewmanPolymathBoydR2Integral_differentiableOn_rightHalfPlane
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hone : (1 : ℂ) ∈ U := by simp [U]
  let x : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hx : Filter.Tendsto x Filter.atTop (𝓝 1) := by
    dsimp only [x]
    simpa using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (𝓝 1)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hxc : Filter.Tendsto (fun n => (x n : ℂ)) Filter.atTop (𝓝 (1 : ℂ)) := by
    change Filter.Tendsto (Complex.ofReal ∘ x) Filter.atTop (𝓝 (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  have hpunctured : ∀ᶠ n in Filter.atTop, (x n : ℂ) ∈ ({(1 : ℂ)} : Set ℂ)ᶜ :=
    Filter.Eventually.of_forall fun n => by
      have hxn : x n ≠ 1 := by
        dsimp only [x]
        have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      exact hxn (Complex.ofReal_inj.mp (by simpa only [ofReal_one] using h))
  have hxcWithin : Filter.Tendsto (fun n => (x n : ℂ)) Filter.atTop
      (𝓝[({(1 : ℂ)} : Set ℂ)ᶜ] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxc, hpunctured⟩
  have heqFrequentlyAtTop : ∃ᶠ n in Filter.atTop,
      deBruijnNewmanPolymathGammaStirlingR2 (x n : ℂ) =
        deBruijnNewmanPolymathBoydR2Integral (x n : ℂ) :=
    (Filter.Eventually.of_forall fun n => hreal (x n) (by dsimp only [x]; positivity)).frequently
  have heqFrequently : ∃ᶠ w in 𝓝[({(1 : ℂ)} : Set ℂ)ᶜ] (1 : ℂ),
      deBruijnNewmanPolymathGammaStirlingR2 w =
        deBruijnNewmanPolymathBoydR2Integral w :=
    hxcWithin.frequently heqFrequentlyAtTop
  exact (hR2Analytic.eqOn_of_preconnected_of_frequently_eq hBoydAnalytic hpre hone
    heqFrequently) hz

/-- The full Boyd--Nemes equation `(15)` at `N = 2` is equivalent to the one remaining
positive-real contour equality. -/
theorem deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_iff_positiveRealContourEquality :
    (∀ z : ℂ, 0 < z.re →
      deBruijnNewmanPolymathGammaStirlingR2 z =
        deBruijnNewmanPolymathBoydR2Integral z) ↔
      deBruijnNewmanPolymathBoydR2PositiveRealContourEquality := by
  constructor
  · intro hall x hx
    rw [← deBruijnNewmanPolymathGammaStirlingR2_ofReal_eq_boydJacobianRemainder hx]
    exact hall (x : ℂ) (by simpa using hx)
  · intro hcontour z hz
    apply deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_of_forall_pos_ofReal
      (z := z) (hz := hz)
    intro x hx
    rw [deBruijnNewmanPolymathGammaStirlingR2_ofReal_eq_boydJacobianRemainder hx]
    exact hcontour x hx

end

end LeanLab.Riemann
