import LeanLab.Riemann.DeBruijnNewmanPolymathBoydLocalSaddleInverse
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.MonotoneContinuity

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The global real Boyd saddle coordinate

This module extends the normalized Boyd saddle coordinate over the whole real axis, constructs its
global real inverse, and applies the resulting Jacobian to the scaled-Gamma integral. It also
records the nonzero integer complex saddles where global complex continuation first becomes
critical. It makes no global complex-inverse or resurgence-contour claim.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Real Set
open scoped ComplexOrder Real Topology

noncomputable section

/-- Boyd's saddle phase restricted to the real logarithmic coordinate. -/
def deBruijnNewmanPolymathBoydRealSaddlePhase (u : ℝ) : ℝ :=
  Real.exp u - u - 1

/-- The positive removable factor of the real Boyd saddle phase. -/
def deBruijnNewmanPolymathBoydRealSaddleFactor (u : ℝ) : ℝ :=
  if u = 0 then 1 else
    2 * deBruijnNewmanPolymathBoydRealSaddlePhase u / u ^ 2

/-- The principal Boyd saddle coordinate on the complete real axis. -/
def deBruijnNewmanPolymathBoydRealSaddleCoordinate (u : ℝ) : ℝ :=
  u * Real.sqrt (deBruijnNewmanPolymathBoydRealSaddleFactor u)

@[simp]
theorem deBruijnNewmanPolymathBoydRealSaddlePhase_zero :
    deBruijnNewmanPolymathBoydRealSaddlePhase 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydRealSaddlePhase]

@[simp]
theorem deBruijnNewmanPolymathBoydRealSaddleFactor_zero :
    deBruijnNewmanPolymathBoydRealSaddleFactor 0 = 1 := by
  simp [deBruijnNewmanPolymathBoydRealSaddleFactor]

@[simp]
theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_zero :
    deBruijnNewmanPolymathBoydRealSaddleCoordinate 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydRealSaddleCoordinate]

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal (u : ℝ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase (u : ℂ) =
      (deBruijnNewmanPolymathBoydRealSaddlePhase u : ℂ) := by
  simp [deBruijnNewmanPolymathBoydComplexSaddlePhase,
    deBruijnNewmanPolymathBoydRealSaddlePhase]

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_ofReal (u : ℝ) :
    deBruijnNewmanPolymathBoydComplexSaddleFactor (u : ℂ) =
      (deBruijnNewmanPolymathBoydRealSaddleFactor u : ℂ) := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [deBruijnNewmanPolymathBoydComplexSaddleFactor,
      deBruijnNewmanPolymathBoydRealSaddleFactor, if_neg hu]
    simp only [ofReal_eq_zero, hu, if_false,
      deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal]
    push_cast
    rfl

theorem deBruijnNewmanPolymathBoydRealSaddleFactor_pos (u : ℝ) :
    0 < deBruijnNewmanPolymathBoydRealSaddleFactor u := by
  by_cases hu : u = 0
  · simp [hu]
  · have hphase : 0 < deBruijnNewmanPolymathBoydRealSaddlePhase u := by
      unfold deBruijnNewmanPolymathBoydRealSaddlePhase
      linarith [Real.add_one_lt_exp hu]
    rw [deBruijnNewmanPolymathBoydRealSaddleFactor, if_neg hu]
    positivity

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ofReal (u : ℝ) :
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate (u : ℂ) =
      (deBruijnNewmanPolymathBoydRealSaddleCoordinate u : ℂ) := by
  rw [deBruijnNewmanPolymathBoydComplexSaddleCoordinate,
    deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor,
    deBruijnNewmanPolymathBoydComplexSaddleFactor_ofReal]
  have hnonneg : (0 : ℂ) ≤
      (deBruijnNewmanPolymathBoydRealSaddleFactor u : ℂ) := by
    simpa using (deBruijnNewmanPolymathBoydRealSaddleFactor_pos u).le
  rw [Complex.sqrt_of_nonneg hnonneg]
  simp [deBruijnNewmanPolymathBoydRealSaddleCoordinate]

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq (u : ℝ) :
    deBruijnNewmanPolymathBoydRealSaddleCoordinate u ^ 2 / 2 =
      deBruijnNewmanPolymathBoydRealSaddlePhase u := by
  rw [deBruijnNewmanPolymathBoydRealSaddleCoordinate, mul_pow,
    Real.sq_sqrt (deBruijnNewmanPolymathBoydRealSaddleFactor_pos u).le]
  by_cases hu : u = 0
  · simp [hu]
  · rw [deBruijnNewmanPolymathBoydRealSaddleFactor, if_neg hu]
    field_simp [hu]

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_differentiableAt (u : ℝ) :
    DifferentiableAt ℝ deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
  by_cases hu : u = 0
  · subst u
    have hcomplex : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddleCoordinate 1 0 := by
      have h :=
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero.differentiableAt.hasDerivAt
      rw [deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero] at h
      exact h
    have hreal := hcomplex.real_of_complex
    simpa only [deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ofReal, ofReal_re, one_re] using
      hreal.differentiableAt
  · have hfactor : DifferentiableAt ℝ deBruijnNewmanPolymathBoydRealSaddleFactor u := by
      have hdirect : DifferentiableAt ℝ
          (fun y : ℝ => 2 * deBruijnNewmanPolymathBoydRealSaddlePhase y / y ^ 2) u := by
        unfold deBruijnNewmanPolymathBoydRealSaddlePhase
        fun_prop (disch := aesop)
      apply hdirect.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hu] with y hy
      simp [deBruijnNewmanPolymathBoydRealSaddleFactor, hy]
    unfold deBruijnNewmanPolymathBoydRealSaddleCoordinate
    exact differentiableAt_id.mul
      (hfactor.hasDerivAt.sqrt
        (deBruijnNewmanPolymathBoydRealSaddleFactor_pos u).ne').differentiableAt

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_mul_deriv (u : ℝ) :
    deBruijnNewmanPolymathBoydRealSaddleCoordinate u *
        deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u =
      Real.exp u - 1 := by
  have hcoordinate :=
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_differentiableAt u
  have hsquare : HasDerivAt
      (fun y : ℝ => deBruijnNewmanPolymathBoydRealSaddleCoordinate y ^ 2 / 2)
      (deBruijnNewmanPolymathBoydRealSaddleCoordinate u *
        deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u) u := by
    have hraw := (hcoordinate.hasDerivAt.pow 2).div_const 2
    have hcoeff :
        (2 : ℝ) * deBruijnNewmanPolymathBoydRealSaddleCoordinate u ^ (2 - 1) *
              deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u / 2 =
            deBruijnNewmanPolymathBoydRealSaddleCoordinate u *
              deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
      norm_num
      ring
    exact hraw.congr_deriv hcoeff
  have hphase : HasDerivAt deBruijnNewmanPolymathBoydRealSaddlePhase
      (Real.exp u - 1) u := by
    unfold deBruijnNewmanPolymathBoydRealSaddlePhase
    have hraw := ((Real.hasDerivAt_exp u).sub (hasDerivAt_id u)).sub
      (hasDerivAt_const u 1)
    apply (hraw.congr_deriv (by ring)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => rfl
  exact (hphase.unique <| hsquare.congr_of_eventuallyEq <|
    Filter.Eventually.of_forall fun y =>
      (deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq y).symm).symm

theorem deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_zero :
    deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate 0 = 1 := by
  have hcomplex : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddleCoordinate 1 0 := by
    have h :=
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_zero.differentiableAt.hasDerivAt
    rw [deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero] at h
    exact h
  have hreal := hcomplex.real_of_complex
  simpa only [deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ofReal, ofReal_re, one_re] using
    hreal.deriv

theorem deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_pos (u : ℝ) :
    0 < deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have hcoordinate : deBruijnNewmanPolymathBoydRealSaddleCoordinate u < 0 := by
      unfold deBruijnNewmanPolymathBoydRealSaddleCoordinate
      exact mul_neg_of_neg_of_pos hu
        (Real.sqrt_pos.2 (deBruijnNewmanPolymathBoydRealSaddleFactor_pos u))
    have hexp : Real.exp u - 1 < 0 := by
      exact sub_neg.mpr (Real.exp_lt_one_iff.mpr hu)
    have hderiv : deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u =
        (Real.exp u - 1) / deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
      apply (eq_div_iff hcoordinate.ne).2
      rw [mul_comm, deBruijnNewmanPolymathBoydRealSaddleCoordinate_mul_deriv]
    rw [hderiv]
    exact div_pos_of_neg_of_neg hexp hcoordinate
  · subst u
    simp [deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_zero]
  · have hcoordinate : 0 < deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
      unfold deBruijnNewmanPolymathBoydRealSaddleCoordinate
      exact mul_pos hu
        (Real.sqrt_pos.2 (deBruijnNewmanPolymathBoydRealSaddleFactor_pos u))
    have hexp : 0 < Real.exp u - 1 := by
      exact sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
    have hderiv : deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate u =
        (Real.exp u - 1) / deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
      apply (eq_div_iff hcoordinate.ne').2
      rw [mul_comm, deBruijnNewmanPolymathBoydRealSaddleCoordinate_mul_deriv]
    rw [hderiv]
    exact div_pos hexp hcoordinate

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_strictMono :
    StrictMono deBruijnNewmanPolymathBoydRealSaddleCoordinate :=
  strictMono_of_deriv_pos deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_pos

theorem deBruijnNewmanPolymathBoydRealSaddleFactor_one_le
    {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ deBruijnNewmanPolymathBoydRealSaddleFactor u := by
  by_cases hzero : u = 0
  · simp [hzero]
  · have hphase : u ^ 2 / 2 ≤ deBruijnNewmanPolymathBoydRealSaddlePhase u := by
      unfold deBruijnNewmanPolymathBoydRealSaddlePhase
      linarith [Real.quadratic_le_exp_of_nonneg hu]
    rw [deBruijnNewmanPolymathBoydRealSaddleFactor, if_neg hzero]
    have hsq : 0 < u ^ 2 := sq_pos_of_ne_zero hzero
    apply (le_div_iff₀ hsq).2
    nlinarith

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_self_le
    {u : ℝ} (hu : 0 ≤ u) :
    u ≤ deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
  have hsqrt : 1 ≤ Real.sqrt (deBruijnNewmanPolymathBoydRealSaddleFactor u) := by
    simpa using Real.sqrt_le_sqrt
      (deBruijnNewmanPolymathBoydRealSaddleFactor_one_le hu)
  unfold deBruijnNewmanPolymathBoydRealSaddleCoordinate
  nlinarith

theorem tendsto_deBruijnNewmanPolymathBoydRealSaddleCoordinate_atTop :
    Tendsto deBruijnNewmanPolymathBoydRealSaddleCoordinate atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  exact deBruijnNewmanPolymathBoydRealSaddleCoordinate_self_le hu

theorem tendsto_deBruijnNewmanPolymathBoydRealSaddlePhase_atBot :
    Tendsto deBruijnNewmanPolymathBoydRealSaddlePhase atBot atTop := by
  have hlinear : Tendsto (fun u : ℝ => -u - 1) atBot atTop := by
    have hneg : Tendsto (fun u : ℝ => -u) atBot atTop := tendsto_neg_atBot_atTop
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atBot (-1 : ℝ) hneg
  refine tendsto_atTop_mono' atBot ?_ hlinear
  exact Filter.Eventually.of_forall fun u => by
    unfold deBruijnNewmanPolymathBoydRealSaddlePhase
    linarith [Real.exp_pos u]

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_eq_neg_sqrt
    {u : ℝ} (hu : u ≤ 0) :
    deBruijnNewmanPolymathBoydRealSaddleCoordinate u =
      -Real.sqrt (2 * deBruijnNewmanPolymathBoydRealSaddlePhase u) := by
  have hcoordinate : deBruijnNewmanPolymathBoydRealSaddleCoordinate u ≤ 0 := by
    unfold deBruijnNewmanPolymathBoydRealSaddleCoordinate
    exact mul_nonpos_of_nonpos_of_nonneg hu (Real.sqrt_nonneg _)
  have hsquare : deBruijnNewmanPolymathBoydRealSaddleCoordinate u ^ 2 =
      2 * deBruijnNewmanPolymathBoydRealSaddlePhase u := by
    nlinarith [deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq u]
  calc
    deBruijnNewmanPolymathBoydRealSaddleCoordinate u =
        -|deBruijnNewmanPolymathBoydRealSaddleCoordinate u| := by
      rw [abs_of_nonpos hcoordinate]
      ring
    _ = -Real.sqrt (deBruijnNewmanPolymathBoydRealSaddleCoordinate u ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ = -Real.sqrt (2 * deBruijnNewmanPolymathBoydRealSaddlePhase u) := by
      rw [hsquare]

theorem tendsto_deBruijnNewmanPolymathBoydRealSaddleCoordinate_atBot :
    Tendsto deBruijnNewmanPolymathBoydRealSaddleCoordinate atBot atBot := by
  have hphase : Tendsto
      (fun u : ℝ => 2 * deBruijnNewmanPolymathBoydRealSaddlePhase u) atBot atTop :=
    Tendsto.const_mul_atTop (by norm_num)
      tendsto_deBruijnNewmanPolymathBoydRealSaddlePhase_atBot
  have hsqrt : Tendsto
      (fun u : ℝ => Real.sqrt (2 * deBruijnNewmanPolymathBoydRealSaddlePhase u))
      atBot atTop := Real.tendsto_sqrt_atTop.comp hphase
  have hneg : Tendsto
      (fun u : ℝ => -Real.sqrt (2 * deBruijnNewmanPolymathBoydRealSaddlePhase u))
      atBot atBot := tendsto_neg_atTop_atBot.comp hsqrt
  apply hneg.congr'
  filter_upwards [eventually_le_atBot (0 : ℝ)] with u hu
  exact (deBruijnNewmanPolymathBoydRealSaddleCoordinate_eq_neg_sqrt hu).symm

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_differentiable :
    Differentiable ℝ deBruijnNewmanPolymathBoydRealSaddleCoordinate :=
  fun u => deBruijnNewmanPolymathBoydRealSaddleCoordinate_differentiableAt u

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_continuous :
    Continuous deBruijnNewmanPolymathBoydRealSaddleCoordinate :=
  deBruijnNewmanPolymathBoydRealSaddleCoordinate_differentiable.continuous

theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_surjective :
    Function.Surjective deBruijnNewmanPolymathBoydRealSaddleCoordinate :=
  deBruijnNewmanPolymathBoydRealSaddleCoordinate_continuous.surjective
    tendsto_deBruijnNewmanPolymathBoydRealSaddleCoordinate_atTop
    tendsto_deBruijnNewmanPolymathBoydRealSaddleCoordinate_atBot

/-- The normalized Boyd coordinate as an orientation-preserving order isomorphism of `ℝ`. -/
noncomputable def deBruijnNewmanPolymathBoydRealSaddleOrderIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective
    deBruijnNewmanPolymathBoydRealSaddleCoordinate
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_strictMono
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_surjective

@[simp]
theorem deBruijnNewmanPolymathBoydRealSaddleOrderIso_apply (u : ℝ) :
    deBruijnNewmanPolymathBoydRealSaddleOrderIso u =
      deBruijnNewmanPolymathBoydRealSaddleCoordinate u := by
  rfl

/-- The global real inverse of the normalized Boyd saddle coordinate. -/
noncomputable def deBruijnNewmanPolymathBoydRealSaddleInverse (w : ℝ) : ℝ :=
  deBruijnNewmanPolymathBoydRealSaddleOrderIso.symm w

@[simp]
theorem deBruijnNewmanPolymathBoydRealSaddleInverse_coordinate (u : ℝ) :
    deBruijnNewmanPolymathBoydRealSaddleInverse
        (deBruijnNewmanPolymathBoydRealSaddleCoordinate u) = u := by
  exact StrictMono.orderIsoOfSurjective_symm_apply_self
    deBruijnNewmanPolymathBoydRealSaddleCoordinate
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_strictMono
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_surjective u

@[simp]
theorem deBruijnNewmanPolymathBoydRealSaddleCoordinate_inverse (w : ℝ) :
    deBruijnNewmanPolymathBoydRealSaddleCoordinate
        (deBruijnNewmanPolymathBoydRealSaddleInverse w) = w := by
  exact StrictMono.orderIsoOfSurjective_self_symm_apply
    deBruijnNewmanPolymathBoydRealSaddleCoordinate
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_strictMono
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_surjective w

theorem deBruijnNewmanPolymathBoydRealSaddleInverse_continuous :
    Continuous deBruijnNewmanPolymathBoydRealSaddleInverse := by
  exact deBruijnNewmanPolymathBoydRealSaddleOrderIso.symm.continuous

theorem hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse (w : ℝ) :
    HasDerivAt deBruijnNewmanPolymathBoydRealSaddleInverse
      (deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate
        (deBruijnNewmanPolymathBoydRealSaddleInverse w))⁻¹ w := by
  have hforward : HasDerivAt deBruijnNewmanPolymathBoydRealSaddleCoordinate
      (deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate
        (deBruijnNewmanPolymathBoydRealSaddleInverse w))
      (deBruijnNewmanPolymathBoydRealSaddleInverse w) :=
    (deBruijnNewmanPolymathBoydRealSaddleCoordinate_differentiableAt _).hasDerivAt
  apply hforward.of_local_left_inverse
    deBruijnNewmanPolymathBoydRealSaddleInverse_continuous.continuousAt
    (deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_pos _).ne'
  exact Filter.Eventually.of_forall
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_inverse

theorem deriv_deBruijnNewmanPolymathBoydRealSaddleInverse (w : ℝ) :
    deriv deBruijnNewmanPolymathBoydRealSaddleInverse w =
      (deriv deBruijnNewmanPolymathBoydRealSaddleCoordinate
        (deBruijnNewmanPolymathBoydRealSaddleInverse w))⁻¹ :=
  (hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse w).deriv

theorem hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse_deriv (w : ℝ) :
    HasDerivAt deBruijnNewmanPolymathBoydRealSaddleInverse
      (deriv deBruijnNewmanPolymathBoydRealSaddleInverse w) w :=
  (hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse w).congr_deriv
    (deriv_deBruijnNewmanPolymathBoydRealSaddleInverse w).symm

theorem deriv_deBruijnNewmanPolymathBoydRealSaddleInverse_pos (w : ℝ) :
    0 < deriv deBruijnNewmanPolymathBoydRealSaddleInverse w := by
  rw [deriv_deBruijnNewmanPolymathBoydRealSaddleInverse]
  exact inv_pos.mpr
    (deriv_deBruijnNewmanPolymathBoydRealSaddleCoordinate_pos _)

theorem deBruijnNewmanPolymathBoydRealSaddleInverse_strictMono :
    StrictMono deBruijnNewmanPolymathBoydRealSaddleInverse := by
  exact deBruijnNewmanPolymathBoydRealSaddleOrderIso.symm.strictMono

theorem deBruijnNewmanPolymathBoydRealSaddleInverse_image_univ :
    deBruijnNewmanPolymathBoydRealSaddleInverse '' (Set.univ : Set ℝ) = Set.univ := by
  rw [Set.image_univ, Set.range_eq_univ]
  exact deBruijnNewmanPolymathBoydRealSaddleOrderIso.symm.surjective

/-- The exact Gaussian phase multiplied by the derivative of the global real inverse. -/
def deBruijnNewmanPolymathBoydGaussianSaddleIntegrand (x w : ℝ) : ℝ :=
  deriv deBruijnNewmanPolymathBoydRealSaddleInverse w * Real.exp (-x * w ^ 2 / 2)

theorem deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_eq_jacobian
    (x w : ℝ) :
    deriv deBruijnNewmanPolymathBoydRealSaddleInverse w •
        deBruijnNewmanPolymathBoydLogSaddleIntegrand x
          (deBruijnNewmanPolymathBoydRealSaddleInverse w) =
      deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w := by
  have hphase := deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq
    (deBruijnNewmanPolymathBoydRealSaddleInverse w)
  rw [deBruijnNewmanPolymathBoydRealSaddleCoordinate_inverse] at hphase
  simp only [smul_eq_mul, deBruijnNewmanPolymathBoydLogSaddleIntegrand,
    deBruijnNewmanPolymathBoydGaussianSaddleIntegrand]
  change deriv deBruijnNewmanPolymathBoydRealSaddleInverse w *
      Real.exp (-x * deBruijnNewmanPolymathBoydRealSaddlePhase
        (deBruijnNewmanPolymathBoydRealSaddleInverse w)) =
    deriv deBruijnNewmanPolymathBoydRealSaddleInverse w * Real.exp (-x * w ^ 2 / 2)
  rw [← hphase]
  congr 2
  ring

theorem deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_integrable
    {x : ℝ} (hx : 0 < x) :
    Integrable (deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x) := by
  have himage : IntegrableOn (deBruijnNewmanPolymathBoydLogSaddleIntegrand x)
      (deBruijnNewmanPolymathBoydRealSaddleInverse '' (Set.univ : Set ℝ)) := by
    rw [deBruijnNewmanPolymathBoydRealSaddleInverse_image_univ]
    exact integrableOn_univ.mpr
      (deBruijnNewmanPolymathBoydLogSaddleIntegrand_integrable hx)
  have hjac : IntegrableOn
      (fun w : ℝ => deriv deBruijnNewmanPolymathBoydRealSaddleInverse w •
        deBruijnNewmanPolymathBoydLogSaddleIntegrand x
          (deBruijnNewmanPolymathBoydRealSaddleInverse w)) Set.univ :=
    (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      MeasurableSet.univ
      (fun w _hw =>
        (hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse_deriv w).hasDerivWithinAt)
      (deBruijnNewmanPolymathBoydRealSaddleInverse_strictMono.monotone.monotoneOn Set.univ)
      (deBruijnNewmanPolymathBoydLogSaddleIntegrand x)).mp himage
  exact (integrableOn_univ.mp hjac).congr <| Filter.Eventually.of_forall fun w =>
    deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_eq_jacobian x w

theorem integral_deBruijnNewmanPolymathBoydGaussianSaddleIntegrand (x : ℝ) :
    (∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) =
      ∫ u : ℝ, deBruijnNewmanPolymathBoydLogSaddleIntegrand x u := by
  have hchange := integral_image_eq_integral_deriv_smul_of_monotoneOn
    MeasurableSet.univ
    (fun w _hw =>
      (hasDerivAt_deBruijnNewmanPolymathBoydRealSaddleInverse_deriv w).hasDerivWithinAt)
    (deBruijnNewmanPolymathBoydRealSaddleInverse_strictMono.monotone.monotoneOn Set.univ)
    (deBruijnNewmanPolymathBoydLogSaddleIntegrand x)
  rw [deBruijnNewmanPolymathBoydRealSaddleInverse_image_univ] at hchange
  calc
    (∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) =
        ∫ w : ℝ, deriv deBruijnNewmanPolymathBoydRealSaddleInverse w •
          deBruijnNewmanPolymathBoydLogSaddleIntegrand x
            (deBruijnNewmanPolymathBoydRealSaddleInverse w) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w =>
        (deBruijnNewmanPolymathBoydGaussianSaddleIntegrand_eq_jacobian x w).symm
    _ = ∫ u : ℝ, deBruijnNewmanPolymathBoydLogSaddleIntegrand x u := by
      simpa only [Measure.restrict_univ] using hchange.symm

theorem deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydGaussianSaddleIntegral
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : ℂ) =
      ((Real.sqrt (x / (2 * Real.pi)) *
        (∫ w : ℝ, deBruijnNewmanPolymathBoydGaussianSaddleIntegrand x w) : ℝ) : ℂ) := by
  rw [deBruijnNewmanPolymathScaledGamma_ofReal_eq_boydLogSaddleIntegral hx,
    integral_deBruijnNewmanPolymathBoydGaussianSaddleIntegrand]

/-- The integer translates of the logarithmic Gamma saddle. -/
def deBruijnNewmanPolymathBoydComplexSaddlePoint (n : ℤ) : ℂ :=
  (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)

@[simp]
theorem deBruijnNewmanPolymathBoydComplexSaddlePoint_exp (n : ℤ) :
    Complex.exp (deBruijnNewmanPolymathBoydComplexSaddlePoint n) = 1 := by
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem deBruijnNewmanPolymathBoydComplexSaddlePoint_ne_zero
    {n : ℤ} (hn : n ≠ 0) :
    deBruijnNewmanPolymathBoydComplexSaddlePoint n ≠ 0 := by
  unfold deBruijnNewmanPolymathBoydComplexSaddlePoint
  exact mul_ne_zero (Int.cast_ne_zero.mpr hn) <|
    mul_ne_zero (mul_ne_zero (by norm_num) <| ofReal_ne_zero.mpr Real.pi_ne_zero)
      Complex.I_ne_zero

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_saddle
    (n : ℤ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) =
      -deBruijnNewmanPolymathBoydComplexSaddlePoint n := by
  rw [deBruijnNewmanPolymathBoydComplexSaddlePhase,
    deBruijnNewmanPolymathBoydComplexSaddlePoint_exp]
  ring

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_saddle
    {n : ℤ} (hn : n ≠ 0) :
    deBruijnNewmanPolymathBoydComplexSaddleFactor
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) =
      Complex.I / ((n : ℂ) * (Real.pi : ℂ)) := by
  have hsaddle := deBruijnNewmanPolymathBoydComplexSaddlePoint_ne_zero hn
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor, if_neg hsaddle,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_saddle]
  unfold deBruijnNewmanPolymathBoydComplexSaddlePoint
  field_simp [Int.cast_ne_zero.mpr hn, Real.pi_ne_zero, Complex.I_ne_zero]
  rw [pow_two, Complex.I_mul_I]

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_saddle_mem_slitPlane
    {n : ℤ} (hn : n ≠ 0) :
    deBruijnNewmanPolymathBoydComplexSaddleFactor
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) ∈ Complex.slitPlane := by
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor_saddle hn,
    Complex.mem_slitPlane_iff]
  right
  have hden : ((n : ℂ) * (Real.pi : ℂ)) = (((n : ℝ) * Real.pi : ℝ) : ℂ) := by
    norm_cast
  rw [hden, div_eq_mul_inv, ← Complex.ofReal_inv]
  simp [Int.cast_ne_zero.mpr hn, Real.pi_ne_zero]

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_of_ne
    {u : ℂ} (hu : u ≠ 0) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
  have hdirect : AnalyticAt ℂ
      (fun z : ℂ => 2 * deBruijnNewmanPolymathBoydComplexSaddlePhase z / z ^ 2) u := by
    exact (analyticAt_const.mul
      (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt u)).div
        (analyticAt_id.pow 2) (pow_ne_zero 2 hu)
  apply hdirect.congr
  filter_upwards [eventually_ne_nhds hu] with z hz
  simp [deBruijnNewmanPolymathBoydComplexSaddleFactor, hz]

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_saddle
    {n : ℤ} (hn : n ≠ 0) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) := by
  have hfactor : AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleFactor
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) :=
    deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_of_ne
      (deBruijnNewmanPolymathBoydComplexSaddlePoint_ne_zero hn)
  have hsqrt : AnalyticAt ℂ Complex.sqrt
      (deBruijnNewmanPolymathBoydComplexSaddleFactor
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n)) :=
    Complex.differentiableOn_sqrt.analyticAt <|
      Complex.isOpen_slitPlane.mem_nhds <|
        deBruijnNewmanPolymathBoydComplexSaddleFactor_saddle_mem_slitPlane hn
  have hsqrtFactor : AnalyticAt ℂ
      deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) := by
    unfold deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor
    change AnalyticAt ℂ
      (Complex.sqrt ∘ deBruijnNewmanPolymathBoydComplexSaddleFactor)
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n)
    exact hsqrt.comp_of_eq hfactor rfl
  unfold deBruijnNewmanPolymathBoydComplexSaddleCoordinate
  exact analyticAt_id.mul hsqrtFactor

theorem deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_saddle
    {n : ℤ} (hn : n ≠ 0) :
    deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) = 0 := by
  let s := deBruijnNewmanPolymathBoydComplexSaddlePoint n
  have hsaddle : s ≠ 0 := deBruijnNewmanPolymathBoydComplexSaddlePoint_ne_zero hn
  have hcoordinate : AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate s :=
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_saddle hn
  have hcoordinate_ne : deBruijnNewmanPolymathBoydComplexSaddleCoordinate s ≠ 0 := by
    have hphase_ne : deBruijnNewmanPolymathBoydComplexSaddlePhase s ≠ 0 := by
      rw [show s = deBruijnNewmanPolymathBoydComplexSaddlePoint n by rfl,
        deBruijnNewmanPolymathBoydComplexSaddlePhase_saddle]
      exact neg_ne_zero.mpr hsaddle
    intro hzero
    apply hphase_ne
    rw [← deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq s, hzero]
    simp
  have hsquare : HasDerivAt
      (fun z : ℂ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate z ^ 2 / 2)
      (deBruijnNewmanPolymathBoydComplexSaddleCoordinate s *
        deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate s) s := by
    have hraw := (hcoordinate.differentiableAt.hasDerivAt.pow 2).div_const 2
    have hcoeff :
        (2 : ℂ) * deBruijnNewmanPolymathBoydComplexSaddleCoordinate s ^ (2 - 1) *
              deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate s / 2 =
            deBruijnNewmanPolymathBoydComplexSaddleCoordinate s *
              deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate s := by
      norm_num
      ring
    exact hraw.congr_deriv hcoeff
  have hphase : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddlePhase 0 s := by
    have hraw := deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt s
      |>.differentiableAt.hasDerivAt
    rw [deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase] at hraw
    apply hraw.congr_deriv
    change Complex.exp s - 1 = 0
    rw [show s = deBruijnNewmanPolymathBoydComplexSaddlePoint n by rfl,
      deBruijnNewmanPolymathBoydComplexSaddlePoint_exp]
    ring
  have hmul : deBruijnNewmanPolymathBoydComplexSaddleCoordinate s *
      deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate s = 0 :=
    (hphase.unique <| hsquare.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun z =>
        (deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq z).symm).symm
  exact (mul_eq_zero.mp hmul).resolve_left hcoordinate_ne

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle
    (n : ℤ) :
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) ^ 2 =
      -2 * deBruijnNewmanPolymathBoydComplexSaddlePoint n := by
  have hphase := deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq
    (deBruijnNewmanPolymathBoydComplexSaddlePoint n)
  rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_saddle] at hphase
  linear_combination 2 * hphase

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle_explicit
    (n : ℤ) :
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) ^ 2 =
      -4 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
  rw [deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle]
  unfold deBruijnNewmanPolymathBoydComplexSaddlePoint
  ring

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_critical
    {n : ℤ} (hn : n ≠ 0) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n) ∧
      deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) = 0 ∧
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) ^ 2 =
        -2 * deBruijnNewmanPolymathBoydComplexSaddlePoint n :=
  ⟨deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_saddle hn,
    deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_saddle hn,
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle n⟩

end

end LeanLab.Riemann
