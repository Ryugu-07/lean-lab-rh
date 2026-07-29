import LeanLab.Riemann.HardyComplexAlpha
import LeanLab.Riemann.HardyAbelMomentAmplification
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy's tangential theta limit

This module reconstructs Hardy's passage from equation (2) to equation (3) and the tangential
theta limit at `alpha = pi / 2`.
-/

open Complex Filter MeasureTheory Metric Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The upper-half-plane parameter in Hardy's equation (2). -/
def hardyThetaTau (alpha : ℂ) : ℂ :=
  Complex.I * Complex.exp (Complex.I * alpha)

/-- Translation of Hardy's theta parameter from the cusp `-1` to the cusp `0`. -/
def hardyThetaCuspSigma (alpha : ℂ) : ℂ :=
  hardyThetaTau alpha + 1

/-- The Poisson-inverted parameter at the cusp. -/
def hardyThetaCuspInv (alpha : ℂ) : ℂ :=
  -1 / hardyThetaCuspSigma alpha

/-- The branch-preserving square-root multiplier after inversion at the cusp. -/
def hardyThetaCuspMultiplier (alpha : ℂ) : ℂ :=
  1 /
    (-Complex.I * hardyThetaCuspSigma alpha) ^
      (1 / 2 : ℂ)

/-- Hardy's complete transformed theta prefactor, including the equation (2) normalization. -/
def hardyThetaCuspPrefactor (alpha : ℂ) : ℂ :=
  ((Real.pi / 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * alpha / 4) *
      hardyThetaCuspMultiplier alpha

/-- The theta boundary term appearing after solving Hardy's equation (2) for the Xi integral. -/
def hardyThetaBoundaryTerm (alpha : ℂ) : ℂ :=
  ((Real.pi / 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * alpha / 4) *
      hardyThetaAlpha alpha

/-- The half-integer theta constant produced by inversion at the cusp `-1`. -/
def jacobiThetaHalf (tau : ℂ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * tau / 4) *
    jacobiTheta₂ (tau / 2) tau

/-- One summand of the half-integer theta constant. -/
def jacobiThetaHalfTerm (n : ℤ) (tau : ℂ) : ℂ :=
  Complex.exp
    (Real.pi * Complex.I * ((n : ℂ) + 1 / 2) ^ 2 * tau)

private theorem differentiableAt_jacobiThetaHalf
    {tau : ℂ} (htau : 0 < tau.im) :
    DifferentiableAt ℂ jacobiThetaHalf tau := by
  have hpair :
      DifferentiableAt ℂ
        (fun w : ℂ => (w / 2, w)) tau := by
    fun_prop
  have hjacobi :
      DifferentiableAt ℂ
        (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2)
        (tau / 2, tau) :=
    (hasFDerivAt_jacobiTheta₂ (tau / 2) htau).differentiableAt
  unfold jacobiThetaHalf
  fun_prop

private theorem differentiableOn_jacobiThetaHalf :
    DifferentiableOn ℂ jacobiThetaHalf
      {tau : ℂ | 0 < tau.im} :=
  fun tau htau =>
    DifferentiableAt.differentiableWithinAt
      (s := {w : ℂ | 0 < w.im})
      (differentiableAt_jacobiThetaHalf
        (tau := tau) htau)

private theorem analyticOnNhd_jacobiThetaHalf :
    AnalyticOnNhd ℂ jacobiThetaHalf
      {tau : ℂ | 0 < tau.im} :=
  (analyticOnNhd_iff_differentiableOn
    (isOpen_lt continuous_const continuous_im)).2
      differentiableOn_jacobiThetaHalf

private theorem hasDerivAt_iteratedDeriv_jacobiThetaHalf
    (k : ℕ) {tau : ℂ} (htau : 0 < tau.im) :
    HasDerivAt
      (iteratedDeriv k jacobiThetaHalf)
      (iteratedDeriv (k + 1) jacobiThetaHalf tau) tau := by
  have hcont :
      ContDiffAt ℂ ⊤ jacobiThetaHalf tau :=
    (analyticOnNhd_jacobiThetaHalf tau htau).contDiffAt
  have hfderiv :
      DifferentiableAt ℂ
        (iteratedFDeriv ℂ k jacobiThetaHalf) tau :=
    hcont.differentiableAt_iteratedFDeriv (by simp)
  have hdiff :
      DifferentiableAt ℂ
        (iteratedDeriv k jacobiThetaHalf) tau := by
    rw [iteratedDeriv_eq_equiv_comp]
    fun_prop
  have hhas := hdiff.hasDerivAt
  have hderiv :
      deriv (iteratedDeriv k jacobiThetaHalf) tau =
        iteratedDeriv (k + 1) jacobiThetaHalf tau :=
    (congrFun (iteratedDeriv_succ
      (n := k) (f := jacobiThetaHalf)) tau).symm
  rw [hderiv] at hhas
  exact hhas

theorem jacobiThetaHalf_eq_tsum (tau : ℂ) :
    jacobiThetaHalf tau =
      ∑' n : ℤ, jacobiThetaHalfTerm n tau := by
  unfold jacobiThetaHalf jacobiThetaHalfTerm jacobiTheta₂
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  ring

theorem norm_jacobiThetaHalfTerm (n : ℤ) (tau : ℂ) :
    ‖jacobiThetaHalfTerm n tau‖ =
      Real.exp
        (-Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * tau.im) := by
  unfold jacobiThetaHalfTerm
  rw [Complex.norm_exp]
  congr 1
  rw [show
      (Real.pi : ℂ) * Complex.I *
            ((n : ℂ) + 1 / 2) ^ 2 * tau =
          (((Real.pi * ((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ)) *
            (tau * Complex.I) by
        push_cast
        ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.mul_I_re]
  ring

private theorem summable_norm_jacobiThetaHalfTerm
    {tau : ℂ} (htau : 0 < tau.im) :
    Summable (fun n : ℤ =>
      ‖jacobiThetaHalfTerm n tau‖) := by
  have hterms :
      Summable (fun n : ℤ =>
        jacobiTheta₂_term n (tau / 2) tau) :=
    (summable_jacobiTheta₂_term_iff
      (tau / 2) tau).mpr htau
  have hmul :
      Summable (fun n : ℤ =>
        Complex.exp
            (Real.pi * Complex.I * tau / 4) *
          jacobiTheta₂_term n (tau / 2) tau) :=
    hterms.mul_left _
  have heq :
      (fun n : ℤ =>
        Complex.exp
            (Real.pi * Complex.I * tau / 4) *
          jacobiTheta₂_term n (tau / 2) tau) =
        (fun n : ℤ => jacobiThetaHalfTerm n tau) := by
    funext n
    unfold jacobiThetaHalfTerm jacobiTheta₂_term
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [heq] at hmul
  exact hmul.norm

private theorem summable_jacobiThetaHalfTerm_norm_at_I :
    Summable (fun n : ℤ =>
      ‖jacobiThetaHalfTerm n Complex.I‖) :=
  summable_norm_jacobiThetaHalfTerm (by norm_num)

theorem hardyThetaAlpha_eq_jacobiTheta_hardyThetaTau (alpha : ℂ) :
    hardyThetaAlpha alpha = jacobiTheta (hardyThetaTau alpha) := by
  rfl

private theorem jacobiTheta₂_half_add_one (tau : ℂ) :
    jacobiTheta₂ (1 / 2) (tau + 1) = jacobiTheta tau := by
  unfold jacobiTheta₂ jacobiTheta₂_term jacobiTheta
  apply tsum_congr
  intro n
  obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
  have hparity : n ^ 2 + n = 2 * k := by
    nlinarith [hk]
  have hparityComplex :
      (n : ℂ) ^ 2 + (n : ℂ) = 2 * (k : ℂ) := by
    exact_mod_cast hparity
  rw [show
    2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2 : ℂ) +
          (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (tau + 1) =
        (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * tau +
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      calc
        2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (1 / 2 : ℂ) +
              (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * (tau + 1) =
            (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * tau +
              (Real.pi : ℂ) * Complex.I *
                ((n : ℂ) ^ 2 + (n : ℂ)) := by ring
        _ = (Real.pi : ℂ) * Complex.I * (n : ℂ) ^ 2 * tau +
              (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          rw [hparityComplex]
          ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring

theorem hardyThetaCuspSigma_im_pos
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    0 < (hardyThetaCuspSigma alpha).im := by
  simpa [hardyThetaCuspSigma, hardyThetaTau] using
    hardyThetaTau_im_pos halpha

theorem hardyThetaCuspSigma_ne_zero
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyThetaCuspSigma alpha ≠ 0 := by
  intro hzero
  have him : (hardyThetaCuspSigma alpha).im = 0 := by
    rw [hzero]
    rfl
  exact (ne_of_gt (hardyThetaCuspSigma_im_pos halpha)) him

private theorem hasDerivAt_hardyThetaCuspSigma (alpha : ℂ) :
    HasDerivAt hardyThetaCuspSigma
      (-Complex.exp (Complex.I * alpha)) alpha := by
  have hexp :
      HasDerivAt
        (fun beta : ℂ =>
          Complex.exp (Complex.I * beta))
        (Complex.exp (Complex.I * alpha) * Complex.I) alpha :=
    Complex.hasDerivAt_exp (Complex.I * alpha) |>.comp alpha <|
      hasDerivAt_const_mul Complex.I
  have htau :
      HasDerivAt hardyThetaTau
        (-Complex.exp (Complex.I * alpha)) alpha := by
    unfold hardyThetaTau
    have hmul := hexp.const_mul Complex.I
    have hderiv :
        Complex.I *
            (Complex.exp (Complex.I * alpha) * Complex.I) =
          -Complex.exp (Complex.I * alpha) := by
      calc
        Complex.I *
            (Complex.exp (Complex.I * alpha) * Complex.I) =
            (Complex.I * Complex.I) *
              Complex.exp (Complex.I * alpha) := by ring
        _ = -Complex.exp (Complex.I * alpha) := by
          rw [show Complex.I * Complex.I = (-1 : ℂ) by norm_num]
          ring
    rw [hderiv] at hmul
    exact hmul
  change
    HasDerivAt
      (fun beta : ℂ => hardyThetaTau beta + 1)
      (-Complex.exp (Complex.I * alpha)) alpha
  exact htau.add_const 1

private theorem hasDerivAt_hardyThetaCuspInv
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt hardyThetaCuspInv
      (-Complex.I * hardyThetaCuspInv alpha *
        (1 + hardyThetaCuspInv alpha)) alpha := by
  change
    HasDerivAt
      (fun beta : ℂ =>
        -1 / hardyThetaCuspSigma beta)
      (-Complex.I * hardyThetaCuspInv alpha *
        (1 + hardyThetaCuspInv alpha)) alpha
  have hsigma := hardyThetaCuspSigma_ne_zero halpha
  have hquot :=
    (hasDerivAt_const alpha (-1 : ℂ)).div
      (hasDerivAt_hardyThetaCuspSigma alpha) hsigma
  have hderiv :
      -Complex.I * hardyThetaCuspInv alpha *
          (1 + hardyThetaCuspInv alpha) =
        (0 * hardyThetaCuspSigma alpha -
            (-1 : ℂ) * (-Complex.exp (Complex.I * alpha))) /
          hardyThetaCuspSigma alpha ^ 2 := by
    unfold hardyThetaCuspInv
    field_simp [hsigma]
    simp only [hardyThetaCuspSigma, hardyThetaTau]
    rw [mul_zero, zero_sub]
    calc
      Complex.I *
          (Complex.I * Complex.exp (Complex.I * alpha) + 1 + -1) =
          (Complex.I * Complex.I) *
            Complex.exp (Complex.I * alpha) := by ring
      _ = -Complex.exp (Complex.I * alpha) := by
        rw [show Complex.I * Complex.I = (-1 : ℂ) by norm_num]
        ring
  rw [hderiv]
  exact hquot

private theorem hasDerivAt_hardyThetaCuspZ (alpha : ℂ) :
    HasDerivAt
      (fun beta : ℂ =>
        -Complex.I * hardyThetaCuspSigma beta)
      (Complex.I * Complex.exp (Complex.I * alpha)) alpha := by
  have hmul :=
    (hasDerivAt_hardyThetaCuspSigma alpha).const_mul
      (-Complex.I)
  have hderiv :
      -Complex.I *
          (-Complex.exp (Complex.I * alpha)) =
        Complex.I * Complex.exp (Complex.I * alpha) := by
    ring
  rw [hderiv] at hmul
  exact hmul

private theorem hardyThetaCuspZ_mem_slitPlane
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    -Complex.I * hardyThetaCuspSigma alpha ∈
      Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have him := hardyThetaCuspSigma_im_pos halpha
  simpa [Complex.mul_re] using him

private theorem hasDerivAt_hardyThetaCuspMultiplier
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt hardyThetaCuspMultiplier
      ((-Complex.I / 2) *
        (1 + hardyThetaCuspInv alpha) *
          hardyThetaCuspMultiplier alpha) alpha := by
  let z : ℂ → ℂ :=
    fun beta =>
      -Complex.I * hardyThetaCuspSigma beta
  have hzSlit : z alpha ∈ Complex.slitPlane := by
    exact hardyThetaCuspZ_mem_slitPlane halpha
  have hz0 : z alpha ≠ 0 :=
    Complex.slitPlane_ne_zero hzSlit
  have hcpow :
      HasDerivAt
        (fun beta : ℂ =>
          z beta ^ (-1 / 2 : ℂ))
        ((-1 / 2 : ℂ) *
          z alpha ^ ((-1 / 2 : ℂ) - 1) *
            (Complex.I *
              Complex.exp (Complex.I * alpha))) alpha :=
    (hasDerivAt_hardyThetaCuspZ alpha).cpow_const hzSlit
  have hfun :
      hardyThetaCuspMultiplier =
        (fun beta : ℂ =>
          z beta ^ (-1 / 2 : ℂ)) := by
    funext beta
    unfold hardyThetaCuspMultiplier
    dsimp only [z]
    rw [show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring,
      Complex.cpow_neg]
    simp only [one_div]
  have hsigma := hardyThetaCuspSigma_ne_zero halpha
  have hlog :
      (Complex.I * Complex.exp (Complex.I * alpha)) /
          z alpha =
        Complex.I * (1 + hardyThetaCuspInv alpha) := by
    dsimp only [z]
    unfold hardyThetaCuspInv
    field_simp [hsigma]
    simp only [hardyThetaCuspSigma, hardyThetaTau]
    calc
      -Complex.exp (Complex.I * alpha) =
          (Complex.I * Complex.I) *
            Complex.exp (Complex.I * alpha) := by
        rw [show Complex.I * Complex.I = (-1 : ℂ) by norm_num]
        ring
      _ = Complex.I *
          (Complex.I * Complex.exp (Complex.I * alpha) + 1 + -1) := by
        ring
  have hvalue :
      z alpha ^ (-1 / 2 : ℂ) =
        hardyThetaCuspMultiplier alpha := by
    rw [← congrFun hfun alpha]
  have hderiv :
      (-1 / 2 : ℂ) *
          z alpha ^ ((-1 / 2 : ℂ) - 1) *
            (Complex.I *
              Complex.exp (Complex.I * alpha)) =
        (-Complex.I / 2) *
          (1 + hardyThetaCuspInv alpha) *
            hardyThetaCuspMultiplier alpha := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
    rw [mul_assoc]
    rw [show
        z alpha ^ (-1 / 2 : ℂ) / z alpha *
              (Complex.I *
                Complex.exp (Complex.I * alpha)) =
            z alpha ^ (-1 / 2 : ℂ) *
              ((Complex.I *
                Complex.exp (Complex.I * alpha)) / z alpha) by
          field_simp]
    rw [hlog, hvalue]
    ring
  rw [← hvalue] at hderiv
  rw [hfun, ← hderiv]
  exact hcpow

private theorem hasDerivAt_hardyThetaCuspPrefactor
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt hardyThetaCuspPrefactor
      (hardyThetaCuspPrefactor alpha *
        (-Complex.I / 4 -
          (Complex.I / 2) *
            hardyThetaCuspInv alpha)) alpha := by
  have hinner :
      HasDerivAt
        (fun beta : ℂ =>
          Complex.I * beta / 4)
        (Complex.I / 4) alpha :=
    (hasDerivAt_const_mul Complex.I).div_const 4
  have hexp :
      HasDerivAt
        (fun beta : ℂ =>
          Complex.exp (Complex.I * beta / 4))
        ((Complex.I / 4) *
          Complex.exp (Complex.I * alpha / 4)) alpha := by
    have hcomp :=
      Complex.hasDerivAt_exp
        (Complex.I * alpha / 4) |>.comp alpha hinner
    have hderiv :
        Complex.exp (Complex.I * alpha / 4) *
            (Complex.I / 4) =
          (Complex.I / 4) *
            Complex.exp (Complex.I * alpha / 4) := by
      ring
    rw [hderiv] at hcomp
    exact hcomp
  let c : ℂ := ((Real.pi / 2 : ℝ) : ℂ)
  have hleft :=
    hexp.const_mul c
  have hprod :=
    hleft.mul
      (hasDerivAt_hardyThetaCuspMultiplier halpha)
  have hderiv :
      hardyThetaCuspPrefactor alpha *
          (-Complex.I / 4 -
            (Complex.I / 2) *
              hardyThetaCuspInv alpha) =
        (c *
            ((Complex.I / 4) *
              Complex.exp (Complex.I * alpha / 4))) *
              hardyThetaCuspMultiplier alpha +
          (c *
            Complex.exp (Complex.I * alpha / 4)) *
              ((-Complex.I / 2) *
                (1 + hardyThetaCuspInv alpha) *
                  hardyThetaCuspMultiplier alpha) := by
    unfold hardyThetaCuspPrefactor
    dsimp only [c]
    ring
  rw [hderiv]
  exact hprod

theorem hardyThetaCuspInv_im_pos
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    0 < (hardyThetaCuspInv alpha).im := by
  unfold hardyThetaCuspInv
  rw [show
      (-1 / hardyThetaCuspSigma alpha).im =
        (hardyThetaCuspSigma alpha).im /
          normSq (hardyThetaCuspSigma alpha) by
      rw [neg_div, neg_im, one_div, inv_im]
      ring]
  exact div_pos (hardyThetaCuspSigma_im_pos halpha)
    (normSq_pos.mpr (hardyThetaCuspSigma_ne_zero halpha))

theorem hardyThetaAlpha_eq_cusp_transform
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyThetaAlpha alpha =
      1 / (-Complex.I * hardyThetaCuspSigma alpha) ^ (1 / 2 : ℂ) *
        jacobiThetaHalf (hardyThetaCuspInv alpha) := by
  rw [hardyThetaAlpha_eq_jacobiTheta_hardyThetaTau,
    ← jacobiTheta₂_half_add_one (hardyThetaTau alpha)]
  change jacobiTheta₂ (1 / 2) (hardyThetaCuspSigma alpha) = _
  rw [jacobiTheta₂_functional_equation]
  unfold jacobiThetaHalf hardyThetaCuspInv
  have hsigma := hardyThetaCuspSigma_ne_zero halpha
  rw [show
      (1 / 2 : ℂ) / hardyThetaCuspSigma alpha =
        -((-1 / hardyThetaCuspSigma alpha) / 2) by
      field_simp,
    jacobiTheta₂_neg_left]
  have hexponent :
      -(Real.pi : ℂ) * Complex.I * (1 / 2 : ℂ) ^ 2 /
          hardyThetaCuspSigma alpha =
        (Real.pi : ℂ) * Complex.I *
          (-1 / hardyThetaCuspSigma alpha) / 4 := by
    field_simp
    ring
  rw [hexponent]
  ring

theorem hardyThetaBoundaryTerm_eq_cusp_transform
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyThetaBoundaryTerm alpha =
      hardyThetaCuspPrefactor alpha *
        jacobiThetaHalf (hardyThetaCuspInv alpha) := by
  unfold hardyThetaBoundaryTerm hardyThetaCuspPrefactor
  rw [hardyThetaAlpha_eq_cusp_transform halpha]
  unfold hardyThetaCuspMultiplier
  ring

private def hardyThetaCuspBasis
    (d k : ℕ) (alpha : ℂ) : ℂ :=
  hardyThetaCuspPrefactor alpha *
    hardyThetaCuspInv alpha ^ d *
      iteratedDeriv k jacobiThetaHalf
        (hardyThetaCuspInv alpha)

private theorem hasDerivAt_hardyThetaCuspBasis
    (d k : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt (hardyThetaCuspBasis d k)
      ((-Complex.I / 4) *
          hardyThetaCuspBasis d k alpha +
        (-Complex.I / 2) *
          hardyThetaCuspBasis (d + 1) k alpha +
        (-(d : ℂ) * Complex.I) *
          hardyThetaCuspBasis d k alpha +
        (-(d : ℂ) * Complex.I) *
          hardyThetaCuspBasis (d + 1) k alpha +
        (-Complex.I) *
          hardyThetaCuspBasis (d + 1) (k + 1) alpha +
        (-Complex.I) *
          hardyThetaCuspBasis (d + 2) (k + 1) alpha) alpha := by
  have hu :=
    hasDerivAt_hardyThetaCuspInv halpha
  have hpow :=
    hu.pow d
  have htheta :=
    (hasDerivAt_iteratedDeriv_jacobiThetaHalf k
      (hardyThetaCuspInv_im_pos halpha)).comp alpha hu
  have hraw :=
    ((hasDerivAt_hardyThetaCuspPrefactor halpha).mul hpow).mul
      htheta
  have hderiv :
      ((hardyThetaCuspPrefactor alpha *
            (-Complex.I / 4 -
              (Complex.I / 2) *
                hardyThetaCuspInv alpha)) *
            hardyThetaCuspInv alpha ^ d +
          hardyThetaCuspPrefactor alpha *
            ((d : ℂ) *
              hardyThetaCuspInv alpha ^ (d - 1) *
                (-Complex.I * hardyThetaCuspInv alpha *
                  (1 + hardyThetaCuspInv alpha)))) *
          iteratedDeriv k jacobiThetaHalf
            (hardyThetaCuspInv alpha) +
        (hardyThetaCuspPrefactor alpha *
            hardyThetaCuspInv alpha ^ d) *
          (iteratedDeriv (k + 1) jacobiThetaHalf
              (hardyThetaCuspInv alpha) *
            (-Complex.I * hardyThetaCuspInv alpha *
              (1 + hardyThetaCuspInv alpha))) =
        (-Complex.I / 4) *
            hardyThetaCuspBasis d k alpha +
          (-Complex.I / 2) *
            hardyThetaCuspBasis (d + 1) k alpha +
          (-(d : ℂ) * Complex.I) *
            hardyThetaCuspBasis d k alpha +
          (-(d : ℂ) * Complex.I) *
            hardyThetaCuspBasis (d + 1) k alpha +
          (-Complex.I) *
            hardyThetaCuspBasis (d + 1) (k + 1) alpha +
          (-Complex.I) *
            hardyThetaCuspBasis (d + 2) (k + 1) alpha := by
    cases d with
    | zero =>
        simp [hardyThetaCuspBasis]
        ring
    | succ d =>
        simp only [Nat.cast_add, Nat.cast_one,
          Nat.succ_sub_one]
        simp [hardyThetaCuspBasis, pow_succ]
        ring
  refine (hraw.congr_of_eventuallyEq ?_).congr_deriv hderiv
  filter_upwards with beta
  rfl

private structure HardyThetaCuspTerm where
  coeff : ℂ
  degree : ℕ
  order : ℕ

private def HardyThetaCuspTerm.eval
    (term : HardyThetaCuspTerm) (alpha : ℂ) : ℂ :=
  term.coeff *
    hardyThetaCuspBasis term.degree term.order alpha

private def HardyThetaCuspTerm.step
    (term : HardyThetaCuspTerm) :
    List HardyThetaCuspTerm :=
  [ { coeff := term.coeff * (-Complex.I / 4)
      degree := term.degree
      order := term.order },
    { coeff := term.coeff * (-Complex.I / 2)
      degree := term.degree + 1
      order := term.order },
    { coeff := term.coeff *
          (-(term.degree : ℂ) * Complex.I)
      degree := term.degree
      order := term.order },
    { coeff := term.coeff *
          (-(term.degree : ℂ) * Complex.I)
      degree := term.degree + 1
      order := term.order },
    { coeff := term.coeff * (-Complex.I)
      degree := term.degree + 1
      order := term.order + 1 },
    { coeff := term.coeff * (-Complex.I)
      degree := term.degree + 2
      order := term.order + 1 } ]

private theorem HardyThetaCuspTerm.hasDerivAt_eval
    (term : HardyThetaCuspTerm) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt term.eval
      ((term.step.map (fun next => next.eval alpha)).sum)
      alpha := by
  have hraw :=
    (hasDerivAt_hardyThetaCuspBasis
      term.degree term.order halpha).const_mul term.coeff
  refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with beta
    rfl
  · simp [HardyThetaCuspTerm.step,
      HardyThetaCuspTerm.eval]
    ring

private def hardyThetaCuspDerivativeTerms :
    ℕ → List HardyThetaCuspTerm
  | 0 =>
      [ { coeff := 1
          degree := 0
          order := 0 } ]
  | m + 1 =>
      (hardyThetaCuspDerivativeTerms m).flatMap
        HardyThetaCuspTerm.step

private def hardyThetaCuspDerivativeModel
    (m : ℕ) (alpha : ℂ) : ℂ :=
  ((hardyThetaCuspDerivativeTerms m).map
    (fun term => term.eval alpha)).sum

private theorem hasDerivAt_hardyThetaCuspTermList
    (terms : List HardyThetaCuspTerm)
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt
      (fun beta : ℂ =>
        (terms.map (fun term => term.eval beta)).sum)
      ((terms.flatMap HardyThetaCuspTerm.step).map
        (fun term => term.eval alpha) |>.sum)
      alpha := by
  induction terms with
  | nil =>
      simpa using hasDerivAt_const (x := alpha) (c := (0 : ℂ))
  | cons term terms ih =>
      refine
        (((term.hasDerivAt_eval halpha).add ih).congr_of_eventuallyEq
          ?_).congr_deriv ?_
      · filter_upwards with beta
        simp
      · simp [List.flatMap_cons]

private theorem hasDerivAt_hardyThetaCuspDerivativeModel
    (m : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt (hardyThetaCuspDerivativeModel m)
      (hardyThetaCuspDerivativeModel (m + 1) alpha)
      alpha := by
  unfold hardyThetaCuspDerivativeModel
  rw [hardyThetaCuspDerivativeTerms]
  exact hasDerivAt_hardyThetaCuspTermList
    (hardyThetaCuspDerivativeTerms m) halpha

private theorem iteratedDeriv_hardyThetaBoundaryTerm_eq_model
    (m : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    iteratedDeriv m hardyThetaBoundaryTerm alpha =
      hardyThetaCuspDerivativeModel m alpha := by
  induction m generalizing alpha with
  | zero =>
      rw [iteratedDeriv_zero]
      simp only [hardyThetaCuspDerivativeModel,
        hardyThetaCuspDerivativeTerms, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, add_zero,
        HardyThetaCuspTerm.eval, one_mul]
      simpa [hardyThetaCuspBasis] using
        hardyThetaBoundaryTerm_eq_cusp_transform halpha
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega,
        iteratedDeriv_succ]
      have heq :
          iteratedDeriv m hardyThetaBoundaryTerm =ᶠ[𝓝 alpha]
            hardyThetaCuspDerivativeModel m := by
        filter_upwards
            [isOpen_hardyAlphaStrip.mem_nhds halpha]
            with beta hbeta
        exact ih hbeta
      rw [heq.deriv_eq]
      exact
        (hasDerivAt_hardyThetaCuspDerivativeModel
          m halpha).deriv

theorem hardyThetaCuspSigma_ofReal_re (alpha : ℝ) :
    (hardyThetaCuspSigma (alpha : ℂ)).re =
      1 - Real.sin alpha := by
  simp [hardyThetaCuspSigma, hardyThetaTau, Complex.mul_re,
    Complex.exp_re, Complex.exp_im]
  ring

theorem hardyThetaCuspSigma_ofReal_im (alpha : ℝ) :
    (hardyThetaCuspSigma (alpha : ℂ)).im =
      Real.cos alpha := by
  simp [hardyThetaCuspSigma, hardyThetaTau, Complex.mul_im,
    Complex.exp_re, Complex.exp_im]

theorem normSq_hardyThetaCuspSigma_ofReal (alpha : ℝ) :
    normSq (hardyThetaCuspSigma (alpha : ℂ)) =
      2 * (1 - Real.sin alpha) := by
  rw [normSq_apply, hardyThetaCuspSigma_ofReal_re,
    hardyThetaCuspSigma_ofReal_im]
  nlinarith [Real.sin_sq_add_cos_sq alpha]

theorem hardyThetaCuspInv_ofReal_re
    {alpha : ℝ} (halpha : |alpha| < Real.pi / 2) :
    (hardyThetaCuspInv (alpha : ℂ)).re = -1 / 2 := by
  have hcos : 0 < Real.cos alpha := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp halpha)
  have hsin : Real.sin alpha < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  have hden : 1 - Real.sin alpha ≠ 0 :=
    ne_of_gt (sub_pos.mpr hsin)
  unfold hardyThetaCuspInv
  rw [neg_div, neg_re, one_div, inv_re,
    hardyThetaCuspSigma_ofReal_re,
    normSq_hardyThetaCuspSigma_ofReal]
  field_simp [hden]

theorem hardyThetaCuspInv_ofReal_im
    {alpha : ℝ} (halpha : |alpha| < Real.pi / 2) :
    (hardyThetaCuspInv (alpha : ℂ)).im =
      Real.cos alpha / (2 * (1 - Real.sin alpha)) := by
  have hcos : 0 < Real.cos alpha := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp halpha)
  have hsin : Real.sin alpha < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  unfold hardyThetaCuspInv
  rw [neg_div, neg_im, one_div, inv_im,
    hardyThetaCuspSigma_ofReal_im,
    normSq_hardyThetaCuspSigma_ofReal]
  ring

private theorem hardyThetaCuspInv_im_rationalized
    {alpha : ℝ} (halpha : |alpha| < Real.pi / 2) :
    Real.cos alpha / (2 * (1 - Real.sin alpha)) =
      (Real.cos alpha)⁻¹ * ((1 + Real.sin alpha) / 2) := by
  have hcos : Real.cos alpha ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo (abs_lt.mp halpha))
  have hsin : Real.sin alpha < 1 := by
    have hcosPos := Real.cos_pos_of_mem_Ioo (abs_lt.mp halpha)
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  have hden : 1 - Real.sin alpha ≠ 0 :=
    ne_of_gt (sub_pos.mpr hsin)
  field_simp [hcos, hden]
  nlinarith [Real.sin_sq_add_cos_sq alpha]

theorem tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two :
    Tendsto
      (fun alpha : ℝ =>
        (hardyThetaCuspInv (alpha : ℂ)).im)
      (𝓝[<] (Real.pi / 2)) atTop := by
  have hfactor :
      Tendsto
        (fun alpha : ℝ => (1 + Real.sin alpha) / 2)
        (𝓝[<] (Real.pi / 2)) (𝓝 1) := by
    convert
      (tendsto_const_nhds.add Real.tendsto_sin_pi_div_two).div_const 2 using 1
    norm_num
  have hmain :
      Tendsto
        (fun alpha : ℝ =>
          (Real.cos alpha)⁻¹ *
            ((1 + Real.sin alpha) / 2))
        (𝓝[<] (Real.pi / 2)) atTop :=
    Real.tendsto_cos_pi_div_two.inv_tendsto_nhdsGT_zero.atTop_mul_pos
      zero_lt_one hfactor
  apply hmain.congr'
  filter_upwards
      [Ioo_mem_nhdsLT (neg_lt_self Real.pi_div_two_pos)]
      with alpha halpha
  have hstrip : |alpha| < Real.pi / 2 :=
    abs_lt.mpr halpha
  rw [hardyThetaCuspInv_ofReal_im hstrip,
    hardyThetaCuspInv_im_rationalized hstrip]

private theorem intCast_add_half_ne_zero (n : ℤ) :
    (n : ℝ) + 1 / 2 ≠ 0 := by
  intro hzero
  have hcast : (2 * n : ℤ) = -1 := by
    exact_mod_cast (show (2 : ℝ) * n = -1 by linarith)
  omega

private theorem tendsto_one_add_pow_mul_exp_neg_mul_atTop
    (m : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun y : ℝ =>
        (1 + y) ^ m * Real.exp (-c * y))
      atTop (𝓝 0) := by
  have hshift :
      Tendsto (fun y : ℝ => y + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hbase :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (m : ℝ) c hc).comp hshift
  have hscaled := hbase.const_mul (Real.exp c)
  have hscaledZero :
      Tendsto
        (fun y : ℝ =>
          Real.exp c *
            ((y + 1) ^ (m : ℝ) *
              Real.exp (-c * (y + 1))))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using hscaled
  apply hscaledZero.congr'
  filter_upwards with y
  symm
  calc
    (1 + y) ^ m * Real.exp (-c * y) =
        (y + 1) ^ m *
          (Real.exp c * Real.exp (-c * (y + 1))) := by
      have hexp :
          Real.exp (-c * y) =
            Real.exp c * Real.exp (-c * (y + 1)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ = Real.exp c *
        ((y + 1) ^ (m : ℝ) *
          Real.exp (-c * (y + 1))) := by
      rw [Real.rpow_natCast]
      ring

private theorem one_quarter_le_intCast_add_half_sq (n : ℤ) :
    (1 / 4 : ℝ) ≤ ((n : ℝ) + 1 / 2) ^ 2 := by
  rcases le_or_gt 0 n with hn | hn
  · have hnReal : 0 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) + 1 / 2)]
  · have hnInt : n ≤ -1 := by omega
    have hnReal : (n : ℝ) ≤ -1 := by exact_mod_cast hnInt
    nlinarith [sq_nonneg ((n : ℝ) + 1 / 2)]

private def hardyThetaRapidConstant (m : ℕ) : ℝ :=
  Real.exp (Real.pi / 8) * (m.factorial : ℝ) *
    (((Real.pi / 8) ^ m)⁻¹)

private theorem hardyThetaRapidConstant_nonneg (m : ℕ) :
    0 ≤ hardyThetaRapidConstant m := by
  unfold hardyThetaRapidConstant
  positivity

private theorem pow_mul_exp_neg_mul_le_factorial_local
    (m : ℕ) {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    x ^ m * Real.exp (-b * x) ≤
      (m.factorial : ℝ) * (b ^ m)⁻¹ := by
  have hfactorial : 0 < (m.factorial : ℝ) := by positivity
  have hseries :=
    Real.pow_div_factorial_le_exp (b * x) (mul_nonneg hb.le hx) m
  have hpow :
      (b * x) ^ m ≤
        (m.factorial : ℝ) * Real.exp (b * x) := by
    simpa [mul_comm] using
      (div_le_iff₀ hfactorial).mp hseries
  have hscale :
      0 ≤ Real.exp (-b * x) * (b ^ m)⁻¹ := by
    positivity
  have hscaled :=
    mul_le_mul_of_nonneg_right hpow hscale
  calc
    x ^ m * Real.exp (-b * x) =
        (b * x) ^ m *
          (Real.exp (-b * x) * (b ^ m)⁻¹) := by
      rw [mul_pow]
      field_simp [hb.ne']
    _ ≤ ((m.factorial : ℝ) * Real.exp (b * x)) *
        (Real.exp (-b * x) * (b ^ m)⁻¹) :=
      hscaled
    _ = (m.factorial : ℝ) * (b ^ m)⁻¹ := by
      have hexp :
          Real.exp (b * x) * Real.exp (-b * x) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [show
        (m.factorial : ℝ) * Real.exp (b * x) *
              (Real.exp (-b * x) * (b ^ m)⁻¹) =
            (m.factorial : ℝ) *
              (Real.exp (b * x) * Real.exp (-b * x)) *
              (b ^ m)⁻¹ by ring,
        hexp]
      ring

private theorem one_add_pow_mul_exp_pi_div_eight_le
    (m : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ m * Real.exp (-(Real.pi / 8) * y) ≤
      hardyThetaRapidConstant m := by
  let b : ℝ := Real.pi / 8
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hx : 0 ≤ 1 + y := by linarith
  have hpoly :=
    pow_mul_exp_neg_mul_le_factorial_local m hb hx
  calc
    (1 + y) ^ m * Real.exp (-b * y) =
        Real.exp b *
          ((1 + y) ^ m *
            Real.exp (-b * (1 + y))) := by
      have hexp :
          Real.exp (-b * y) =
            Real.exp b * Real.exp (-b * (1 + y)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    _ ≤ Real.exp b *
        ((m.factorial : ℝ) * (b ^ m)⁻¹) := by
      gcongr
    _ = hardyThetaRapidConstant m := by
      unfold hardyThetaRapidConstant
      dsimp only [b]
      ring

private def hardyThetaGaussianMass : ℝ :=
  ∑' n : ℤ, ‖jacobiThetaHalfTerm n (Complex.I / 2)‖

private theorem hardyThetaGaussianMass_nonneg :
    0 ≤ hardyThetaGaussianMass := by
  unfold hardyThetaGaussianMass
  exact tsum_nonneg fun _ => norm_nonneg _

private theorem norm_jacobiThetaHalfTerm_le_gaussianMassTerm
    {tau : ℂ} {Y : ℝ} (hY : 2 ≤ Y)
    (htau : Y / 2 ≤ tau.im) (n : ℤ) :
    ‖jacobiThetaHalfTerm n tau‖ ≤
      Real.exp (-Real.pi * Y / 16) *
        ‖jacobiThetaHalfTerm n (Complex.I / 2)‖ := by
  let c : ℝ :=
    Real.pi * ((n : ℝ) + 1 / 2) ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos Real.pi_pos
      (sq_pos_of_ne_zero (intCast_add_half_ne_zero n))
  have hcLower : Real.pi / 4 ≤ c := by
    dsimp only [c]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [one_div] using
          one_quarter_le_intCast_add_half_sq n)
      Real.pi_pos.le
  have hY0 : 0 ≤ Y := by linarith
  have hsplit : Y / 4 + 1 / 2 ≤ tau.im := by
    calc
      Y / 4 + 1 / 2 ≤ Y / 2 := by linarith
      _ ≤ tau.im := htau
  have hproduct :
      Real.pi * Y / 16 + c / 2 ≤ c * tau.im := by
    calc
      Real.pi * Y / 16 + c / 2 ≤ c * (Y / 4) + c / 2 := by
        gcongr
        calc
          Real.pi * Y / 16 =
              (Real.pi / 4) * (Y / 4) := by ring
          _ ≤ c * (Y / 4) :=
            mul_le_mul_of_nonneg_right hcLower (by linarith)
      _ = c * (Y / 4 + 1 / 2) := by ring
      _ ≤ c * tau.im :=
        mul_le_mul_of_nonneg_left hsplit hc.le
  rw [norm_jacobiThetaHalfTerm,
    norm_jacobiThetaHalfTerm]
  have hIhalf : (Complex.I / 2).im = (1 / 2 : ℝ) := by
    norm_num
  rw [hIhalf]
  rw [show
      -Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * tau.im =
        -c * tau.im by
      dsimp only [c]
      ring,
    show
      -Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * (1 / 2) =
        -c * (1 / 2) by
      dsimp only [c]
      ring]
  change Real.exp (-c * tau.im) ≤
    Real.exp (-Real.pi * Y / 16) *
      Real.exp (-c * (1 / 2))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

private theorem norm_jacobiThetaHalf_le_gaussianMass
    {tau : ℂ} {Y : ℝ} (hY : 2 ≤ Y)
    (htau : Y / 2 ≤ tau.im) :
    ‖jacobiThetaHalf tau‖ ≤
      Real.exp (-Real.pi * Y / 16) *
        hardyThetaGaussianMass := by
  have htauPos : 0 < tau.im := by
    linarith
  have hsumTau :
      Summable (fun n : ℤ =>
        ‖jacobiThetaHalfTerm n tau‖) :=
    summable_norm_jacobiThetaHalfTerm htauPos
  have hsumBase :
      Summable (fun n : ℤ =>
        ‖jacobiThetaHalfTerm n (Complex.I / 2)‖) :=
    summable_norm_jacobiThetaHalfTerm (by norm_num)
  have hsumMajor :
      Summable (fun n : ℤ =>
        Real.exp (-Real.pi * Y / 16) *
          ‖jacobiThetaHalfTerm n (Complex.I / 2)‖) :=
    hsumBase.mul_left _
  rw [jacobiThetaHalf_eq_tsum]
  calc
    ‖∑' n : ℤ, jacobiThetaHalfTerm n tau‖ ≤
        ∑' n : ℤ, ‖jacobiThetaHalfTerm n tau‖ :=
      norm_tsum_le_tsum_norm hsumTau
    _ ≤
        ∑' n : ℤ,
          Real.exp (-Real.pi * Y / 16) *
            ‖jacobiThetaHalfTerm n (Complex.I / 2)‖ :=
      hsumTau.tsum_le_tsum
        (norm_jacobiThetaHalfTerm_le_gaussianMassTerm hY htau)
        hsumMajor
    _ = Real.exp (-Real.pi * Y / 16) *
        hardyThetaGaussianMass := by
      rw [tsum_mul_left]
      rfl

private theorem closedBall_subset_jacobiThetaHalf_domain
    {tau : ℂ} (htau : 0 < tau.im) :
    closedBall tau (tau.im / 2) ⊆
      {z : ℂ | 0 < z.im} := by
  intro z hz
  have hdist : ‖z - tau‖ ≤ tau.im / 2 := by
    simpa only [mem_closedBall, Complex.dist_eq] using hz
  have hdiff : tau.im - z.im ≤ ‖z - tau‖ := by
    calc
      tau.im - z.im = -(z - tau).im := by
        simp
      _ ≤ |(z - tau).im| := neg_le_abs _
      _ ≤ ‖z - tau‖ := Complex.abs_im_le_norm _
  change 0 < z.im
  linarith

private theorem diffContOnCl_jacobiThetaHalf_ball
    {tau : ℂ} (htau : 0 < tau.im) :
    DiffContOnCl ℂ jacobiThetaHalf
      (ball tau (tau.im / 2)) :=
  differentiableOn_jacobiThetaHalf.diffContOnCl_ball
    (closedBall_subset_jacobiThetaHalf_domain htau)

private theorem sphere_jacobiThetaHalf_im_lower
    {tau z : ℂ} (hz : z ∈ sphere tau (tau.im / 2)) :
    tau.im / 2 ≤ z.im := by
  have hdist : ‖z - tau‖ = tau.im / 2 := by
    simpa only [mem_sphere, Complex.dist_eq] using hz
  have hdiff : tau.im - z.im ≤ ‖z - tau‖ := by
    calc
      tau.im - z.im = -(z - tau).im := by
        simp
      _ ≤ |(z - tau).im| := neg_le_abs _
      _ ≤ ‖z - tau‖ := Complex.abs_im_le_norm _
  linarith

private theorem norm_iteratedDeriv_jacobiThetaHalf_le
    (k : ℕ) {tau : ℂ} (htau : 2 ≤ tau.im) :
    ‖iteratedDeriv k jacobiThetaHalf tau‖ ≤
      (k.factorial : ℝ) *
        (Real.exp (-Real.pi * tau.im / 16) *
          hardyThetaGaussianMass) := by
  have htauPos : 0 < tau.im := by linarith
  have hraw :=
    Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      k (by linarith : 0 < tau.im / 2)
      (diffContOnCl_jacobiThetaHalf_ball htauPos)
      (fun z hz =>
        norm_jacobiThetaHalf_le_gaussianMass htau
          (sphere_jacobiThetaHalf_im_lower hz))
  calc
    ‖iteratedDeriv k jacobiThetaHalf tau‖ ≤
        (k.factorial : ℝ) *
            (Real.exp (-Real.pi * tau.im / 16) *
              hardyThetaGaussianMass) /
          (tau.im / 2) ^ k :=
      hraw
    _ ≤
        (k.factorial : ℝ) *
          (Real.exp (-Real.pi * tau.im / 16) *
            hardyThetaGaussianMass) := by
      exact div_le_self
        (mul_nonneg (by positivity)
          (mul_nonneg (Real.exp_pos _).le
            hardyThetaGaussianMass_nonneg))
        (one_le_pow₀ (by linarith))

theorem tendsto_pow_mul_iteratedDeriv_jacobiThetaHalf_cusp
    (m k : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        (((1 +
            (hardyThetaCuspInv (alpha : ℂ)).im) ^ m : ℝ) : ℂ) *
          iteratedDeriv k jacobiThetaHalf
            (hardyThetaCuspInv (alpha : ℂ)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  let c : ℝ := Real.pi / 16
  let C : ℝ := (k.factorial : ℝ) * hardyThetaGaussianMass
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hbase :
      Tendsto
        (fun alpha : ℝ =>
          (1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m *
            Real.exp
              (-c *
                (hardyThetaCuspInv (alpha : ℂ)).im))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    (tendsto_one_add_pow_mul_exp_neg_mul_atTop m hc).comp
      tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two
  have hmajor :
      Tendsto
        (fun alpha : ℝ =>
          C *
            ((1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m *
              Real.exp
                (-c *
                  (hardyThetaCuspInv (alpha : ℂ)).im)))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (Eventually.of_forall fun alpha => norm_nonneg _) ?_ hmajor
  have hy :
      ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
        2 ≤ (hardyThetaCuspInv (alpha : ℂ)).im :=
    (tendsto_atTop.1
      tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two) 2
  filter_upwards [hy] with alpha halpha
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by linarith) m)]
  calc
    (1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m *
        ‖iteratedDeriv k jacobiThetaHalf
          (hardyThetaCuspInv (alpha : ℂ))‖ ≤
      (1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m *
        ((k.factorial : ℝ) *
          (Real.exp
              (-Real.pi *
                (hardyThetaCuspInv (alpha : ℂ)).im / 16) *
            hardyThetaGaussianMass)) :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedDeriv_jacobiThetaHalf_le k halpha)
        (pow_nonneg (by linarith) m)
    _ =
        C *
          ((1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m *
            Real.exp
              (-c *
                (hardyThetaCuspInv (alpha : ℂ)).im)) := by
      dsimp only [C, c]
      ring

private theorem weighted_norm_jacobiThetaHalfTerm_cusp_le
    (m : ℕ) {alpha : ℝ}
    (hy : 1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im)
    (n : ℤ) :
    ‖(((1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m : ℝ) : ℂ) *
        jacobiThetaHalfTerm n
          (hardyThetaCuspInv (alpha : ℂ))‖ ≤
      hardyThetaRapidConstant m *
        ‖jacobiThetaHalfTerm n (Complex.I / 2)‖ := by
  let y : ℝ := (hardyThetaCuspInv (alpha : ℂ)).im
  let c : ℝ := Real.pi * ((n : ℝ) + 1 / 2) ^ 2
  let b : ℝ := Real.pi / 8
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    linarith
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos Real.pi_pos
      (sq_pos_of_ne_zero (intCast_add_half_ne_zero n))
  have hcLower : Real.pi / 4 ≤ c := by
    dsimp only [c]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [one_div] using
          one_quarter_le_intCast_add_half_sq n)
      Real.pi_pos.le
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have htwoB : 2 * b ≤ c := by
    dsimp only [b]
    linarith
  have hcb : c / 2 ≤ c - b := by linarith
  have hcb0 : 0 ≤ c - b := by linarith
  have hscale : c / 2 ≤ (c - b) * y := by
    exact hcb.trans
      (le_mul_of_one_le_right hcb0 (by simpa only [y] using hy))
  have hexponent :
      -c * y ≤ -b * y + -(c / 2) := by
    linarith
  have hexp :
      Real.exp (-c * y) ≤
        Real.exp (-b * y) * Real.exp (-(c / 2)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent
  have habs :
      |(1 + y) ^ m| = (1 + y) ^ m := by
    rw [abs_of_nonneg (pow_nonneg (by linarith) _)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, habs,
    norm_jacobiThetaHalfTerm]
  rw [show
      -Real.pi * ((n : ℝ) + 1 / 2) ^ 2 * y =
        -c * y by
      dsimp only [c]
      ring]
  change
    (1 + y) ^ m * Real.exp (-c * y) ≤
      hardyThetaRapidConstant m *
        ‖jacobiThetaHalfTerm n (Complex.I / 2)‖
  calc
    (1 + y) ^ m * Real.exp (-c * y) ≤
        (1 + y) ^ m *
          (Real.exp (-b * y) * Real.exp (-(c / 2))) := by
      gcongr
    _ =
        ((1 + y) ^ m * Real.exp (-b * y)) *
          Real.exp (-(c / 2)) := by ring
    _ ≤ hardyThetaRapidConstant m *
          Real.exp (-(c / 2)) := by
      gcongr
      exact one_add_pow_mul_exp_pi_div_eight_le m hy0
    _ = hardyThetaRapidConstant m *
        ‖jacobiThetaHalfTerm n (Complex.I / 2)‖ := by
      have hIhalf : (Complex.I / 2).im = (1 / 2 : ℝ) := by
        norm_num
      rw [norm_jacobiThetaHalfTerm]
      rw [hIhalf]
      dsimp only [c]
      congr 2
      ring

private theorem tendsto_weighted_jacobiThetaHalfTerm_cusp
    (m : ℕ) (n : ℤ) :
    Tendsto
      (fun alpha : ℝ =>
        (((1 +
            (hardyThetaCuspInv (alpha : ℂ)).im) ^ m : ℝ) : ℂ) *
          jacobiThetaHalfTerm n
            (hardyThetaCuspInv (alpha : ℂ)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  let c : ℝ :=
    Real.pi * ((n : ℝ) + 1 / 2) ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos Real.pi_pos
      (sq_pos_of_ne_zero (intCast_add_half_ne_zero n))
  have hreal :
      Tendsto
        (fun alpha : ℝ =>
          (1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^ m *
            Real.exp
              (-c *
                (hardyThetaCuspInv (alpha : ℂ)).im))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    (tendsto_one_add_pow_mul_exp_neg_mul_atTop m hc).comp
      tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply hreal.congr'
  have hy :
      ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
        1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im :=
    (tendsto_atTop.1
      tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two) 1
  filter_upwards [hy] with alpha halpha
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (by linarith) m),
    norm_jacobiThetaHalfTerm]
  dsimp only [c]
  ring

theorem tendsto_pow_mul_jacobiThetaHalf_cusp (m : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        (((1 +
            (hardyThetaCuspInv (alpha : ℂ)).im) ^ m : ℝ) : ℂ) *
          jacobiThetaHalf
            (hardyThetaCuspInv (alpha : ℂ)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hsum :
      Summable (fun n : ℤ =>
        hardyThetaRapidConstant m *
          ‖jacobiThetaHalfTerm n (Complex.I / 2)‖) :=
    (summable_norm_jacobiThetaHalfTerm (by norm_num)).mul_left _
  have hbound :
      ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
        ∀ n : ℤ,
          ‖(((1 +
              (hardyThetaCuspInv (alpha : ℂ)).im) ^ m : ℝ) : ℂ) *
            jacobiThetaHalfTerm n
              (hardyThetaCuspInv (alpha : ℂ))‖ ≤
            hardyThetaRapidConstant m *
              ‖jacobiThetaHalfTerm n (Complex.I / 2)‖ := by
    have hy :
        ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
          1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im :=
      (tendsto_atTop.1
        tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two) 1
    filter_upwards [hy] with alpha halpha
    exact weighted_norm_jacobiThetaHalfTerm_cusp_le m halpha
  have htendsto :=
    tendsto_tsum_of_dominated_convergence
      hsum (tendsto_weighted_jacobiThetaHalfTerm_cusp m) hbound
  have htendstoZero :
      Tendsto
        (fun alpha : ℝ =>
          ∑' n : ℤ,
            (((1 +
                (hardyThetaCuspInv (alpha : ℂ)).im) ^ m : ℝ) : ℂ) *
              jacobiThetaHalfTerm n
                (hardyThetaCuspInv (alpha : ℂ)))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa only [tsum_zero] using htendsto
  apply htendstoZero.congr'
  filter_upwards with alpha
  rw [jacobiThetaHalf_eq_tsum, ← tsum_mul_left]

private theorem norm_hardyThetaCuspMultiplier_le
    {alpha : ℝ} (halpha : |alpha| < Real.pi / 2)
    (hy : 1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im) :
    ‖1 /
        (-Complex.I * hardyThetaCuspSigma (alpha : ℂ)) ^
          (1 / 2 : ℂ)‖ ≤
      1 + (hardyThetaCuspInv (alpha : ℂ)).im := by
  have halphaComplex : (alpha : ℂ) ∈ hardyAlphaStrip := by
    simpa [hardyAlphaStrip] using halpha
  have hsigma :
      hardyThetaCuspSigma (alpha : ℂ) ≠ 0 :=
    hardyThetaCuspSigma_ne_zero halphaComplex
  have hsigmaNormPos :
      0 < ‖hardyThetaCuspSigma (alpha : ℂ)‖ :=
    norm_pos_iff.mpr hsigma
  have hinvNorm :
      ‖hardyThetaCuspInv (alpha : ℂ)‖ =
        1 / ‖hardyThetaCuspSigma (alpha : ℂ)‖ := by
    simp [hardyThetaCuspInv]
  have honeInv :
      1 ≤ 1 / ‖hardyThetaCuspSigma (alpha : ℂ)‖ := by
    rw [← hinvNorm]
    exact hy.trans (Complex.im_le_norm _)
  have hsigmaNormLeOne :
      ‖hardyThetaCuspSigma (alpha : ℂ)‖ ≤ 1 := by
    have h := (le_div_iff₀ hsigmaNormPos).mp honeInv
    simpa using h
  have hsigmaNormLeSqrt :
      ‖hardyThetaCuspSigma (alpha : ℂ)‖ ≤
        ‖hardyThetaCuspSigma (alpha : ℂ)‖ ^ (1 / 2 : ℝ) :=
    Real.self_le_rpow_of_le_one hsigmaNormPos.le hsigmaNormLeOne
      (by norm_num)
  calc
    ‖1 /
        (-Complex.I * hardyThetaCuspSigma (alpha : ℂ)) ^
          (1 / 2 : ℂ)‖ =
        1 /
          ‖hardyThetaCuspSigma (alpha : ℂ)‖ ^ (1 / 2 : ℝ) := by
      have hhalf :
          (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        norm_num
      rw [norm_div, norm_one, hhalf, Complex.norm_cpow_real, norm_mul,
        norm_neg, Complex.norm_I, one_mul]
    _ ≤ 1 / ‖hardyThetaCuspSigma (alpha : ℂ)‖ :=
      one_div_le_one_div_of_le hsigmaNormPos hsigmaNormLeSqrt
    _ = ‖hardyThetaCuspInv (alpha : ℂ)‖ := hinvNorm.symm
    _ ≤
        |(hardyThetaCuspInv (alpha : ℂ)).re| +
          |(hardyThetaCuspInv (alpha : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + (hardyThetaCuspInv (alpha : ℂ)).im := by
      rw [hardyThetaCuspInv_ofReal_re halpha,
        abs_of_nonneg (by linarith : 0 ≤
          (hardyThetaCuspInv (alpha : ℂ)).im)]
      norm_num
    _ ≤ 1 + (hardyThetaCuspInv (alpha : ℂ)).im := by
      norm_num

private theorem norm_hardyThetaCuspInv_le
    {alpha : ℝ} (halpha : |alpha| < Real.pi / 2)
    (hy : 1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im) :
    ‖hardyThetaCuspInv (alpha : ℂ)‖ ≤
      1 + (hardyThetaCuspInv (alpha : ℂ)).im := by
  calc
    ‖hardyThetaCuspInv (alpha : ℂ)‖ ≤
        |(hardyThetaCuspInv (alpha : ℂ)).re| +
          |(hardyThetaCuspInv (alpha : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + (hardyThetaCuspInv (alpha : ℂ)).im := by
      rw [hardyThetaCuspInv_ofReal_re halpha,
        abs_of_nonneg (by linarith : 0 ≤
          (hardyThetaCuspInv (alpha : ℂ)).im)]
      norm_num
    _ ≤ 1 + (hardyThetaCuspInv (alpha : ℂ)).im := by
      norm_num

private theorem norm_hardyThetaCuspPrefactor_le
    {alpha : ℝ} (halpha : |alpha| < Real.pi / 2)
    (hy : 1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im) :
    ‖hardyThetaCuspPrefactor (alpha : ℂ)‖ ≤
      (Real.pi / 2) *
        (1 + (hardyThetaCuspInv (alpha : ℂ)).im) := by
  have hmult :
      ‖hardyThetaCuspMultiplier (alpha : ℂ)‖ ≤
        1 + (hardyThetaCuspInv (alpha : ℂ)).im := by
    simpa only [hardyThetaCuspMultiplier] using
      norm_hardyThetaCuspMultiplier_le halpha hy
  have hexp :
      ‖Complex.exp
          (Complex.I * (alpha : ℂ) / 4)‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (Complex.I * (alpha : ℂ) / 4).re = 0 := by
      norm_num [Complex.div_re, Complex.mul_re]
    rw [hre, Real.exp_zero]
  unfold hardyThetaCuspPrefactor
  rw [norm_mul, norm_mul, hexp,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.pi / 2),
    mul_one]
  exact mul_le_mul_of_nonneg_left hmult (by positivity)

private theorem tendsto_hardyThetaCuspTerm_eval
    (term : HardyThetaCuspTerm) :
    Tendsto
      (fun alpha : ℝ => term.eval (alpha : ℂ))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  let C : ℝ := ‖term.coeff‖ * (Real.pi / 2)
  have hweighted :=
    tendsto_pow_mul_iteratedDeriv_jacobiThetaHalf_cusp
      (term.degree + 1) term.order
  have hweightedNorm :
      Tendsto
        (fun alpha : ℝ =>
          ‖(((1 +
              (hardyThetaCuspInv (alpha : ℂ)).im) ^
                (term.degree + 1) : ℝ) : ℂ) *
            iteratedDeriv term.order jacobiThetaHalf
              (hardyThetaCuspInv (alpha : ℂ))‖)
        (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hweighted
  have hmajor :
      Tendsto
        (fun alpha : ℝ =>
          C *
            ‖(((1 +
                (hardyThetaCuspInv (alpha : ℂ)).im) ^
                  (term.degree + 1) : ℝ) : ℂ) *
              iteratedDeriv term.order jacobiThetaHalf
                (hardyThetaCuspInv (alpha : ℂ))‖)
        (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
    simpa only [mul_zero] using hweightedNorm.const_mul C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (Eventually.of_forall fun alpha => norm_nonneg _) ?_ hmajor
  have hy :
      ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
        1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im :=
    (tendsto_atTop.1
      tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two) 1
  filter_upwards
      [hy, Ioo_mem_nhdsLT (neg_lt_self Real.pi_div_two_pos)]
      with alpha halpha hstrip
  have habs : |alpha| < Real.pi / 2 :=
    abs_lt.mpr hstrip
  have hbase :
      0 ≤ 1 + (hardyThetaCuspInv (alpha : ℂ)).im := by
    linarith
  unfold HardyThetaCuspTerm.eval hardyThetaCuspBasis
  rw [norm_mul, norm_mul, norm_mul, norm_pow]
  calc
    ‖term.coeff‖ *
          (‖hardyThetaCuspPrefactor (alpha : ℂ)‖ *
            ‖hardyThetaCuspInv (alpha : ℂ)‖ ^ term.degree *
              ‖iteratedDeriv term.order jacobiThetaHalf
                (hardyThetaCuspInv (alpha : ℂ))‖) ≤
        ‖term.coeff‖ *
          (((Real.pi / 2) *
              (1 + (hardyThetaCuspInv (alpha : ℂ)).im)) *
            (1 + (hardyThetaCuspInv (alpha : ℂ)).im) ^
              term.degree *
              ‖iteratedDeriv term.order jacobiThetaHalf
                (hardyThetaCuspInv (alpha : ℂ))‖) := by
      gcongr
      · exact norm_hardyThetaCuspPrefactor_le habs halpha
      · exact norm_hardyThetaCuspInv_le habs halpha
    _ =
        C *
          ‖(((1 +
              (hardyThetaCuspInv (alpha : ℂ)).im) ^
                (term.degree + 1) : ℝ) : ℂ) *
            iteratedDeriv term.order jacobiThetaHalf
              (hardyThetaCuspInv (alpha : ℂ))‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg hbase _)]
      dsimp only [C]
      rw [pow_succ]
      ring

private theorem tendsto_hardyThetaCuspTermList
    (terms : List HardyThetaCuspTerm) :
    Tendsto
      (fun alpha : ℝ =>
        (terms.map
          (fun term => term.eval (alpha : ℂ))).sum)
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  induction terms with
  | nil =>
      simp
  | cons term terms ih =>
      simpa using
        (tendsto_hardyThetaCuspTerm_eval term).add ih

private theorem tendsto_hardyThetaCuspDerivativeModel
    (m : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        hardyThetaCuspDerivativeModel m (alpha : ℂ))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  unfold hardyThetaCuspDerivativeModel
  exact tendsto_hardyThetaCuspTermList
    (hardyThetaCuspDerivativeTerms m)

theorem tendsto_iteratedDeriv_hardyThetaBoundaryTerm_all
    (m : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        iteratedDeriv m hardyThetaBoundaryTerm (alpha : ℂ))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hmodel :=
    tendsto_hardyThetaCuspDerivativeModel m
  apply hmodel.congr'
  filter_upwards
      [Ioo_mem_nhdsLT (neg_lt_self Real.pi_div_two_pos)]
      with alpha hstrip
  have halpha : (alpha : ℂ) ∈ hardyAlphaStrip := by
    simpa [hardyAlphaStrip] using
      (abs_lt.mpr hstrip)
  exact
    (iteratedDeriv_hardyThetaBoundaryTerm_eq_model
      m halpha).symm

theorem tendsto_iteratedDeriv_hardyThetaBoundaryTerm
    (p : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        iteratedDeriv (2 * p) hardyThetaBoundaryTerm
          (alpha : ℂ))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
  tendsto_iteratedDeriv_hardyThetaBoundaryTerm_all (2 * p)

theorem tendsto_hardyThetaAlpha_ofReal_at_pi_div_two :
    Tendsto
      (fun alpha : ℝ => hardyThetaAlpha (alpha : ℂ))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hmajor :=
    tendsto_pow_mul_jacobiThetaHalf_cusp 1
  have hmajorNorm :
      Tendsto
        (fun alpha : ℝ =>
          ‖(((1 +
              (hardyThetaCuspInv (alpha : ℂ)).im) ^ 1 : ℝ) : ℂ) *
            jacobiThetaHalf
              (hardyThetaCuspInv (alpha : ℂ))‖)
        (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hmajor
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (Eventually.of_forall fun alpha => norm_nonneg _) ?_ hmajorNorm
  have hy :
      ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
        1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im :=
    (tendsto_atTop.1
      tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two) 1
  filter_upwards
      [hy, Ioo_mem_nhdsLT (neg_lt_self Real.pi_div_two_pos)]
      with alpha halpha hstrip
  have habs : |alpha| < Real.pi / 2 :=
    abs_lt.mpr hstrip
  have halphaComplex : (alpha : ℂ) ∈ hardyAlphaStrip := by
    simpa [hardyAlphaStrip] using habs
  rw [hardyThetaAlpha_eq_cusp_transform halphaComplex, norm_mul]
  calc
    ‖1 /
        (-Complex.I * hardyThetaCuspSigma (alpha : ℂ)) ^
          (1 / 2 : ℂ)‖ *
          ‖jacobiThetaHalf
            (hardyThetaCuspInv (alpha : ℂ))‖ ≤
        (1 + (hardyThetaCuspInv (alpha : ℂ)).im) *
          ‖jacobiThetaHalf
            (hardyThetaCuspInv (alpha : ℂ))‖ :=
      mul_le_mul_of_nonneg_right
        (norm_hardyThetaCuspMultiplier_le habs halpha)
        (norm_nonneg _)
    _ =
        ‖(((1 +
            (hardyThetaCuspInv (alpha : ℂ)).im) ^ 1 : ℝ) : ℂ) *
          jacobiThetaHalf
            (hardyThetaCuspInv (alpha : ℂ))‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (pow_nonneg (by linarith) 1)]
      simp only [pow_one]

private theorem tendsto_jacobiThetaHalfTerm_cusp
    (n : ℤ) :
    Tendsto
      (fun alpha : ℝ =>
        jacobiThetaHalfTerm n
          (hardyThetaCuspInv (alpha : ℂ)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  let c : ℝ :=
    Real.pi * ((n : ℝ) + 1 / 2) ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos Real.pi_pos
      (sq_pos_of_ne_zero (intCast_add_half_ne_zero n))
  have hlinear :
      Tendsto
        (fun alpha : ℝ =>
          -c * (hardyThetaCuspInv (alpha : ℂ)).im)
        (𝓝[<] (Real.pi / 2)) atBot :=
    tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two.const_mul_atTop_of_neg
      (neg_lt_zero.mpr hc)
  have hexp :
      Tendsto
        (fun alpha : ℝ =>
          Real.exp
            (-c * (hardyThetaCuspInv (alpha : ℂ)).im))
        (𝓝[<] (Real.pi / 2)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlinear
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert hexp using 1
  ext alpha
  rw [norm_jacobiThetaHalfTerm]
  dsimp only [c]
  ring

theorem tendsto_jacobiThetaHalf_cusp :
    Tendsto
      (fun alpha : ℝ =>
        jacobiThetaHalf
          (hardyThetaCuspInv (alpha : ℂ)))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  have hbound :
      ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
        ∀ n : ℤ,
          ‖jacobiThetaHalfTerm n
              (hardyThetaCuspInv (alpha : ℂ))‖ ≤
            ‖jacobiThetaHalfTerm n Complex.I‖ := by
    have hy :
        ∀ᶠ alpha : ℝ in 𝓝[<] (Real.pi / 2),
          1 ≤ (hardyThetaCuspInv (alpha : ℂ)).im :=
      (tendsto_atTop.1
        tendsto_hardyThetaCuspInv_ofReal_im_at_pi_div_two) 1
    filter_upwards [hy] with alpha halpha
    intro n
    rw [norm_jacobiThetaHalfTerm,
      norm_jacobiThetaHalfTerm, Complex.I_im]
    apply Real.exp_le_exp.mpr
    have hsquare :
        0 ≤ ((n : ℝ) + 1 / 2) ^ 2 := sq_nonneg _
    have hcoeff :
        -Real.pi * ((n : ℝ) + 1 / 2) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr Real.pi_pos.le) hsquare
    exact mul_le_mul_of_nonpos_left halpha hcoeff
  have htendsto :=
    tendsto_tsum_of_dominated_convergence
      summable_jacobiThetaHalfTerm_norm_at_I
      tendsto_jacobiThetaHalfTerm_cusp hbound
  simpa only [← jacobiThetaHalf_eq_tsum, tsum_zero] using htendsto

end

end LeanLab.Riemann
