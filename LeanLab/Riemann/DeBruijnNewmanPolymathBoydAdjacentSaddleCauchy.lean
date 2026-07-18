import LeanLab.Riemann.DeBruijnNewmanPolymathBoydRealSaddleDiffeomorphism
import Mathlib.Analysis.Complex.CauchyIntegral

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The first complex continuation barrier for Boyd's Gamma saddle coordinate

This module computes the norm of every nonzero critical image and isolates the exact obstruction
to extending the origin inverse branch through either adjacent image. It does not assume a global
complex inverse or Boyd--Nemes equation (15).
-/

namespace LeanLab.Riemann

open Complex Filter Metric Set
open scoped Topology

noncomputable section

/-- The image of an integer Gamma saddle under the normalized Boyd coordinate. -/
def deBruijnNewmanPolymathBoydComplexSaddleImage (n : ℤ) : ℂ :=
  deBruijnNewmanPolymathBoydComplexSaddleCoordinate
    (deBruijnNewmanPolymathBoydComplexSaddlePoint n)

theorem norm_deBruijnNewmanPolymathBoydComplexSaddleImage_sq
    (n : ℤ) :
    ‖deBruijnNewmanPolymathBoydComplexSaddleImage n‖ ^ 2 =
      4 * Real.pi * |(n : ℝ)| := by
  rw [← norm_pow, deBruijnNewmanPolymathBoydComplexSaddleImage,
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle_explicit]
  simp [abs_of_pos Real.pi_pos]

theorem norm_deBruijnNewmanPolymathBoydComplexSaddleImage_one :
    ‖deBruijnNewmanPolymathBoydComplexSaddleImage 1‖ =
      2 * Real.sqrt Real.pi := by
  have hsquare := norm_deBruijnNewmanPolymathBoydComplexSaddleImage_sq 1
  have hnonneg : 0 ≤ ‖deBruijnNewmanPolymathBoydComplexSaddleImage 1‖ := norm_nonneg _
  have hsqrtNonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  norm_num at hsquare
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

theorem norm_deBruijnNewmanPolymathBoydComplexSaddleImage_neg_one :
    ‖deBruijnNewmanPolymathBoydComplexSaddleImage (-1)‖ =
      2 * Real.sqrt Real.pi := by
  have hsquare := norm_deBruijnNewmanPolymathBoydComplexSaddleImage_sq (-1)
  have hnonneg : 0 ≤ ‖deBruijnNewmanPolymathBoydComplexSaddleImage (-1)‖ := norm_nonneg _
  have hsqrtNonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  norm_num at hsquare
  nlinarith [Real.sq_sqrt Real.pi_pos.le]

theorem deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero
    {n : ℤ} (hn : n ≠ 0) :
    deBruijnNewmanPolymathBoydComplexSaddleImage n ≠ 0 := by
  intro hzero
  have hsquare := deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle n
  rw [← deBruijnNewmanPolymathBoydComplexSaddleImage, hzero] at hsquare
  have hsaddleZero : deBruijnNewmanPolymathBoydComplexSaddlePoint n = 0 := by
    simpa using hsquare.symm
  exact deBruijnNewmanPolymathBoydComplexSaddlePoint_ne_zero hn hsaddleZero

/-- The integer saddles are exactly all critical points of the complex Gamma phase. -/
theorem deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff
    (u : ℂ) :
    deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u = 0 ↔
      ∃ n : ℤ, u = deBruijnNewmanPolymathBoydComplexSaddlePoint n := by
  rw [deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase, sub_eq_zero,
    Complex.exp_eq_one_iff]
  rfl

/-- Every nonzero critical value of the Gamma phase has norm at least `2*pi`. -/
theorem two_pi_le_norm_deBruijnNewmanPolymathBoydComplexSaddlePhase_of_critical
    {u : ℂ} (hu : u ≠ 0)
    (hcritical : deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u = 0) :
    2 * Real.pi ≤ ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ := by
  obtain ⟨n, rfl⟩ :=
    (deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff u).mp hcritical
  have hn : n ≠ 0 := by
    intro hn
    apply hu
    simp [hn, deBruijnNewmanPolymathBoydComplexSaddlePoint]
  have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
    have habsInt : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast habsInt
  rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_saddle, norm_neg]
  unfold deBruijnNewmanPolymathBoydComplexSaddlePoint
  simp only [norm_mul, norm_intCast, norm_ofNat, norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one]
  rw [abs_of_pos Real.pi_pos]
  nlinarith [Real.pi_pos]

/-- There are no nonzero critical points above the open phase disk of radius `2*pi`. -/
theorem deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_ne_zero_of_norm_lt_two_pi
    {u : ℂ} (hu : u ≠ 0)
    (hvalue : ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ < 2 * Real.pi) :
    deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u ≠ 0 := by
  intro hcritical
  exact (not_lt_of_ge
    (two_pi_le_norm_deBruijnNewmanPolymathBoydComplexSaddlePhase_of_critical hu hcritical)) hvalue

/-- A critical saddle admits no differentiable local left inverse of the normalized coordinate. -/
theorem not_differentiableAt_leftInverse_at_boydComplexSaddle
    {n : ℤ} (hn : n ≠ 0) (U : ℂ → ℂ)
    (hleft :
      (U ∘ deBruijnNewmanPolymathBoydComplexSaddleCoordinate) =ᶠ[
        𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint n)] id) :
    ¬DifferentiableAt ℂ U (deBruijnNewmanPolymathBoydComplexSaddleImage n) := by
  intro hU
  have hw : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddleCoordinate 0
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) :=
    (deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_saddle hn).differentiableAt
      |>.hasDerivAt.congr_deriv
        (deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_saddle hn)
  have hcomp : HasDerivAt
      (U ∘ deBruijnNewmanPolymathBoydComplexSaddleCoordinate) 0
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) := by
    exact (hU.hasDerivAt.comp (deBruijnNewmanPolymathBoydComplexSaddlePoint n) hw).congr_deriv
      (mul_zero _)
  have hid : HasDerivAt
      (fun u : ℂ => u) 1 (deBruijnNewmanPolymathBoydComplexSaddlePoint n) :=
    hasDerivAt_id _
  have hcompOne : HasDerivAt
      (U ∘ deBruijnNewmanPolymathBoydComplexSaddleCoordinate) 1
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) :=
    hid.congr_of_eventuallyEq hleft
  exact zero_ne_one (hcomp.unique hcompOne)

/-- Local agreement with the compiled inverse forces the phase equation across a connected disk. -/
theorem deBruijnNewmanPolymathBoydOriginInverseBranch_phaseOn_ball
    {U : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hU : AnalyticOnNhd ℂ U (ball 0 R))
    (hlocal : U =ᶠ[𝓝 0] deBruijnNewmanPolymathBoydComplexSaddleLocalInverse) :
    EqOn
      (fun z => deBruijnNewmanPolymathBoydComplexSaddlePhase (U z))
      (fun z : ℂ => z ^ 2 / 2) (ball 0 R) := by
  have hlocalPhase :
      (fun z => deBruijnNewmanPolymathBoydComplexSaddlePhase (U z)) =ᶠ[𝓝 0]
        fun z : ℂ => z ^ 2 / 2 := by
    filter_upwards [hlocal,
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_right] with z hzU hzright
    rw [hzU, ← deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq]
    simp [hzright]
  have hphaseAnalytic : AnalyticOnNhd ℂ
      (fun z => deBruijnNewmanPolymathBoydComplexSaddlePhase (U z)) (ball 0 R) :=
    fun z hz => (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt (U z)).comp (hU z hz)
  have hquadraticAnalytic : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2 / 2) (ball 0 R) := by
    intro z hz
    fun_prop
  exact hphaseAnalytic.eqOn_of_preconnected_of_eventuallyEq hquadraticAnalytic
    (convex_ball (0 : ℂ) R).isPreconnected (mem_ball_self hR) hlocalPhase

/-- The inverse Jacobian has its Cauchy power series on every closed subdisk of an analytic
origin branch. -/
theorem deBruijnNewmanPolymathBoydOriginInverseJacobian_hasCauchyPowerSeriesOnBall
    {U : ℂ → ℂ} {R : ℝ} (hU : AnalyticOnNhd ℂ U (ball 0 R))
    {r : NNReal} (hr0 : 0 < r) (hr : (r : ℝ) < R) :
    HasFPowerSeriesOnBall (deriv U) (cauchyPowerSeries (deriv U) 0 r) 0 r := by
  have hd : DifferentiableOn ℂ (deriv U) (closedBall 0 (r : ℝ)) := by
    intro z hz
    have hzR : z ∈ ball (0 : ℂ) R := by
      have hzr : ‖z‖ ≤ (r : ℝ) := by simpa [mem_closedBall, dist_zero_right] using hz
      simpa [mem_ball, dist_zero_right] using hzr.trans_lt hr
    exact (hU.deriv z hzR).differentiableAt.differentiableWithinAt
  exact hd.hasFPowerSeriesOnBall hr0

theorem deBruijnNewmanPolymathBoydComplexSaddleImage_norm_of_adjacent
    {n : ℤ} (hn : n = 1 ∨ n = -1) :
    ‖deBruijnNewmanPolymathBoydComplexSaddleImage n‖ =
      2 * Real.sqrt Real.pi := by
  rcases hn with rfl | rfl
  · exact norm_deBruijnNewmanPolymathBoydComplexSaddleImage_one
  · exact norm_deBruijnNewmanPolymathBoydComplexSaddleImage_neg_one

/-- Any analytic origin branch which lands at an adjacent saddle has centered radius at most the
norm of the adjacent critical images. -/
theorem deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent
    {U : ℂ → ℂ} {R : ℝ} {n : ℤ} (hn : n = 1 ∨ n = -1) (hR : 0 < R)
    (hU : AnalyticOnNhd ℂ U (ball 0 R))
    (hlocal : U =ᶠ[𝓝 0] deBruijnNewmanPolymathBoydComplexSaddleLocalInverse)
    (hlands : U (deBruijnNewmanPolymathBoydComplexSaddleImage n) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint n) :
    R ≤ 2 * Real.sqrt Real.pi := by
  by_contra hnot
  have hradius : 2 * Real.sqrt Real.pi < R := lt_of_not_ge hnot
  have hnorm := deBruijnNewmanPolymathBoydComplexSaddleImage_norm_of_adjacent hn
  have himage : deBruijnNewmanPolymathBoydComplexSaddleImage n ∈ ball (0 : ℂ) R := by
    simpa [mem_ball, dist_zero_right, hnorm] using hradius
  have hphaseEq := deBruijnNewmanPolymathBoydOriginInverseBranch_phaseOn_ball hR hU hlocal
  have hphaseEventually :
      (deBruijnNewmanPolymathBoydComplexSaddlePhase ∘ U) =ᶠ[
        𝓝 (deBruijnNewmanPolymathBoydComplexSaddleImage n)] fun z : ℂ => z ^ 2 / 2 :=
    eventually_of_mem (isOpen_ball.mem_nhds himage) hphaseEq
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  have hphaseSaddle : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddlePhase 0
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n) := by
    have hraw := (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n)).differentiableAt.hasDerivAt
    apply hraw.congr_deriv
    rw [deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase]
    change Complex.exp (deBruijnNewmanPolymathBoydComplexSaddlePoint n) - 1 = 0
    rw [deBruijnNewmanPolymathBoydComplexSaddlePoint_exp]
    simp
  have hleft : HasDerivAt
      (deBruijnNewmanPolymathBoydComplexSaddlePhase ∘ U) 0
      (deBruijnNewmanPolymathBoydComplexSaddleImage n) := by
    have houter : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddlePhase 0
        (U (deBruijnNewmanPolymathBoydComplexSaddleImage n)) := by
      rw [hlands]
      exact hphaseSaddle
    exact (houter.comp (deBruijnNewmanPolymathBoydComplexSaddleImage n)
      (hU _ himage).differentiableAt.hasDerivAt).congr_deriv (zero_mul _)
  have hright : HasDerivAt (fun z : ℂ => z ^ 2 / 2)
      (deBruijnNewmanPolymathBoydComplexSaddleImage n)
      (deBruijnNewmanPolymathBoydComplexSaddleImage n) := by
    have hraw :=
      ((hasDerivAt_id (deBruijnNewmanPolymathBoydComplexSaddleImage n)).pow 2).div_const 2
    simpa only [Pi.pow_apply, id_eq] using hraw.congr_deriv (by simp only [id_eq]; ring)
  have hrightAsLeft : HasDerivAt
      (deBruijnNewmanPolymathBoydComplexSaddlePhase ∘ U)
      (deBruijnNewmanPolymathBoydComplexSaddleImage n)
      (deBruijnNewmanPolymathBoydComplexSaddleImage n) :=
    hright.congr_of_eventuallyEq hphaseEventually
  exact deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero hn0
    (hleft.unique hrightAsLeft).symm

end

end LeanLab.Riemann
