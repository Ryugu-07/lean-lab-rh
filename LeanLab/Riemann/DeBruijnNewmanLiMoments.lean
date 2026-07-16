import LeanLab.Riemann.DeBruijnNewmanThreshold
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# Li moments of the de Bruijn-Newman heat family

This file studies the first two Li-type differential expressions of the exact heat family in
the Xi coordinate.  The positive theta kernel turns their values at `s = 1` into weighted
hyperbolic moments on the positive half-line.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The source-normalized de Bruijn-Newman family in the Xi coordinate. -/
def deBruijnNewmanHeatXi (t : ℝ) (s : ℂ) : ℂ :=
  8 * deBruijnNewmanH t (-Complex.I * (2 * s - 1))

/-- The zeroth positive hyperbolic moment at heat time `t`. -/
def deBruijnNewmanHeatLiMomentA (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u

/-- The first odd hyperbolic moment at heat time `t`. -/
def deBruijnNewmanHeatLiMomentB (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u

/-- The second positive hyperbolic moment at heat time `t`. -/
def deBruijnNewmanHeatLiMomentC (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u

/-- The first Li-type logarithmic derivative of the heat family. -/
def deBruijnNewmanHeatLiOne (t : ℝ) : ℂ :=
  logDeriv (deBruijnNewmanHeatXi t) 1

/-- The second Li-type differential expression of the heat family. -/
def deBruijnNewmanHeatLiTwo (t : ℝ) : ℂ :=
  2 * logDeriv (deBruijnNewmanHeatXi t) 1 +
    deriv (logDeriv (deBruijnNewmanHeatXi t)) 1

private theorem deBruijnNewmanH_neg_heatLi (t : ℝ) (z : ℂ) :
    deBruijnNewmanH t (-z) = deBruijnNewmanH t z := by
  rw [deBruijnNewmanH]
  apply integral_congr_ae
  filter_upwards with u
  rw [show (-z) * (u : ℂ) = -(z * (u : ℂ)) by ring, Complex.cos_neg]

theorem deBruijnNewmanHeatXi_one_sub (t : ℝ) (s : ℂ) :
    deBruijnNewmanHeatXi t (1 - s) = deBruijnNewmanHeatXi t s := by
  simp only [deBruijnNewmanHeatXi]
  rw [show -Complex.I * (2 * (1 - s) - 1) =
    -(-Complex.I * (2 * s - 1)) by ring, deBruijnNewmanH_neg_heatLi]

private theorem I_mul_neg_I_mul (z : ℂ) :
    Complex.I * (-Complex.I * z) = z := by
  calc
    Complex.I * (-Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
    _ = z := by rw [Complex.I_mul_I]; ring

theorem deBruijnNewmanHeatXi_zero_eq_riemannXi (s : ℂ) :
    deBruijnNewmanHeatXi 0 s = riemannXi s := by
  rw [deBruijnNewmanHeatXi, deBruijnNewmanH_zero_eq_riemannXi]
  rw [show (1 + Complex.I * (-Complex.I * (2 * s - 1))) / 2 = s by
    rw [I_mul_neg_I_mul]
    ring]
  ring

private theorem cos_neg_I_mul_ofReal (u : ℝ) :
    Complex.cos (-Complex.I * (u : ℂ)) = (Real.cosh u : ℂ) := by
  rw [show -Complex.I * (u : ℂ) = (-(u : ℂ)) * Complex.I by ring,
    Complex.cos_mul_I, Complex.cosh_neg, ← Complex.ofReal_cosh]

private theorem sin_neg_I_mul_ofReal (u : ℝ) :
    Complex.sin (-Complex.I * (u : ℂ)) = -(Real.sinh u : ℂ) * Complex.I := by
  rw [show -Complex.I * (u : ℂ) = (-(u : ℂ)) * Complex.I by ring,
    Complex.sin_mul_I, Complex.sinh_neg, ← Complex.ofReal_sinh]

theorem integrableOn_deBruijnNewmanHeatLiMomentA_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u)
      (Ioi 0) := by
  have hre := (integrableOn_dbnHeatCosIntegrand t (-Complex.I)).re
  apply hre.congr
  filter_upwards with u
  rw [cos_neg_I_mul_ofReal, ← Complex.ofReal_mul]
  exact RCLike.ofReal_re _

theorem integrableOn_deBruijnNewmanHeatLiMomentC_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u)
      (Ioi 0) := by
  have hre := (integrableOn_dbnHeatSecondMomentIntegrand t (-Complex.I)).re
  apply hre.congr
  filter_upwards with u
  rw [cos_neg_I_mul_ofReal, ← Complex.ofReal_mul]
  exact RCLike.ofReal_re _

theorem integrableOn_deBruijnNewmanHeatLiMomentB_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u)
      (Ioi 0) := by
  have hmajor :=
    (integrableOn_deBruijnNewmanHeatLiMomentA_integrand t).add
      (integrableOn_deBruijnNewmanHeatLiMomentC_integrand t)
  apply Integrable.mono' hmajor
  · have hterms : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : ℝ ↦ deBruijnNewmanPhiTerm n u)
        (volume.restrict (Ioi 0)) := fun n ↦ by
      apply Continuous.aestronglyMeasurable
      simp_rw [deBruijnNewmanPhiTerm_eq]
      fun_prop
    have hphi : AEStronglyMeasurable deBruijnNewmanPhi
        (volume.restrict (Ioi 0)) :=
      AEStronglyMeasurable.tsum hterms
    exact (((continuous_id.aestronglyMeasurable.mul
      (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (t * u ^ 2))).aestronglyMeasurable).mul
        hphi).mul (by fun_prop : Continuous Real.sinh).aestronglyMeasurable)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hphi : 0 ≤ deBruijnNewmanPhi u := (deBruijnNewmanPhi_pos hu0).le
    have hsinh : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu0
    have hsinh_cosh : Real.sinh u ≤ Real.cosh u := by
      nlinarith [Real.cosh_sub_sinh u, Real.exp_pos (-u)]
    change
      |u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u| ≤
        Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u +
          u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u
    rw [
      abs_of_nonneg (by positivity :
        0 ≤ u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u)]
    calc
      u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u ≤
          (1 + u ^ 2) * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u *
            Real.cosh u := by
        gcongr
        nlinarith [sq_nonneg u]
      _ = Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u +
          u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u := by
        ring

private theorem integral_pos_restrict_Ioi_of_pos
    (f : ℝ → ℝ) (hf_int : Integrable f (volume.restrict (Ioi 0)))
    (hf_pos : ∀ {u : ℝ}, 0 < u → 0 < f u) :
    0 < ∫ u, f u ∂volume.restrict (Ioi 0) := by
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hf_pos hu).le
  have hsupport : 0 < (volume.restrict (Ioi 0)) (Function.support f) := by
    have hsubset : Ioo (0 : ℝ) 1 ⊆ Function.support f := by
      intro u hu
      exact (hf_pos hu.1).ne'
    have hmeasure : 0 < (volume.restrict (Ioi 0)) (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      simp only [Ioo_inter_Ioi, max_eq_left (by norm_num : (0 : ℝ) ≤ 0),
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
      norm_num
    exact hmeasure.trans_le (measure_mono hsubset)
  exact (integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int).2 hsupport

theorem deBruijnNewmanHeatLiMomentA_pos (t : ℝ) :
    0 < deBruijnNewmanHeatLiMomentA t := by
  rw [deBruijnNewmanHeatLiMomentA]
  apply integral_pos_restrict_Ioi_of_pos _
    (integrableOn_deBruijnNewmanHeatLiMomentA_integrand t)
  intro u hu
  exact mul_pos (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.le)) (Real.cosh_pos _)

theorem deBruijnNewmanHeatLiMomentB_pos (t : ℝ) :
    0 < deBruijnNewmanHeatLiMomentB t := by
  rw [deBruijnNewmanHeatLiMomentB]
  apply integral_pos_restrict_Ioi_of_pos _
    (integrableOn_deBruijnNewmanHeatLiMomentB_integrand t)
  intro u hu
  exact mul_pos (mul_pos (mul_pos hu (Real.exp_pos _)) (deBruijnNewmanPhi_pos hu.le))
    (Real.sinh_pos_iff.mpr hu)

theorem deBruijnNewmanHeatLiMomentC_pos (t : ℝ) :
    0 < deBruijnNewmanHeatLiMomentC t := by
  rw [deBruijnNewmanHeatLiMomentC]
  apply integral_pos_restrict_Ioi_of_pos _
    (integrableOn_deBruijnNewmanHeatLiMomentC_integrand t)
  intro u hu
  exact mul_pos
    (mul_pos (mul_pos (sq_pos_of_pos hu) (Real.exp_pos _)) (deBruijnNewmanPhi_pos hu.le))
    (Real.cosh_pos _)

theorem deBruijnNewmanH_neg_I_eq_heatLiMomentA (t : ℝ) :
    deBruijnNewmanH t (-Complex.I) = (deBruijnNewmanHeatLiMomentA t : ℂ) := by
  rw [deBruijnNewmanH, deBruijnNewmanHeatLiMomentA, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with u
  rw [cos_neg_I_mul_ofReal, ← Complex.ofReal_mul]

theorem deBruijnNewmanHSpatialFirstMoment_neg_I_eq_heatLiMomentB (t : ℝ) :
    deBruijnNewmanHSpatialFirstMoment t (-Complex.I) =
      (deBruijnNewmanHeatLiMomentB t : ℂ) * Complex.I := by
  rw [deBruijnNewmanHSpatialFirstMoment, deBruijnNewmanHeatLiMomentB,
    ← integral_complex_ofReal, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with u
  rw [sin_neg_I_mul_ofReal]
  push_cast
  ring

theorem deBruijnNewmanHSecondMoment_neg_I_eq_heatLiMomentC (t : ℝ) :
    deBruijnNewmanHSecondMoment t (-Complex.I) =
      (deBruijnNewmanHeatLiMomentC t : ℂ) := by
  rw [deBruijnNewmanHSecondMoment, deBruijnNewmanHeatLiMomentC,
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with u
  rw [cos_neg_I_mul_ofReal, ← Complex.ofReal_mul]

theorem hasDerivAt_deBruijnNewmanHeatXi (t : ℝ) (s : ℂ) :
    HasDerivAt (deBruijnNewmanHeatXi t)
      (8 * (deBruijnNewmanHSpatialFirstMoment t
        (-Complex.I * (2 * s - 1)) * (-Complex.I * 2))) s := by
  have hinner : HasDerivAt (fun w : ℂ ↦ -Complex.I * (2 * w - 1))
      (-Complex.I * 2) s := by
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id s).const_mul (2 : ℂ)).sub_const 1).const_mul (-Complex.I))
  have hcomp :=
    (hasDerivAt_deBruijnNewmanH_spatial t (-Complex.I * (2 * s - 1))).comp s hinner
  change HasDerivAt
    (fun w : ℂ ↦ 8 * deBruijnNewmanH t (-Complex.I * (2 * w - 1)))
    (8 * (deBruijnNewmanHSpatialFirstMoment t
      (-Complex.I * (2 * s - 1)) * (-Complex.I * 2))) s
  simpa only [Function.comp_apply] using hcomp.const_mul (8 : ℂ)

theorem deriv_deBruijnNewmanHeatXi (t : ℝ) (s : ℂ) :
    deriv (deBruijnNewmanHeatXi t) s =
      8 * (deBruijnNewmanHSpatialFirstMoment t
        (-Complex.I * (2 * s - 1)) * (-Complex.I * 2)) :=
  (hasDerivAt_deBruijnNewmanHeatXi t s).deriv

theorem hasDerivAt_deriv_deBruijnNewmanHeatXi (t : ℝ) (s : ℂ) :
    HasDerivAt (deriv (deBruijnNewmanHeatXi t))
      (8 * ((-deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1)) *
        (-Complex.I * 2)) * (-Complex.I * 2))) s := by
  have hinner : HasDerivAt (fun w : ℂ ↦ -Complex.I * (2 * w - 1))
      (-Complex.I * 2) s := by
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id s).const_mul (2 : ℂ)).sub_const 1).const_mul (-Complex.I))
  have hcomp :=
    (hasDerivAt_deriv_deBruijnNewmanH t (-Complex.I * (2 * s - 1))).comp s hinner
  have hscaled := (hcomp.mul_const (-Complex.I * 2)).const_mul (8 : ℂ)
  have hfun : deriv (deBruijnNewmanHeatXi t) = fun w : ℂ ↦
      8 * (deriv (deBruijnNewmanH t) (-Complex.I * (2 * w - 1)) *
        (-Complex.I * 2)) := by
    funext w
    rw [deriv_deBruijnNewmanHeatXi, deriv_deBruijnNewmanH]
  rw [hfun]
  exact hscaled

private theorem mul_I_mul_neg_two_I (z : ℂ) :
    (z * Complex.I) * (-Complex.I * 2) = 2 * z := by
  calc
    (z * Complex.I) * (-Complex.I * 2) = -2 * z * (Complex.I * Complex.I) := by ring
    _ = 2 * z := by rw [Complex.I_mul_I]; ring

private theorem neg_mul_neg_two_I_mul_neg_two_I (z : ℂ) :
    ((-z * (-Complex.I * 2)) * (-Complex.I * 2)) = 4 * z := by
  calc
    ((-z * (-Complex.I * 2)) * (-Complex.I * 2)) =
        -4 * z * (Complex.I * Complex.I) := by ring
    _ = 4 * z := by rw [Complex.I_mul_I]; ring

theorem hasDerivAt_deBruijnNewmanHeatXi_time (t : ℝ) (s : ℂ) :
    HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanHeatXi tau s)
      (8 * deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1))) t := by
  have htime :=
    (hasDerivAt_deBruijnNewmanH_time t (-Complex.I * (2 * s - 1))).const_mul (8 : ℂ)
  change HasDerivAt
    (fun tau : ℝ ↦ 8 * deBruijnNewmanH tau (-Complex.I * (2 * s - 1)))
    (8 * deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1))) t
  exact htime

theorem deBruijnNewmanHeatXi_heat_equation (t : ℝ) (s : ℂ) :
    deriv (fun tau : ℝ ↦ deBruijnNewmanHeatXi tau s) t =
      (1 / 4 : ℂ) * deriv (deriv (deBruijnNewmanHeatXi t)) s := by
  rw [(hasDerivAt_deBruijnNewmanHeatXi_time t s).deriv,
    (hasDerivAt_deriv_deBruijnNewmanHeatXi t s).deriv,
    neg_mul_neg_two_I_mul_neg_two_I]
  ring

theorem deriv_deBruijnNewmanHeatXi_one_eq (t : ℝ) :
    deriv (deBruijnNewmanHeatXi t) 1 =
      16 * (deBruijnNewmanHeatLiMomentB t : ℂ) := by
  rw [deriv_deBruijnNewmanHeatXi]
  rw [show -Complex.I * (2 * (1 : ℂ) - 1) = -Complex.I by ring,
    deBruijnNewmanHSpatialFirstMoment_neg_I_eq_heatLiMomentB,
    mul_I_mul_neg_two_I]
  ring

theorem deriv_deriv_deBruijnNewmanHeatXi_one_eq (t : ℝ) :
    deriv (deriv (deBruijnNewmanHeatXi t)) 1 =
      32 * (deBruijnNewmanHeatLiMomentC t : ℂ) := by
  rw [(hasDerivAt_deriv_deBruijnNewmanHeatXi t 1).deriv]
  rw [show -Complex.I * (2 * (1 : ℂ) - 1) = -Complex.I by ring,
    deBruijnNewmanHSecondMoment_neg_I_eq_heatLiMomentC,
    neg_mul_neg_two_I_mul_neg_two_I]
  ring

theorem hasDerivAt_deBruijnNewmanHeatXi_one (t : ℝ) :
    HasDerivAt (deBruijnNewmanHeatXi t)
      (16 * (deBruijnNewmanHeatLiMomentB t : ℂ)) 1 := by
  apply (hasDerivAt_deBruijnNewmanHeatXi t 1).congr_deriv
  calc
    8 * (deBruijnNewmanHSpatialFirstMoment t
          (-Complex.I * (2 * (1 : ℂ) - 1)) * (-Complex.I * 2)) =
        deriv (deBruijnNewmanHeatXi t) 1 :=
      (hasDerivAt_deBruijnNewmanHeatXi t 1).deriv.symm
    _ = 16 * (deBruijnNewmanHeatLiMomentB t : ℂ) :=
      deriv_deBruijnNewmanHeatXi_one_eq t

theorem hasDerivAt_deriv_deBruijnNewmanHeatXi_one (t : ℝ) :
    HasDerivAt (deriv (deBruijnNewmanHeatXi t))
      (32 * (deBruijnNewmanHeatLiMomentC t : ℂ)) 1 := by
  apply (hasDerivAt_deriv_deBruijnNewmanHeatXi t 1).congr_deriv
  calc
    8 * ((-deBruijnNewmanHSecondMoment t
          (-Complex.I * (2 * (1 : ℂ) - 1)) * (-Complex.I * 2)) *
          (-Complex.I * 2)) =
        deriv (deriv (deBruijnNewmanHeatXi t)) 1 :=
      (hasDerivAt_deriv_deBruijnNewmanHeatXi t 1).deriv.symm
    _ = 32 * (deBruijnNewmanHeatLiMomentC t : ℂ) :=
      deriv_deriv_deBruijnNewmanHeatXi_one_eq t

theorem deBruijnNewmanHeatXi_one_eq (t : ℝ) :
    deBruijnNewmanHeatXi t 1 = 8 * (deBruijnNewmanHeatLiMomentA t : ℂ) := by
  rw [deBruijnNewmanHeatXi]
  rw [show -Complex.I * (2 * (1 : ℂ) - 1) = -Complex.I by ring,
    deBruijnNewmanH_neg_I_eq_heatLiMomentA]

theorem deBruijnNewmanHeatXi_one_ne_zero (t : ℝ) :
    deBruijnNewmanHeatXi t 1 ≠ 0 := by
  rw [deBruijnNewmanHeatXi_one_eq]
  exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr (deBruijnNewmanHeatLiMomentA_pos t).ne')

theorem deBruijnNewmanHeatLiOne_eq (t : ℝ) :
    deBruijnNewmanHeatLiOne t =
      ((2 * deBruijnNewmanHeatLiMomentB t / deBruijnNewmanHeatLiMomentA t : ℝ) : ℂ) := by
  rw [deBruijnNewmanHeatLiOne, logDeriv_apply,
    deriv_deBruijnNewmanHeatXi_one_eq, deBruijnNewmanHeatXi_one_eq]
  have hA : (deBruijnNewmanHeatLiMomentA t : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (deBruijnNewmanHeatLiMomentA_pos t).ne'
  push_cast
  field_simp
  ring

theorem deriv_logDeriv_deBruijnNewmanHeatXi_one_eq (t : ℝ) :
    deriv (logDeriv (deBruijnNewmanHeatXi t)) 1 =
      ((32 * (deBruijnNewmanHeatLiMomentC t : ℂ) *
          (8 * (deBruijnNewmanHeatLiMomentA t : ℂ)) -
        (16 * (deBruijnNewmanHeatLiMomentB t : ℂ)) *
          (16 * (deBruijnNewmanHeatLiMomentB t : ℂ))) /
        (8 * (deBruijnNewmanHeatLiMomentA t : ℂ)) ^ 2) := by
  have hquot := (hasDerivAt_deriv_deBruijnNewmanHeatXi_one t).div
    (hasDerivAt_deBruijnNewmanHeatXi_one t)
    (deBruijnNewmanHeatXi_one_ne_zero t)
  have hfun : logDeriv (deBruijnNewmanHeatXi t) = fun s : ℂ ↦
      deriv (deBruijnNewmanHeatXi t) s / deBruijnNewmanHeatXi t s := by
    funext s
    rw [logDeriv_apply]
  rw [hfun]
  change deriv (deriv (deBruijnNewmanHeatXi t) / deBruijnNewmanHeatXi t) 1 = _
  rw [hquot.deriv, deBruijnNewmanHeatXi_one_eq,
    deriv_deBruijnNewmanHeatXi_one_eq]

theorem deBruijnNewmanHeatLiTwo_eq (t : ℝ) :
    deBruijnNewmanHeatLiTwo t =
      ((4 * (deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentB t +
        deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t -
        deBruijnNewmanHeatLiMomentB t ^ 2) /
        deBruijnNewmanHeatLiMomentA t ^ 2 : ℝ) : ℂ) := by
  change 2 * deBruijnNewmanHeatLiOne t +
    deriv (logDeriv (deBruijnNewmanHeatXi t)) 1 = _
  rw [deBruijnNewmanHeatLiOne_eq,
    deriv_logDeriv_deBruijnNewmanHeatXi_one_eq]
  have hA : (deBruijnNewmanHeatLiMomentA t : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (deBruijnNewmanHeatLiMomentA_pos t).ne'
  push_cast
  field_simp
  ring

private def deBruijnNewmanHeatLiWeight (t u : ℝ) : ℝ :=
  Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u

private def deBruijnNewmanHeatLiCoordinate (u : ℝ) : ℝ :=
  u * Real.tanh u

private def deBruijnNewmanHeatLiTanhSecondMoment (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    deBruijnNewmanHeatLiWeight t u * deBruijnNewmanHeatLiCoordinate u ^ 2

private theorem cosh_mul_tanh_eq_sinh (u : ℝ) :
    Real.cosh u * Real.tanh u = Real.sinh u := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos u).ne']

private theorem heatLiWeight_mul_coordinate_eq (t u : ℝ) :
    deBruijnNewmanHeatLiWeight t u * deBruijnNewmanHeatLiCoordinate u =
      u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u := by
  rw [deBruijnNewmanHeatLiWeight, deBruijnNewmanHeatLiCoordinate]
  calc
    (Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u) *
        (u * Real.tanh u) =
      u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u *
        (Real.cosh u * Real.tanh u) := by ring
    _ = _ := by rw [cosh_mul_tanh_eq_sinh]

private theorem heatLiCoordinate_sq_le_sq (u : ℝ) :
    deBruijnNewmanHeatLiCoordinate u ^ 2 ≤ u ^ 2 := by
  rw [deBruijnNewmanHeatLiCoordinate, mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg u) (Real.tanh_sq_lt_one u).le

private theorem integrableOn_deBruijnNewmanHeatLiTanhSecondMoment_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ deBruijnNewmanHeatLiWeight t u *
        deBruijnNewmanHeatLiCoordinate u ^ 2) (Ioi 0) := by
  have hmajor := integrableOn_deBruijnNewmanHeatLiMomentC_integrand t
  apply Integrable.mono' hmajor
  · have hcoord : Continuous (fun u : ℝ ↦ deBruijnNewmanHeatLiCoordinate u ^ 2) := by
      have htanh : Continuous Real.tanh := by
        have hdiv : Continuous (fun u : ℝ ↦ Real.sinh u / Real.cosh u) := by
          apply (Real.continuous_sinh.div Real.continuous_cosh
            (fun u ↦ (Real.cosh_pos u).ne')).congr
          intro u
          rfl
        exact hdiv.congr fun u ↦ (Real.tanh_eq_sinh_div_cosh u).symm
      simpa only [deBruijnNewmanHeatLiCoordinate, id_eq, Pi.mul_apply] using
        (continuous_id.mul htanh).pow 2
    exact (integrableOn_deBruijnNewmanHeatLiMomentA_integrand t).aestronglyMeasurable.mul
      hcoord.aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hweight : 0 ≤ deBruijnNewmanHeatLiWeight t u := by
      rw [deBruijnNewmanHeatLiWeight]
      exact mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (deBruijnNewmanPhi_pos hu.le).le)
        (Real.cosh_pos _).le
    rw [Real.norm_eq_abs]
    rw [show u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u =
      u ^ 2 * deBruijnNewmanHeatLiWeight t u by
        rw [deBruijnNewmanHeatLiWeight]
        ring]
    change
      |deBruijnNewmanHeatLiWeight t u * deBruijnNewmanHeatLiCoordinate u ^ 2| ≤
        u ^ 2 * deBruijnNewmanHeatLiWeight t u
    rw [abs_of_nonneg (mul_nonneg hweight (sq_nonneg _))]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (heatLiCoordinate_sq_le_sq u) hweight

private theorem deBruijnNewmanHeatLiTanhSecondMoment_le_C (t : ℝ) :
    deBruijnNewmanHeatLiTanhSecondMoment t ≤ deBruijnNewmanHeatLiMomentC t := by
  rw [deBruijnNewmanHeatLiTanhSecondMoment, deBruijnNewmanHeatLiMomentC]
  apply integral_mono_ae
    (integrableOn_deBruijnNewmanHeatLiTanhSecondMoment_integrand t)
    (integrableOn_deBruijnNewmanHeatLiMomentC_integrand t)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hweight : 0 ≤ deBruijnNewmanHeatLiWeight t u := by
    rw [deBruijnNewmanHeatLiWeight]
    exact mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (deBruijnNewmanPhi_pos hu.le).le)
      (Real.cosh_pos _).le
  rw [show u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u =
    u ^ 2 * deBruijnNewmanHeatLiWeight t u by
      rw [deBruijnNewmanHeatLiWeight]
      ring]
  change deBruijnNewmanHeatLiWeight t u * deBruijnNewmanHeatLiCoordinate u ^ 2 ≤
    u ^ 2 * deBruijnNewmanHeatLiWeight t u
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (heatLiCoordinate_sq_le_sq u) hweight

theorem deBruijnNewmanHeatLiMomentB_sq_le_mul (t : ℝ) :
    deBruijnNewmanHeatLiMomentB t ^ 2 ≤
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t := by
  let A := deBruijnNewmanHeatLiMomentA t
  let B := deBruijnNewmanHeatLiMomentB t
  let D := deBruijnNewmanHeatLiTanhSecondMoment t
  let W : ℝ → ℝ := deBruijnNewmanHeatLiWeight t
  let X : ℝ → ℝ := deBruijnNewmanHeatLiCoordinate
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hA_pos : 0 < A := deBruijnNewmanHeatLiMomentA_pos t
  have hW_int : Integrable W μ :=
    integrableOn_deBruijnNewmanHeatLiMomentA_integrand t
  have hWX_int : Integrable (fun u ↦ W u * X u) μ := by
    apply (integrableOn_deBruijnNewmanHeatLiMomentB_integrand t).congr
    filter_upwards with u
    exact (heatLiWeight_mul_coordinate_eq t u).symm
  have hD_int : Integrable (fun u ↦ W u * X u ^ 2) μ :=
    integrableOn_deBruijnNewmanHeatLiTanhSecondMoment_integrand t
  have hW_integral : (∫ u, W u ∂μ) = A := by
    rfl
  have hWX_integral : (∫ u, W u * X u ∂μ) = B := by
    dsimp only [B]
    rw [deBruijnNewmanHeatLiMomentB]
    apply integral_congr_ae
    filter_upwards with u
    exact heatLiWeight_mul_coordinate_eq t u
  have hD_integral : (∫ u, W u * X u ^ 2 ∂μ) = D := by
    rfl
  have hsquare_nonneg : 0 ≤ ∫ u, W u * (A * X u - B) ^ 2 ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hweight : 0 ≤ W u := by
      dsimp only [W]
      rw [deBruijnNewmanHeatLiWeight]
      exact mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (deBruijnNewmanPhi_pos hu.le).le)
        (Real.cosh_pos _).le
    exact mul_nonneg hweight (sq_nonneg _)
  have hD_term : Integrable (fun u ↦ A ^ 2 * (W u * X u ^ 2)) μ :=
    hD_int.const_mul _
  have hB_term : Integrable (fun u ↦ (2 * A * B) * (W u * X u)) μ :=
    hWX_int.const_mul _
  have hA_term : Integrable (fun u ↦ B ^ 2 * W u) μ :=
    hW_int.const_mul _
  have hexpand :
      (∫ u, W u * (A * X u - B) ^ 2 ∂μ) =
        A ^ 2 * D - (2 * A * B) * B + B ^ 2 * A := by
    calc
      (∫ u, W u * (A * X u - B) ^ 2 ∂μ) =
          ∫ u, A ^ 2 * (W u * X u ^ 2) -
            (2 * A * B) * (W u * X u) + B ^ 2 * W u ∂μ := by
        apply integral_congr_ae
        filter_upwards with u
        ring
      _ = (∫ u, A ^ 2 * (W u * X u ^ 2) -
            (2 * A * B) * (W u * X u) ∂μ) +
          ∫ u, B ^ 2 * W u ∂μ := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_add (hD_term.sub hB_term) hA_term
      _ = ((∫ u, A ^ 2 * (W u * X u ^ 2) ∂μ) -
            ∫ u, (2 * A * B) * (W u * X u) ∂μ) +
          ∫ u, B ^ 2 * W u ∂μ := by
        exact congrArg (fun z : ℝ ↦ z + ∫ u, B ^ 2 * W u ∂μ)
          (by simpa only [Pi.sub_apply] using integral_sub hD_term hB_term)
      _ = A ^ 2 * D - (2 * A * B) * B + B ^ 2 * A := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul,
          hD_integral, hWX_integral, hW_integral]
  have hBD : B ^ 2 ≤ A * D := by
    rw [hexpand] at hsquare_nonneg
    nlinarith
  have hDC : D ≤ deBruijnNewmanHeatLiMomentC t :=
    deBruijnNewmanHeatLiTanhSecondMoment_le_C t
  exact hBD.trans (mul_le_mul_of_nonneg_left hDC hA_pos.le)

theorem deBruijnNewmanHeatLiOne_re_pos (t : ℝ) :
    0 < (deBruijnNewmanHeatLiOne t).re := by
  rw [deBruijnNewmanHeatLiOne_eq]
  simp only [ofReal_re]
  exact div_pos
    (mul_pos (by norm_num) (deBruijnNewmanHeatLiMomentB_pos t))
    (deBruijnNewmanHeatLiMomentA_pos t)

theorem deBruijnNewmanHeatLiOne_im_eq_zero (t : ℝ) :
    (deBruijnNewmanHeatLiOne t).im = 0 := by
  rw [deBruijnNewmanHeatLiOne_eq]
  exact ofReal_im _

theorem deBruijnNewmanHeatLiTwo_re_pos (t : ℝ) :
    0 < (deBruijnNewmanHeatLiTwo t).re := by
  rw [deBruijnNewmanHeatLiTwo_eq]
  simp only [ofReal_re]
  have hAB : 0 < deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentB t :=
    mul_pos (deBruijnNewmanHeatLiMomentA_pos t)
      (deBruijnNewmanHeatLiMomentB_pos t)
  have hCS := deBruijnNewmanHeatLiMomentB_sq_le_mul t
  have hnum : 0 <
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentB t +
        deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t -
        deBruijnNewmanHeatLiMomentB t ^ 2 := by
    nlinarith
  exact div_pos (mul_pos (by norm_num) hnum)
    (sq_pos_of_pos (deBruijnNewmanHeatLiMomentA_pos t))

theorem deBruijnNewmanHeatLiTwo_im_eq_zero (t : ℝ) :
    (deBruijnNewmanHeatLiTwo t).im = 0 := by
  rw [deBruijnNewmanHeatLiTwo_eq]
  exact ofReal_im _

/-- The fixed first-two Li endpoint for the exact source-normalized heat family. -/
theorem deBruijnNewmanHeat_firstTwoLi_endpoint (t : ℝ) :
    deBruijnNewmanHeatXi t 1 ≠ 0 ∧
    deBruijnNewmanHeatLiOne t =
      ((2 * deBruijnNewmanHeatLiMomentB t / deBruijnNewmanHeatLiMomentA t : ℝ) : ℂ) ∧
    0 < (deBruijnNewmanHeatLiOne t).re ∧
    (deBruijnNewmanHeatLiOne t).im = 0 ∧
    deBruijnNewmanHeatLiMomentB t ^ 2 ≤
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t ∧
    deBruijnNewmanHeatLiTwo t =
      ((4 * (deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentB t +
        deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentC t -
        deBruijnNewmanHeatLiMomentB t ^ 2) /
        deBruijnNewmanHeatLiMomentA t ^ 2 : ℝ) : ℂ) ∧
    0 < (deBruijnNewmanHeatLiTwo t).re ∧
    (deBruijnNewmanHeatLiTwo t).im = 0 := by
  exact ⟨deBruijnNewmanHeatXi_one_ne_zero t,
    deBruijnNewmanHeatLiOne_eq t,
    deBruijnNewmanHeatLiOne_re_pos t,
    deBruijnNewmanHeatLiOne_im_eq_zero t,
    deBruijnNewmanHeatLiMomentB_sq_le_mul t,
    deBruijnNewmanHeatLiTwo_eq t,
    deBruijnNewmanHeatLiTwo_re_pos t,
    deBruijnNewmanHeatLiTwo_im_eq_zero t⟩

end

end LeanLab.Riemann
