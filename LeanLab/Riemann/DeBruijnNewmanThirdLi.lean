import LeanLab.Riemann.DeBruijnNewmanLiMoments
import LeanLab.Riemann.LiScaffold
import LeanLab.Riemann.LiZeroFormula

set_option linter.style.header false

/-!
# The third Li coefficient from ordered theta moments

This module extends the exact de Bruijn-Newman theta moments by one order.  A weighted
Chebyshev covariance and the existing time-zero first-Li bound give unconditional positivity of
the standard third Li coefficient.  No all-index conclusion is made.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The third odd hyperbolic moment of the source heat family. -/
def deBruijnNewmanHeatLiMomentD (t : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi 0,
    u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u

/-- The standard third Li differential expression of the source heat family. -/
def deBruijnNewmanHeatLiThree (t : ℝ) : ℂ :=
  3 * logDeriv (deBruijnNewmanHeatXi t) 1 +
    3 * deriv (logDeriv (deBruijnNewmanHeatXi t)) 1 +
    (1 / 2) * iteratedDeriv 2 (logDeriv (deBruijnNewmanHeatXi t)) 1

private def deBruijnNewmanThirdLiWeight (t u : ℝ) : ℝ :=
  Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u

private def deBruijnNewmanThirdLiX (u : ℝ) : ℝ :=
  u * Real.tanh u

private def deBruijnNewmanThirdLiY (u : ℝ) : ℝ :=
  u ^ 2

private theorem thirdLi_cosh_mul_tanh (u : ℝ) :
    Real.cosh u * Real.tanh u = Real.sinh u := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos u).ne']

private theorem thirdLiWeight_mul_X (t u : ℝ) :
    deBruijnNewmanThirdLiWeight t u * deBruijnNewmanThirdLiX u =
      u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u := by
  rw [deBruijnNewmanThirdLiWeight, deBruijnNewmanThirdLiX]
  calc
    (Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u) *
        (u * Real.tanh u) =
      u * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u *
        (Real.cosh u * Real.tanh u) := by ring
    _ = _ := by rw [thirdLi_cosh_mul_tanh]

private theorem thirdLiWeight_mul_Y (t u : ℝ) :
    deBruijnNewmanThirdLiWeight t u * deBruijnNewmanThirdLiY u =
      u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh u := by
  rw [deBruijnNewmanThirdLiWeight, deBruijnNewmanThirdLiY]
  ring

private theorem thirdLiWeight_mul_X_mul_Y (t u : ℝ) :
    deBruijnNewmanThirdLiWeight t u * deBruijnNewmanThirdLiX u *
        deBruijnNewmanThirdLiY u =
      u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u := by
  rw [thirdLiWeight_mul_X, deBruijnNewmanThirdLiY]
  ring

private theorem thirdLi_tanh_mono {u v : ℝ} (_hu : 0 ≤ u) (huv : u ≤ v) :
    Real.tanh u ≤ Real.tanh v := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos u) (Real.cosh_pos v)]
  have h := Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr huv)
  rw [Real.sinh_sub] at h
  linarith

private theorem thirdLiX_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    deBruijnNewmanThirdLiX u ≤ deBruijnNewmanThirdLiX v := by
  have hv : 0 ≤ v := hu.trans huv
  have htu : 0 ≤ Real.tanh u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    positivity
  have ht := thirdLi_tanh_mono hu huv
  rw [deBruijnNewmanThirdLiX]
  calc
    u * Real.tanh u ≤ v * Real.tanh u := mul_le_mul_of_nonneg_right huv htu
    _ ≤ v * Real.tanh v := mul_le_mul_of_nonneg_left ht hv

theorem integrableOn_deBruijnNewmanHeatLiMomentD_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦
        u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u)
      (Ioi 0) := by
  let major : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp ((|t| + 1) * u ^ 2 + u) *
      ‖deBruijnNewmanPhi u‖
  have hmajor : IntegrableOn major (Ioi 0) := by
    simpa only [one_mul] using
      integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
        (|t| + 1) (by positivity) 1
  apply Integrable.mono' hmajor
  · have hbase : AEStronglyMeasurable
        (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2))
        (volume.restrict (Ioi 0)) :=
      ((continuous_id.pow 3).mul
        (by fun_prop : Continuous (fun u : ℝ ↦
          Real.exp (t * u ^ 2)))).aestronglyMeasurable
    have hphi := aestronglyMeasurable_deBruijnNewmanPhi
      (volume.restrict (Ioi 0))
    exact ((hbase.mul hphi).mul Real.continuous_sinh.aestronglyMeasurable)
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hsinh0 : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu0
    have hsinh_exp : Real.sinh u ≤ Real.exp u := by
      have hc := Real.cosh_pos u
      rw [← Real.exp_sub_sinh] at hc
      linarith
    have hu_le_exp_sq : u ≤ Real.exp (u ^ 2) := by
      calc
        u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1 / 2)]
        _ ≤ Real.exp (u ^ 2) := by
          simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)
    rw [Real.norm_eq_abs]
    have hintegrand_nonneg :
        0 ≤ u ^ 3 * Real.exp (t * u ^ 2) *
          deBruijnNewmanPhi u * Real.sinh u :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (pow_nonneg hu0 3) (Real.exp_pos _).le)
            (deBruijnNewmanPhi_pos hu0).le)
        hsinh0
    rw [abs_of_nonneg hintegrand_nonneg]
    change
      u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u ≤
        major u
    dsimp only [major]
    have hexp_le : Real.exp (t * u ^ 2) ≤ Real.exp (|t| * u ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self t) (sq_nonneg u))
    have hrest : 0 ≤ u ^ 3 * deBruijnNewmanPhi u * Real.sinh u := by
      exact mul_nonneg
        (mul_nonneg (pow_nonneg hu0 3) (deBruijnNewmanPhi_pos hu0).le) hsinh0
    calc
      u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u ≤
          u ^ 3 * Real.exp (|t| * u ^ 2) * deBruijnNewmanPhi u *
            Real.sinh u := by
        calc
          u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.sinh u =
              Real.exp (t * u ^ 2) *
                (u ^ 3 * deBruijnNewmanPhi u * Real.sinh u) := by ring
          _ ≤ Real.exp (|t| * u ^ 2) *
                (u ^ 3 * deBruijnNewmanPhi u * Real.sinh u) :=
            mul_le_mul_of_nonneg_right hexp_le hrest
          _ = _ := by ring
      _ ≤
          u ^ 3 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
            Real.exp u := by
        rw [show ‖deBruijnNewmanPhi u‖ = deBruijnNewmanPhi u by
          rw [Real.norm_eq_abs, abs_of_pos (deBruijnNewmanPhi_pos hu0)]]
        have hprefix : 0 ≤ u ^ 3 * Real.exp (|t| * u ^ 2) *
            deBruijnNewmanPhi u := by
          exact mul_nonneg
            (mul_nonneg (pow_nonneg hu0 3) (Real.exp_pos _).le)
            (deBruijnNewmanPhi_pos hu0).le
        exact mul_le_mul_of_nonneg_left hsinh_exp hprefix
      _ ≤ (1 + u ^ 2) * Real.exp (u ^ 2) *
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ * Real.exp u := by
        gcongr
        calc
          u ^ 3 = u ^ 2 * u := by ring
          _ ≤ u ^ 2 * Real.exp (u ^ 2) := by gcongr
          _ ≤ (1 + u ^ 2) * Real.exp (u ^ 2) := by
            exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = (1 + u ^ 2) * Real.exp ((|t| + 1) * u ^ 2 + u) *
          ‖deBruijnNewmanPhi u‖ := by
        rw [show (|t| + 1) * u ^ 2 + u = u ^ 2 + |t| * u ^ 2 + u by ring,
          Real.exp_add, Real.exp_add]
        ring

theorem deBruijnNewmanHeatLiMomentD_pos (t : ℝ) :
    0 < deBruijnNewmanHeatLiMomentD t := by
  rw [deBruijnNewmanHeatLiMomentD]
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2) *
        deBruijnNewmanPhi u * Real.sinh u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos
      (mul_pos
        (mul_pos (pow_pos hu 3) (Real.exp_pos _))
          (deBruijnNewmanPhi_pos hu.le))
      (Real.sinh_pos_iff.mpr hu)).le
  have hsupport : 0 < (volume.restrict (Ioi 0)) (Function.support
      (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2) *
        deBruijnNewmanPhi u * Real.sinh u)) := by
    have hsubset : Ioo (0 : ℝ) 1 ⊆ Function.support
        (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2) *
          deBruijnNewmanPhi u * Real.sinh u) := by
      intro u hu
      exact (mul_pos
        (mul_pos
          (mul_pos (pow_pos hu.1 3) (Real.exp_pos _))
            (deBruijnNewmanPhi_pos hu.1.le))
        (Real.sinh_pos_iff.mpr hu.1)).ne'
    have hmeasure : 0 < (volume.restrict (Ioi 0)) (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      simp only [Ioo_inter_Ioi, max_eq_left (by norm_num : (0 : ℝ) ≤ 0),
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
      norm_num
    exact hmeasure.trans_le (measure_mono hsubset)
  exact (integral_pos_iff_support_of_nonneg_ae hnonneg
    (integrableOn_deBruijnNewmanHeatLiMomentD_integrand t)).2 hsupport

private def deBruijnNewmanHThirdMoment (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0,
    (((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.sin (z * (u : ℂ)))

private theorem aestronglyMeasurable_dbnThirdMomentIntegrand (t : ℝ) (z : ℂ) :
    AEStronglyMeasurable
      (fun u : ℝ ↦
        (((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.sin (z * (u : ℂ)))) (volume.restrict (Ioi 0)) := by
  have hbase : AEStronglyMeasurable
      (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2))
      (volume.restrict (Ioi 0)) :=
    ((continuous_id.pow 3).mul
      (by fun_prop : Continuous (fun u : ℝ ↦
        Real.exp (t * u ^ 2)))).aestronglyMeasurable
  have hphi := aestronglyMeasurable_deBruijnNewmanPhi
    (volume.restrict (Ioi 0))
  have hsin : AEStronglyMeasurable
      (fun u : ℝ ↦ Complex.sin (z * (u : ℂ)))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦
      Complex.sin (z * (u : ℂ)))).aestronglyMeasurable
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (hbase.mul hphi)).mul hsin

private theorem integrableOn_dbnThirdMomentIntegrand (t : ℝ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        (((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.sin (z * (u : ℂ)))) (Ioi 0) := by
  let major : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp ((|t| + 1) * u ^ 2 + ‖z‖ * u) *
      ‖deBruijnNewmanPhi u‖
  have hmajor : IntegrableOn major (Ioi 0) :=
    integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|t| + 1) (by positivity) ‖z‖
  apply Integrable.mono' hmajor
  · exact aestronglyMeasurable_dbnThirdMomentIntegrand t z
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hu_le_exp_sq : u ≤ Real.exp (u ^ 2) := by
      calc
        u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1 / 2)]
        _ ≤ Real.exp (u ^ 2) := by
          simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)
    dsimp only [major]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg hu0 3), abs_of_pos (Real.exp_pos _),
      ← Real.norm_eq_abs]
    calc
      u ^ 3 * Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.sin (z * (u : ℂ))‖ ≤
        u ^ 3 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖z‖ * u) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_sin_mul_real_le z hu0
      _ ≤ (1 + u ^ 2) * Real.exp (u ^ 2) *
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
            Real.exp (‖z‖ * u) := by
        gcongr
        calc
          u ^ 3 = u ^ 2 * u := by ring
          _ ≤ u ^ 2 * Real.exp (u ^ 2) := by gcongr
          _ ≤ (1 + u ^ 2) * Real.exp (u ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = (1 + u ^ 2) * Real.exp ((|t| + 1) * u ^ 2 + ‖z‖ * u) *
          ‖deBruijnNewmanPhi u‖ := by
        rw [show (|t| + 1) * u ^ 2 + ‖z‖ * u =
            u ^ 2 + |t| * u ^ 2 + ‖z‖ * u by ring,
          Real.exp_add, Real.exp_add]
        ring

private theorem hasDerivAt_dbnSecondMomentIntegrand
    (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ ↦
        (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (w * (u : ℂ))))
      (-(((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.sin (z * (u : ℂ)))) z := by
  have hcos := (Complex.hasDerivAt_cos (z * (u : ℂ))).comp z
    ((hasDerivAt_id z).mul_const (u : ℂ))
  have h := hcos.const_mul
    ((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ)
  convert! h using 1
  push_cast
  ring

private theorem hasDerivAt_deBruijnNewmanHSecondMoment
    (t : ℝ) (z : ℂ) :
    HasDerivAt (deBruijnNewmanHSecondMoment t)
      (-deBruijnNewmanHThirdMoment t z) z := by
  let F : ℂ → ℝ → ℂ := fun w u ↦
    (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (w * (u : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun w u ↦
    -(((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.sin (w * (u : ℂ)))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp ((|t| + 1) * u ^ 2 + (‖z‖ + 1) * u) *
      ‖deBruijnNewmanPhi u‖
  have hs : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z one_pos
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards with w
    have hbase : AEStronglyMeasurable
        (fun u : ℝ ↦ u ^ 2 * Real.exp (t * u ^ 2))
        (volume.restrict (Ioi 0)) :=
      ((continuous_id.pow 2).mul
        (by fun_prop : Continuous (fun u : ℝ ↦
          Real.exp (t * u ^ 2)))).aestronglyMeasurable
    have hphi := aestronglyMeasurable_deBruijnNewmanPhi
      (volume.restrict (Ioi 0))
    have hcos : AEStronglyMeasurable
        (fun u : ℝ ↦ Complex.cos (w * (u : ℂ)))
        (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous (fun u : ℝ ↦
        Complex.cos (w * (u : ℂ)))).aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (hbase.mul hphi)).mul hcos
  have hF_int : Integrable (F z) (volume.restrict (Ioi 0)) := by
    exact integrableOn_dbnHeatSecondMomentIntegrand t z
  have hF'_meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    exact (aestronglyMeasurable_dbnThirdMomentIntegrand t z).neg
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z 1, ‖F' w u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
    have hu0 : 0 ≤ u := hu.le
    have hw' : ‖w - z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hwNorm : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        ‖w‖ = ‖z + (w - z)‖ := by congr 1; ring
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + 1 := by gcongr
    have hu_le_exp_sq : u ≤ Real.exp (u ^ 2) := by
      calc
        u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1 / 2)]
        _ ≤ Real.exp (u ^ 2) := by
          simpa only [add_comm] using Real.add_one_le_exp (u ^ 2)
    dsimp only [F', bound]
    rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (pow_nonneg hu0 3), abs_of_pos (Real.exp_pos _),
      ← Real.norm_eq_abs]
    calc
      u ^ 3 * Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.sin (w * (u : ℂ))‖ ≤
        u ^ 3 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖w‖ * u) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_sin_mul_real_le w hu0
      _ ≤ u ^ 3 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp ((‖z‖ + 1) * u) := by gcongr
      _ ≤ (1 + u ^ 2) * Real.exp (u ^ 2) *
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
            Real.exp ((‖z‖ + 1) * u) := by
        gcongr
        calc
          u ^ 3 = u ^ 2 * u := by ring
          _ ≤ u ^ 2 * Real.exp (u ^ 2) := by gcongr
          _ ≤ (1 + u ^ 2) * Real.exp (u ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = bound u := by
        dsimp only [bound]
        rw [show (|t| + 1) * u ^ 2 + (‖z‖ + 1) * u =
            u ^ 2 + |t| * u ^ 2 + (‖z‖ + 1) * u by ring,
          Real.exp_add, Real.exp_add]
        ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|t| + 1) (by positivity) (‖z‖ + 1)
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z 1, HasDerivAt (F · u) (F' w u) w := by
    filter_upwards with u w _
    exact hasDerivAt_dbnSecondMomentIntegrand t w u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa only [F, F', deBruijnNewmanHSecondMoment,
    deBruijnNewmanHThirdMoment, integral_neg] using! hmain.2

private theorem sin_neg_I_mul_ofReal_thirdLi (u : ℝ) :
    Complex.sin (-Complex.I * (u : ℂ)) = -(Real.sinh u : ℂ) * Complex.I := by
  rw [show -Complex.I * (u : ℂ) = (-(u : ℂ)) * Complex.I by ring,
    Complex.sin_mul_I, Complex.sinh_neg, ← Complex.ofReal_sinh]

private theorem deBruijnNewmanHThirdMoment_neg_I_eq (t : ℝ) :
    deBruijnNewmanHThirdMoment t (-Complex.I) =
      -(deBruijnNewmanHeatLiMomentD t : ℂ) * Complex.I := by
  rw [deBruijnNewmanHThirdMoment, deBruijnNewmanHeatLiMomentD,
    ← integral_complex_ofReal]
  calc
    (∫ u : ℝ in Ioi 0,
        (((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.sin (-Complex.I * (u : ℂ)))) =
        ∫ u : ℝ in Ioi 0,
          -((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u *
            Real.sinh u : ℝ) : ℂ) * Complex.I := by
      apply integral_congr_ae
      filter_upwards with u
      rw [sin_neg_I_mul_ofReal_thirdLi]
      push_cast
      ring
    _ = -(∫ u : ℝ in Ioi 0,
          ((u ^ 3 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u *
            Real.sinh u : ℝ) : ℂ)) * Complex.I := by
      rw [integral_mul_const, integral_neg]

private theorem deriv_deriv_deBruijnNewmanHeatXi_eq (t : ℝ) (s : ℂ) :
    deriv (deriv (deBruijnNewmanHeatXi t)) s =
      32 * deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1)) := by
  rw [(hasDerivAt_deriv_deBruijnNewmanHeatXi t s).deriv]
  have hsq : (-Complex.I * 2) * (-Complex.I * 2) = (-4 : ℂ) := by
    calc
      (-Complex.I * 2) * (-Complex.I * 2) = 4 * (Complex.I * Complex.I) := by ring
      _ = -4 := by rw [Complex.I_mul_I]; ring
  calc
    8 * (-deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1)) *
        (-Complex.I * 2) * (-Complex.I * 2)) =
      -8 * deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1)) *
        ((-Complex.I * 2) * (-Complex.I * 2)) := by ring
    _ = 32 * deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1)) := by
      rw [hsq]
      ring

theorem hasDerivAt_deriv_deriv_deBruijnNewmanHeatXi_one (t : ℝ) :
    HasDerivAt (deriv (deriv (deBruijnNewmanHeatXi t)))
      (64 * (deBruijnNewmanHeatLiMomentD t : ℂ)) 1 := by
  have hinner : HasDerivAt (fun w : ℂ ↦ -Complex.I * (2 * w - 1))
      (-Complex.I * 2) 1 := by
    simpa only [id_eq, mul_one] using
      ((((hasDerivAt_id (1 : ℂ)).const_mul (2 : ℂ)).sub_const 1).const_mul
        (-Complex.I))
  have hpoint : -Complex.I * (2 * (1 : ℂ) - 1) = -Complex.I := by ring
  have hsecond : HasDerivAt (deBruijnNewmanHSecondMoment t)
      (-deBruijnNewmanHThirdMoment t (-Complex.I * (2 * (1 : ℂ) - 1)))
      (-Complex.I * (2 * (1 : ℂ) - 1)) := by
    simpa only [hpoint] using hasDerivAt_deBruijnNewmanHSecondMoment t (-Complex.I)
  have hcomp := hsecond.comp 1 hinner
  have hscaled := hcomp.const_mul (32 : ℂ)
  have hfun : deriv (deriv (deBruijnNewmanHeatXi t)) = fun s : ℂ ↦
      32 * deBruijnNewmanHSecondMoment t (-Complex.I * (2 * s - 1)) := by
    funext s
    exact deriv_deriv_deBruijnNewmanHeatXi_eq t s
  rw [hfun]
  apply hscaled.congr_deriv
  rw [hpoint, deBruijnNewmanHThirdMoment_neg_I_eq]
  calc
    32 * (-(-(deBruijnNewmanHeatLiMomentD t : ℂ) * Complex.I) *
        (-Complex.I * 2)) =
      -64 * (deBruijnNewmanHeatLiMomentD t : ℂ) *
        (Complex.I * Complex.I) := by ring
    _ = 64 * (deBruijnNewmanHeatLiMomentD t : ℂ) := by
      rw [Complex.I_mul_I]
      ring

theorem deriv_deriv_deriv_deBruijnNewmanHeatXi_one_eq (t : ℝ) :
    deriv (deriv (deriv (deBruijnNewmanHeatXi t))) 1 =
      64 * (deBruijnNewmanHeatLiMomentD t : ℂ) :=
  (hasDerivAt_deriv_deriv_deBruijnNewmanHeatXi_one t).deriv

theorem deBruijnNewmanHeatLiMomentB_mul_C_le_A_mul_D (t : ℝ) :
    deBruijnNewmanHeatLiMomentB t * deBruijnNewmanHeatLiMomentC t ≤
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentD t := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let W : ℝ → ℝ := deBruijnNewmanThirdLiWeight t
  let X : ℝ → ℝ := deBruijnNewmanThirdLiX
  let Y : ℝ → ℝ := deBruijnNewmanThirdLiY
  let A := deBruijnNewmanHeatLiMomentA t
  let B := deBruijnNewmanHeatLiMomentB t
  let C := deBruijnNewmanHeatLiMomentC t
  let D := deBruijnNewmanHeatLiMomentD t
  let m := C / A
  let r := Real.sqrt m
  have hA : 0 < A := deBruijnNewmanHeatLiMomentA_pos t
  have hC : 0 < C := deBruijnNewmanHeatLiMomentC_pos t
  have hm : 0 ≤ m := (div_pos hC hA).le
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = m := Real.sq_sqrt hm
  have hW : Integrable W μ := by
    exact integrableOn_deBruijnNewmanHeatLiMomentA_integrand t
  have hWX : Integrable (fun u ↦ W u * X u) μ := by
    apply (integrableOn_deBruijnNewmanHeatLiMomentB_integrand t).congr
    filter_upwards with u
    exact (thirdLiWeight_mul_X t u).symm
  have hWY : Integrable (fun u ↦ W u * Y u) μ := by
    apply (integrableOn_deBruijnNewmanHeatLiMomentC_integrand t).congr
    filter_upwards with u
    exact (thirdLiWeight_mul_Y t u).symm
  have hWXY : Integrable (fun u ↦ W u * X u * Y u) μ := by
    apply (integrableOn_deBruijnNewmanHeatLiMomentD_integrand t).congr
    filter_upwards with u
    exact (thirdLiWeight_mul_X_mul_Y t u).symm
  have hcert_int : Integrable
      (fun u ↦ W u * (X u - X r) * (Y u - m)) μ := by
    have hexpand : Integrable (fun u ↦
        W u * X u * Y u - m * (W u * X u) -
          X r * (W u * Y u) + (X r * m) * W u) μ :=
      ((hWXY.sub (hWX.const_mul m)).sub (hWY.const_mul (X r))).add
        (hW.const_mul (X r * m))
    apply hexpand.congr
    filter_upwards with u
    ring
  have hcert_nonneg : 0 ≤ ∫ u, W u * (X u - X r) * (Y u - m) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hweight : 0 ≤ W u := by
      dsimp only [W]
      rw [deBruijnNewmanThirdLiWeight]
      exact mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (deBruijnNewmanPhi_pos hu0).le)
        (Real.cosh_pos _).le
    have hprod : 0 ≤ (X u - X r) * (Y u - m) := by
      by_cases hur : u ≤ r
      · have hX : X u ≤ X r := thirdLiX_mono hu0 hur
        have hY : Y u ≤ m := by
          dsimp only [Y]
          rw [deBruijnNewmanThirdLiY, ← hr_sq]
          nlinarith
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hX) (sub_nonpos.mpr hY)
      · have hru : r ≤ u := le_of_not_ge hur
        have hX : X r ≤ X u := thirdLiX_mono hr hru
        have hY : m ≤ Y u := by
          dsimp only [Y]
          rw [deBruijnNewmanThirdLiY, ← hr_sq]
          nlinarith
        exact mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hY)
    calc
      0 ≤ W u * ((X u - X r) * (Y u - m)) := mul_nonneg hweight hprod
      _ = W u * (X u - X r) * (Y u - m) := by ring
  have hW_eq : (∫ u, W u ∂μ) = A := rfl
  have hWX_eq : (∫ u, W u * X u ∂μ) = B := by
    dsimp only [B]
    rw [deBruijnNewmanHeatLiMomentB]
    apply integral_congr_ae
    filter_upwards with u
    exact thirdLiWeight_mul_X t u
  have hWY_eq : (∫ u, W u * Y u ∂μ) = C := by
    dsimp only [C]
    rw [deBruijnNewmanHeatLiMomentC]
    apply integral_congr_ae
    filter_upwards with u
    exact thirdLiWeight_mul_Y t u
  have hWXY_eq : (∫ u, W u * X u * Y u ∂μ) = D := by
    dsimp only [D]
    rw [deBruijnNewmanHeatLiMomentD]
    apply integral_congr_ae
    filter_upwards with u
    exact thirdLiWeight_mul_X_mul_Y t u
  have hcert_eq :
      (∫ u, W u * (X u - X r) * (Y u - m) ∂μ) = D - m * B := by
    calc
      (∫ u, W u * (X u - X r) * (Y u - m) ∂μ) =
          ∫ u, W u * X u * Y u - m * (W u * X u) -
            X r * (W u * Y u) + (X r * m) * W u ∂μ := by
        apply integral_congr_ae
        filter_upwards with u
        ring
      _ = D - m * B - X r * C + (X r * m) * A := by
        have hadd := integral_add
          ((hWXY.sub (hWX.const_mul m)).sub (hWY.const_mul (X r)))
          (hW.const_mul (X r * m))
        have hsub_outer := integral_sub
          (hWXY.sub (hWX.const_mul m)) (hWY.const_mul (X r))
        have hsub_inner := integral_sub hWXY (hWX.const_mul m)
        calc
          (∫ u, W u * X u * Y u - m * (W u * X u) -
              X r * (W u * Y u) + (X r * m) * W u ∂μ) =
              (∫ u, W u * X u * Y u - m * (W u * X u) -
                X r * (W u * Y u) ∂μ) +
              ∫ u, (X r * m) * W u ∂μ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using hadd
          _ = ((∫ u, W u * X u * Y u - m * (W u * X u) ∂μ) -
                ∫ u, X r * (W u * Y u) ∂μ) +
              ∫ u, (X r * m) * W u ∂μ := by
            rw [show (∫ u, W u * X u * Y u - m * (W u * X u) -
                X r * (W u * Y u) ∂μ) =
              (∫ u, W u * X u * Y u - m * (W u * X u) ∂μ) -
                ∫ u, X r * (W u * Y u) ∂μ by
                  simpa only [Pi.sub_apply] using hsub_outer]
          _ = (((∫ u, W u * X u * Y u ∂μ) -
                ∫ u, m * (W u * X u) ∂μ) -
                ∫ u, X r * (W u * Y u) ∂μ) +
              ∫ u, (X r * m) * W u ∂μ := by
            rw [show (∫ u, W u * X u * Y u - m * (W u * X u) ∂μ) =
              (∫ u, W u * X u * Y u ∂μ) -
                ∫ u, m * (W u * X u) ∂μ by
                  simpa only [Pi.sub_apply] using hsub_inner]
          _ = D - m * B - X r * C + (X r * m) * A := by
            rw [integral_const_mul, integral_const_mul, integral_const_mul,
              hW_eq, hWX_eq, hWY_eq, hWXY_eq]
      _ = D - m * B := by
        have hmA : m * A = C := by
          dsimp only [m]
          field_simp
        rw [← hmA]
        ring
  rw [hcert_eq] at hcert_nonneg
  have hmain : B * C ≤ A * D := by
    have hm_eq : m = C / A := rfl
    rw [hm_eq] at hcert_nonneg
    have hA0 : A ≠ 0 := hA.ne'
    field_simp [hA0] at hcert_nonneg
    nlinarith
  exact hmain

private def deBruijnNewmanHeatLogD1 (t : ℝ) : ℂ → ℂ :=
  (deriv (deriv (deBruijnNewmanHeatXi t)) * deBruijnNewmanHeatXi t -
      deriv (deBruijnNewmanHeatXi t) * deriv (deBruijnNewmanHeatXi t)) /
    deBruijnNewmanHeatXi t ^ 2

private theorem hasDerivAt_logDeriv_deBruijnNewmanHeatXi
    (t : ℝ) (s : ℂ) (hs : deBruijnNewmanHeatXi t s ≠ 0) :
    HasDerivAt (logDeriv (deBruijnNewmanHeatXi t))
      (deBruijnNewmanHeatLogD1 t s) s := by
  have hquot := (hasDerivAt_deriv_deBruijnNewmanHeatXi t s).div
    (hasDerivAt_deBruijnNewmanHeatXi t s) hs
  rw [show logDeriv (deBruijnNewmanHeatXi t) =
      deriv (deBruijnNewmanHeatXi t) / deBruijnNewmanHeatXi t by
    funext z
    exact logDeriv_apply _ _]
  unfold deBruijnNewmanHeatLogD1
  apply hquot.congr_deriv
  rw [← (hasDerivAt_deBruijnNewmanHeatXi t s).deriv,
    ← (hasDerivAt_deriv_deBruijnNewmanHeatXi t s).deriv]
  simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]

private theorem hasDerivAt_deBruijnNewmanHeatLogD1_one (t : ℝ) :
    HasDerivAt (deBruijnNewmanHeatLogD1 t)
      (((8 * deBruijnNewmanHeatLiMomentD t /
          deBruijnNewmanHeatLiMomentA t -
        24 * deBruijnNewmanHeatLiMomentB t *
          deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t ^ 2 +
        16 * deBruijnNewmanHeatLiMomentB t ^ 3 /
          deBruijnNewmanHeatLiMomentA t ^ 3 : ℝ) : ℂ)) 1 := by
  have hnum := ((hasDerivAt_deriv_deriv_deBruijnNewmanHeatXi_one t).mul
      (hasDerivAt_deBruijnNewmanHeatXi_one t)).sub
    ((hasDerivAt_deriv_deBruijnNewmanHeatXi_one t).mul
      (hasDerivAt_deriv_deBruijnNewmanHeatXi_one t))
  have hden := (hasDerivAt_deBruijnNewmanHeatXi_one t).pow 2
  have hden_ne : deBruijnNewmanHeatXi t 1 ^ 2 ≠ 0 :=
    pow_ne_zero 2 (deBruijnNewmanHeatXi_one_ne_zero t)
  have hquot := hnum.div hden hden_ne
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at hquot
  rw [deBruijnNewmanHeatXi_one_eq,
    deriv_deBruijnNewmanHeatXi_one_eq,
    deriv_deriv_deBruijnNewmanHeatXi_one_eq] at hquot
  unfold deBruijnNewmanHeatLogD1
  apply hquot.congr_deriv
  have hA : (deBruijnNewmanHeatLiMomentA t : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (deBruijnNewmanHeatLiMomentA_pos t).ne'
  push_cast
  field_simp
  ring

private theorem hasDerivAt_deriv_logDeriv_deBruijnNewmanHeatXi_one (t : ℝ) :
    HasDerivAt (deriv (logDeriv (deBruijnNewmanHeatXi t)))
      (((8 * deBruijnNewmanHeatLiMomentD t /
          deBruijnNewmanHeatLiMomentA t -
        24 * deBruijnNewmanHeatLiMomentB t *
          deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t ^ 2 +
        16 * deBruijnNewmanHeatLiMomentB t ^ 3 /
          deBruijnNewmanHeatLiMomentA t ^ 3 : ℝ) : ℂ)) 1 := by
  have hne : ∀ᶠ s in nhds (1 : ℂ), deBruijnNewmanHeatXi t s ≠ 0 :=
    (hasDerivAt_deBruijnNewmanHeatXi_one t).continuousAt.eventually_ne
      (deBruijnNewmanHeatXi_one_ne_zero t)
  have heq : deriv (logDeriv (deBruijnNewmanHeatXi t)) =ᶠ[nhds (1 : ℂ)]
      deBruijnNewmanHeatLogD1 t := hne.mono fun s hs ↦
    (hasDerivAt_logDeriv_deBruijnNewmanHeatXi t s hs).deriv
  exact (hasDerivAt_deBruijnNewmanHeatLogD1_one t).congr_of_eventuallyEq heq

theorem iteratedDeriv_two_logDeriv_deBruijnNewmanHeatXi_one_eq (t : ℝ) :
    iteratedDeriv 2 (logDeriv (deBruijnNewmanHeatXi t)) 1 =
      (((8 * deBruijnNewmanHeatLiMomentD t /
          deBruijnNewmanHeatLiMomentA t -
        24 * deBruijnNewmanHeatLiMomentB t *
          deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t ^ 2 +
        16 * deBruijnNewmanHeatLiMomentB t ^ 3 /
          deBruijnNewmanHeatLiMomentA t ^ 3 : ℝ) : ℂ)) := by
  simpa [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ] using
    (hasDerivAt_deriv_logDeriv_deBruijnNewmanHeatXi_one t).deriv

theorem deBruijnNewmanHeatLiThree_eq (t : ℝ) :
    deBruijnNewmanHeatLiThree t =
      (((6 * deBruijnNewmanHeatLiMomentB t /
          deBruijnNewmanHeatLiMomentA t +
        12 * (deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t -
          (deBruijnNewmanHeatLiMomentB t /
            deBruijnNewmanHeatLiMomentA t) ^ 2) +
        4 * deBruijnNewmanHeatLiMomentD t /
          deBruijnNewmanHeatLiMomentA t -
        12 * deBruijnNewmanHeatLiMomentB t *
          deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t ^ 2 +
        8 * deBruijnNewmanHeatLiMomentB t ^ 3 /
          deBruijnNewmanHeatLiMomentA t ^ 3 : ℝ) : ℂ)) := by
  change 3 * deBruijnNewmanHeatLiOne t +
    3 * deriv (logDeriv (deBruijnNewmanHeatXi t)) 1 +
    (1 / 2) * iteratedDeriv 2 (logDeriv (deBruijnNewmanHeatXi t)) 1 = _
  rw [deBruijnNewmanHeatLiOne_eq,
    deriv_logDeriv_deBruijnNewmanHeatXi_one_eq,
    iteratedDeriv_two_logDeriv_deBruijnNewmanHeatXi_one_eq]
  have hA : (deBruijnNewmanHeatLiMomentA t : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (deBruijnNewmanHeatLiMomentA_pos t).ne'
  push_cast
  field_simp
  ring

theorem liCoefficientCandidate_two_eq_third_li_expression :
    liCoefficientCandidate 2 =
      3 * logDeriv riemannXi 1 +
        3 * deriv (logDeriv riemannXi) 1 +
        (1 / 2) * iteratedDeriv 2 (logDeriv riemannXi) 1 := by
  rw [liCoefficientCandidate_eq_finset_sum_iteratedDeriv_logDeriv]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  ring

theorem deBruijnNewmanHeatLiThree_zero_eq_liCoefficientCandidate_two :
    deBruijnNewmanHeatLiThree 0 = liCoefficientCandidate 2 := by
  have hxi : deBruijnNewmanHeatXi 0 = riemannXi := by
    funext s
    exact deBruijnNewmanHeatXi_zero_eq_riemannXi s
  rw [deBruijnNewmanHeatLiThree, hxi,
    liCoefficientCandidate_two_eq_third_li_expression]

theorem deBruijnNewmanHeatLiThree_zero_eq_candidate_two :
    deBruijnNewmanHeatLiThree 0 = liCoefficientCandidate 2 :=
  deBruijnNewmanHeatLiThree_zero_eq_liCoefficientCandidate_two

theorem deBruijnNewmanHeatLiOne_zero_eq_candidate_zero :
    deBruijnNewmanHeatLiOne 0 = liCoefficientCandidate 0 := by
  have hxi : deBruijnNewmanHeatXi 0 = riemannXi := by
    funext s
    exact deBruijnNewmanHeatXi_zero_eq_riemannXi s
  rw [deBruijnNewmanHeatLiOne, hxi,
    logDeriv_riemannXi_one_eq_liCoefficientCandidate_zero]

private theorem thirdLi_normalized_pos
    {A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hvariance : B ^ 2 ≤ A * C)
    (hcovariance : B * C ≤ A * D)
    (hsmall : 2 * (B / A) < 1) :
    0 < 6 * B / A + 12 * (C / A - (B / A) ^ 2) +
      4 * D / A - 12 * B * C / A ^ 2 + 8 * B ^ 3 / A ^ 3 := by
  have hA0 : A ≠ 0 := hA.ne'
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have hb : 0 < B / A := div_pos hB hA
  have hvariance' : (B / A) ^ 2 ≤ C / A := by
    calc
      (B / A) ^ 2 = B ^ 2 / A ^ 2 := by ring
      _ ≤ (A * C) / A ^ 2 :=
        (div_le_div_iff_of_pos_right hA2).2 hvariance
      _ = C / A := by field_simp
  have hcovariance' : (B / A) * (C / A) ≤ D / A := by
    calc
      (B / A) * (C / A) = (B * C) / A ^ 2 := by ring
      _ ≤ (A * D) / A ^ 2 :=
        (div_le_div_iff_of_pos_right hA2).2 hcovariance
      _ = D / A := by field_simp
  have hcoefficient : 0 ≤ 12 - 8 * (B / A) := by
    nlinarith
  have hvariance_term :
      0 ≤ (12 - 8 * (B / A)) * (C / A - (B / A) ^ 2) :=
    mul_nonneg hcoefficient (sub_nonneg.mpr hvariance')
  have hcovariance_term :
      0 ≤ 4 * (D / A - (B / A) * (C / A)) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hcovariance')
  have hpositive :
      0 < 6 * (B / A) +
        (12 - 8 * (B / A)) * (C / A - (B / A) ^ 2) +
        4 * (D / A - (B / A) * (C / A)) := by
    nlinarith
  convert hpositive using 1
  field_simp
  ring

theorem deBruijnNewmanHeatLiThree_zero_re_pos :
    0 < (deBruijnNewmanHeatLiThree 0).re := by
  rw [deBruijnNewmanHeatLiThree_eq]
  simp only [ofReal_re]
  apply thirdLi_normalized_pos
  · exact deBruijnNewmanHeatLiMomentA_pos 0
  · exact deBruijnNewmanHeatLiMomentB_pos 0
  · exact deBruijnNewmanHeatLiMomentB_sq_le_mul 0
  · exact deBruijnNewmanHeatLiMomentB_mul_C_le_A_mul_D 0
  · have hsmall := liCoefficientCandidate_zero_re_lt_one
    rw [← deBruijnNewmanHeatLiOne_zero_eq_candidate_zero,
      deBruijnNewmanHeatLiOne_eq] at hsmall
    simp only [ofReal_re] at hsmall
    convert hsmall using 1
    ring

theorem deBruijnNewmanHeatLiThree_zero_im_eq_zero :
    (deBruijnNewmanHeatLiThree 0).im = 0 := by
  rw [deBruijnNewmanHeatLiThree_eq]
  exact ofReal_im _

theorem liCoefficientCandidate_two_re_pos :
    0 < (liCoefficientCandidate 2).re := by
  rw [← deBruijnNewmanHeatLiThree_zero_eq_candidate_two]
  exact deBruijnNewmanHeatLiThree_zero_re_pos

theorem liCoefficientCandidate_two_im_eq_zero :
    (liCoefficientCandidate 2).im = 0 := by
  rw [← deBruijnNewmanHeatLiThree_zero_eq_candidate_two]
  exact deBruijnNewmanHeatLiThree_zero_im_eq_zero

/-- The fixed third-Li covariance endpoint for the exact source-normalized heat family. -/
theorem deBruijnNewmanHeat_thirdLi_covariance_endpoint :
    (∀ t : ℝ, IntegrableOn
      (fun u : ℝ ↦ u ^ 3 * Real.exp (t * u ^ 2) *
        deBruijnNewmanPhi u * Real.sinh u) (Ioi 0)) ∧
    (∀ t : ℝ, deriv (deriv (deriv (deBruijnNewmanHeatXi t))) 1 =
      64 * (deBruijnNewmanHeatLiMomentD t : ℂ)) ∧
    (∀ t : ℝ, deBruijnNewmanHeatLiMomentB t *
      deBruijnNewmanHeatLiMomentC t ≤
      deBruijnNewmanHeatLiMomentA t * deBruijnNewmanHeatLiMomentD t) ∧
    (∀ t : ℝ, deBruijnNewmanHeatLiThree t =
      (((6 * deBruijnNewmanHeatLiMomentB t /
          deBruijnNewmanHeatLiMomentA t +
        12 * (deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t -
          (deBruijnNewmanHeatLiMomentB t /
            deBruijnNewmanHeatLiMomentA t) ^ 2) +
        4 * deBruijnNewmanHeatLiMomentD t /
          deBruijnNewmanHeatLiMomentA t -
        12 * deBruijnNewmanHeatLiMomentB t *
          deBruijnNewmanHeatLiMomentC t /
          deBruijnNewmanHeatLiMomentA t ^ 2 +
        8 * deBruijnNewmanHeatLiMomentB t ^ 3 /
          deBruijnNewmanHeatLiMomentA t ^ 3 : ℝ) : ℂ))) ∧
    deBruijnNewmanHeatLiThree 0 = liCoefficientCandidate 2 ∧
    0 < (liCoefficientCandidate 2).re ∧
    (liCoefficientCandidate 2).im = 0 := by
  exact ⟨integrableOn_deBruijnNewmanHeatLiMomentD_integrand,
    deriv_deriv_deriv_deBruijnNewmanHeatXi_one_eq,
    deBruijnNewmanHeatLiMomentB_mul_C_le_A_mul_D,
    deBruijnNewmanHeatLiThree_eq,
    deBruijnNewmanHeatLiThree_zero_eq_candidate_two,
    liCoefficientCandidate_two_re_pos,
    liCoefficientCandidate_two_im_eq_zero⟩

end

end LeanLab.Riemann
