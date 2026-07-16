import LeanLab.Riemann.DeBruijnNewman
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option linter.style.header false

/-!
# Analytic heat-flow structure for the de Bruijn-Newman family

This file proves domination for the source kernel at arbitrary fixed real time and uses it to
differentiate the defining integral in time and in the complex spatial variable.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

private def dbnHeatIndexMajor (n : ℕ) : ℝ :=
  2 * π ^ 2 * HurwitzKernelBounds.f_nat 4 1 (1 / 2) n +
    3 * π * HurwitzKernelBounds.f_nat 2 1 (1 / 2) n

private theorem dbnHeatIndexMajor_nonneg (n : ℕ) : 0 ≤ dbnHeatIndexMajor n := by
  unfold dbnHeatIndexMajor HurwitzKernelBounds.f_nat
  positivity

private theorem summable_dbnHeatIndexMajor : Summable dbnHeatIndexMajor := by
  exact
    ((HurwitzKernelBounds.summable_f_nat 4 1 (by norm_num : (0 : ℝ) < 1 / 2)).mul_left
        (2 * π ^ 2)).add
      ((HurwitzKernelBounds.summable_f_nat 2 1 (by norm_num : (0 : ℝ) < 1 / 2)).mul_left
        (3 * π))

private def dbnHeatIndexMajorSum : ℝ := ∑' n : ℕ, dbnHeatIndexMajor n

private theorem dbnHeatIndexMajorSum_nonneg : 0 ≤ dbnHeatIndexMajorSum := by
  exact tsum_nonneg dbnHeatIndexMajor_nonneg

private theorem dbn_heat_gaussian_split (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)) ≤
      Real.exp (-π * ((n : ℝ) + 1) ^ 2 / 2) *
        Real.exp (-π * Real.exp (4 * u) / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hm0 : 1 ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hm : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) + 1)]
  have he : 1 ≤ Real.exp (4 * u) := Real.one_le_exp (by positivity)
  have hprod := mul_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr he)
  have hxy : 1 ≤ ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by
    simpa only [one_mul] using
      mul_le_mul hm he zero_le_one (zero_le_one.trans hm)
  have havg : (((n : ℝ) + 1) ^ 2 + Real.exp (4 * u)) / 2 ≤
      ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u) := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left havg pi_pos.le
  nlinarith

private theorem norm_deBruijnNewmanPhiTerm_le_heatMajor
    (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ‖deBruijnNewmanPhiTerm n u‖ ≤
      dbnHeatIndexMajor n * Real.exp (9 * u) *
        Real.exp (-π * Real.exp (4 * u) / 2) := by
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have h5 : Real.exp (5 * u) ≤ Real.exp (9 * u) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hsplit := dbn_heat_gaussian_split n hu
  have hA : 0 ≤ 2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) := by positivity
  have hB : 0 ≤ 3 * π * m ^ 2 * Real.exp (5 * u) := by positivity
  rw [Real.norm_eq_abs, deBruijnNewmanPhiTerm_eq]
  change
    |(2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) -
        3 * π * m ^ 2 * Real.exp (5 * u)) *
        Real.exp (-π * m ^ 2 * Real.exp (4 * u))| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    |2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) -
          3 * π * m ^ 2 * Real.exp (5 * u)| *
        Real.exp (-π * m ^ 2 * Real.exp (4 * u)) ≤
      (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) +
          3 * π * m ^ 2 * Real.exp (5 * u)) *
        Real.exp (-π * m ^ 2 * Real.exp (4 * u)) := by
      gcongr
      rw [← Real.norm_eq_abs]
      exact (norm_sub_le _ _).trans_eq (by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA, abs_of_nonneg hB])
    _ ≤ (2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) +
          3 * π * m ^ 2 * Real.exp (5 * u)) *
        (Real.exp (-π * m ^ 2 / 2) *
          Real.exp (-π * Real.exp (4 * u) / 2)) := by
      gcongr
    _ ≤ (2 * π ^ 2 * m ^ 4 + 3 * π * m ^ 2) *
          Real.exp (-π * m ^ 2 / 2) * Real.exp (9 * u) *
            Real.exp (-π * Real.exp (4 * u) / 2) := by
      have hcoeff :
          2 * π ^ 2 * m ^ 4 * Real.exp (9 * u) +
              3 * π * m ^ 2 * Real.exp (5 * u) ≤
            (2 * π ^ 2 * m ^ 4 + 3 * π * m ^ 2) * Real.exp (9 * u) := by
        nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 3 * π * m ^ 2)]
      have hmul := mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg (Real.exp_pos (-π * m ^ 2 / 2)).le
          (Real.exp_pos (-π * Real.exp (4 * u) / 2)).le)
      nlinarith
    _ = dbnHeatIndexMajor n * Real.exp (9 * u) *
          Real.exp (-π * Real.exp (4 * u) / 2) := by
      simp only [dbnHeatIndexMajor, HurwitzKernelBounds.f_nat]
      dsimp [m]
      ring_nf

private theorem norm_deBruijnNewmanPhi_le_heatMajor {u : ℝ} (hu : 0 ≤ u) :
    ‖deBruijnNewmanPhi u‖ ≤
      dbnHeatIndexMajorSum * Real.exp (9 * u) *
        Real.exp (-π * Real.exp (4 * u) / 2) := by
  have hphi := (summable_deBruijnNewmanPhiTerm u).norm
  have hmajor : Summable fun n : ℕ ↦
      dbnHeatIndexMajor n * Real.exp (9 * u) *
        Real.exp (-π * Real.exp (4 * u) / 2) :=
    (summable_dbnHeatIndexMajor.mul_right (Real.exp (9 * u))).mul_right
      (Real.exp (-π * Real.exp (4 * u) / 2))
  calc
    ‖deBruijnNewmanPhi u‖ = ‖∑' n : ℕ, deBruijnNewmanPhiTerm n u‖ := rfl
    _ ≤ ∑' n : ℕ, ‖deBruijnNewmanPhiTerm n u‖ := norm_tsum_le_tsum_norm hphi
    _ ≤ ∑' n : ℕ, dbnHeatIndexMajor n * Real.exp (9 * u) *
          Real.exp (-π * Real.exp (4 * u) / 2) :=
      hphi.tsum_le_tsum (fun n ↦ norm_deBruijnNewmanPhiTerm_le_heatMajor n hu) hmajor
    _ = _ := by
      simp_rw [mul_assoc]
      rw [tsum_mul_right]
      rfl

/-- The source kernel admits a uniform double-exponential bound on the positive half-line. -/
theorem exists_norm_deBruijnNewmanPhi_le_doubleExp :
    ∃ A ≥ 0, ∀ {u : ℝ}, 0 ≤ u →
      ‖deBruijnNewmanPhi u‖ ≤
        A * Real.exp (9 * u) * Real.exp (-(π / 2) * Real.exp (4 * u)) := by
  refine ⟨dbnHeatIndexMajorSum, dbnHeatIndexMajorSum_nonneg, ?_⟩
  intro u hu
  have hexponent : -(π / 2) * Real.exp (4 * u) =
      -π * Real.exp (4 * u) / 2 := by ring
  rw [hexponent]
  exact norm_deBruijnNewmanPhi_le_heatMajor hu

theorem integrableOn_dbn_exp_sq_mul_exp_neg_exp
    (a : ℝ) (ha : 0 < a) (c : ℝ) (_hc : 0 ≤ c) (d : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ Real.exp (c * u ^ 2 + d * u) *
        Real.exp (-a * Real.exp (4 * u))) (Ioi 0) := by
  let K : ℝ := c ^ 2 / (16 * a)
  have hbase := integrableOn_dbn_exp_mul_exp_neg_exp (a / 2) (by positivity) d
  have hmajor := hbase.const_mul (Real.exp K)
  apply Integrable.mono' hmajor
  · fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hexp4 : 8 * u ^ 4 ≤ Real.exp (4 * u) := by
      have h := Real.pow_div_factorial_le_exp (4 * u)
        (show 0 ≤ 4 * u by positivity) 4
      norm_num at h
      ring_nf at h
      calc
        8 * u ^ 4 ≤ u ^ 4 * (32 / 3 : ℝ) := by
          have hu4 : 0 ≤ u ^ 4 := by positivity
          nlinarith
        _ ≤ Real.exp (4 * u) := by simpa only [mul_comm] using h
    have hquad : c * u ^ 2 ≤ 4 * a * u ^ 4 + K := by
      have hsquare : 0 ≤ (4 * a * u ^ 2 - c / 2) ^ 2 := sq_nonneg _
      have hscaled := mul_nonneg (show 0 ≤ (4 * a)⁻¹ by positivity) hsquare
      dsimp [K]
      field_simp [ne_of_gt ha] at hscaled ⊢
      nlinarith
    have hca : c * u ^ 2 ≤ a / 2 * Real.exp (4 * u) + K := by
      nlinarith [mul_le_mul_of_nonneg_left hexp4 (show 0 ≤ a / 2 by positivity)]
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
    change Real.exp (c * u ^ 2 + d * u) * Real.exp (-a * Real.exp (4 * u)) ≤
      Real.exp K * (Real.exp (d * u) * Real.exp (-(a / 2) * Real.exp (4 * u)))
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith

private theorem integrableOn_dbn_one_add_sq_exp_sq_mul_exp_neg_exp
    (a : ℝ) (ha : 0 < a) (c : ℝ) (hc : 0 ≤ c) (d : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
        Real.exp (-a * Real.exp (4 * u))) (Ioi 0) := by
  have h0 := integrableOn_dbn_exp_sq_mul_exp_neg_exp a ha c hc d
  have h2base := integrableOn_dbn_exp_sq_mul_exp_neg_exp a ha c hc (d + 2)
  have h2 : IntegrableOn
      (fun u : ℝ ↦ u ^ 2 * Real.exp (c * u ^ 2 + d * u) *
        Real.exp (-a * Real.exp (4 * u))) (Ioi 0) := by
    apply Integrable.mono' h2base
    · fun_prop
    · rw [ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with u hu
      have hu0 : 0 ≤ u := hu.le
      have hu_exp : u ^ 2 ≤ Real.exp (2 * u) := by
        have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * u by positivity)
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ u ^ 2 * Real.exp (c * u ^ 2 + d * u) *
          Real.exp (-a * Real.exp (4 * u)))]
      change u ^ 2 * Real.exp (c * u ^ 2 + d * u) *
          Real.exp (-a * Real.exp (4 * u)) ≤
        Real.exp (c * u ^ 2 + (d + 2) * u) *
          Real.exp (-a * Real.exp (4 * u))
      gcongr
      calc
        u ^ 2 * Real.exp (c * u ^ 2 + d * u) ≤
            Real.exp (2 * u) * Real.exp (c * u ^ 2 + d * u) := by gcongr
        _ = Real.exp (c * u ^ 2 + (d + 2) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
  rw [show (fun u : ℝ ↦ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
      Real.exp (-a * Real.exp (4 * u))) =
      (fun u : ℝ ↦ Real.exp (c * u ^ 2 + d * u) *
        Real.exp (-a * Real.exp (4 * u))) +
      (fun u : ℝ ↦ u ^ 2 * Real.exp (c * u ^ 2 + d * u) *
        Real.exp (-a * Real.exp (4 * u))) by
    funext u
    simp only [Pi.add_apply]
    ring]
  exact h0.add h2

theorem integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
    (c : ℝ) (hc : 0 ≤ c) (d : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
        ‖deBruijnNewmanPhi u‖) (Ioi 0) := by
  have hbase := integrableOn_dbn_one_add_sq_exp_sq_mul_exp_neg_exp
    (π / 2) (by positivity) c hc (d + 9)
  have hmajor := hbase.const_mul dbnHeatIndexMajorSum
  apply Integrable.mono' hmajor
  · have hterms : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : ℝ ↦ deBruijnNewmanPhiTerm n u)
        (volume.restrict (Ioi 0)) := fun n ↦ by
      apply Continuous.aestronglyMeasurable
      simp_rw [deBruijnNewmanPhiTerm_eq]
      fun_prop
    have hphi : AEStronglyMeasurable deBruijnNewmanPhi
        (volume.restrict (Ioi 0)) := by
      exact MeasureTheory.AEStronglyMeasurable.tsum hterms
    have hscalar : AEStronglyMeasurable
        (fun u : ℝ ↦ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u))
        (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous (fun u : ℝ ↦
        (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u))).aestronglyMeasurable
    exact hscalar.mul hphi.norm
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have hphi := norm_deBruijnNewmanPhi_le_heatMajor hu0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
        ‖deBruijnNewmanPhi u‖)]
    change (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
        ‖deBruijnNewmanPhi u‖ ≤
      dbnHeatIndexMajorSum *
        ((1 + u ^ 2) * Real.exp (c * u ^ 2 + (d + 9) * u) *
          Real.exp (-(π / 2) * Real.exp (4 * u)))
    calc
      _ ≤ (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
          (dbnHeatIndexMajorSum * Real.exp (9 * u) *
            Real.exp (-π * Real.exp (4 * u) / 2)) := by gcongr
      _ = _ := by
        have hgauss : -(π / 2) * Real.exp (4 * u) =
            -π * Real.exp (4 * u) / 2 := by ring
        have hexp : Real.exp (c * u ^ 2 + d * u) * Real.exp (9 * u) =
            Real.exp (c * u ^ 2 + (d + 9) * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hgauss]
        calc
          (1 + u ^ 2) * Real.exp (c * u ^ 2 + d * u) *
                (dbnHeatIndexMajorSum * Real.exp (9 * u) *
                  Real.exp (-π * Real.exp (4 * u) / 2)) =
              dbnHeatIndexMajorSum * (1 + u ^ 2) *
                (Real.exp (c * u ^ 2 + d * u) * Real.exp (9 * u)) *
                  Real.exp (-π * Real.exp (4 * u) / 2) := by ring
          _ = _ := by rw [hexp]; ring

theorem aestronglyMeasurable_deBruijnNewmanPhi
    (μ : Measure ℝ) : AEStronglyMeasurable deBruijnNewmanPhi μ := by
  have hterms : ∀ n : ℕ, AEStronglyMeasurable
      (fun u : ℝ ↦ deBruijnNewmanPhiTerm n u) μ := fun n ↦ by
    apply Continuous.aestronglyMeasurable
    simp_rw [deBruijnNewmanPhiTerm_eq]
    fun_prop
  exact MeasureTheory.AEStronglyMeasurable.tsum hterms

/-- The common integral occurring in the time derivative and the negative spatial second
derivative of the de Bruijn-Newman heat family. -/
def deBruijnNewmanHSecondMoment (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0,
    (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (z * (u : ℂ)))

def deBruijnNewmanHSpatialFirstMoment (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi 0,
    (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      (-(u : ℂ) * Complex.sin (z * (u : ℂ))))

private theorem aestronglyMeasurable_dbnHeatCosIntegrand (t : ℝ) (z : ℂ) :
    AEStronglyMeasurable
      (fun u : ℝ ↦
        (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (volume.restrict (Ioi 0)) := by
  have hscalar : AEStronglyMeasurable
      (fun u : ℝ ↦ Real.exp (t * u ^ 2)) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (t * u ^ 2))).aestronglyMeasurable
  have hphi := aestronglyMeasurable_deBruijnNewmanPhi (volume.restrict (Ioi 0))
  have hreal := hscalar.mul hphi
  have hcos : AEStronglyMeasurable
      (fun u : ℝ ↦ Complex.cos (z * (u : ℂ))) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦ Complex.cos (z * (u : ℂ)))).aestronglyMeasurable
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hreal).mul hcos

private theorem aestronglyMeasurable_dbnHeatFirstMomentIntegrand (t : ℝ) (z : ℂ) :
    AEStronglyMeasurable
      (fun u : ℝ ↦
        (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          (-(u : ℂ) * Complex.sin (z * (u : ℂ)))))
      (volume.restrict (Ioi 0)) := by
  have hscalar : AEStronglyMeasurable
      (fun u : ℝ ↦ Real.exp (t * u ^ 2)) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (t * u ^ 2))).aestronglyMeasurable
  have hphi := aestronglyMeasurable_deBruijnNewmanPhi (volume.restrict (Ioi 0))
  have hreal := hscalar.mul hphi
  have hsin : AEStronglyMeasurable
      (fun u : ℝ ↦ -(u : ℂ) * Complex.sin (z * (u : ℂ)))
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦
      -(u : ℂ) * Complex.sin (z * (u : ℂ)))).aestronglyMeasurable
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hreal).mul hsin

private theorem aestronglyMeasurable_dbnHeatSecondMomentIntegrand (t : ℝ) (z : ℂ) :
    AEStronglyMeasurable
      (fun u : ℝ ↦
        (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (volume.restrict (Ioi 0)) := by
  have hu2 : AEStronglyMeasurable (fun u : ℝ ↦ u ^ 2)
      (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦ u ^ 2)).aestronglyMeasurable
  have hscalar : AEStronglyMeasurable
      (fun u : ℝ ↦ Real.exp (t * u ^ 2)) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (t * u ^ 2))).aestronglyMeasurable
  have hphi := aestronglyMeasurable_deBruijnNewmanPhi (volume.restrict (Ioi 0))
  have hreal := (hu2.mul hscalar).mul hphi
  have hcos : AEStronglyMeasurable
      (fun u : ℝ ↦ Complex.cos (z * (u : ℂ))) (volume.restrict (Ioi 0)) :=
    (by fun_prop : Continuous (fun u : ℝ ↦ Complex.cos (z * (u : ℂ)))).aestronglyMeasurable
  exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hreal).mul hcos

theorem integrableOn_dbnHeatCosIntegrand (t : ℝ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (Ioi 0) := by
  have hmajor := integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
    |t| (abs_nonneg t) ‖z‖
  apply Integrable.mono' hmajor
  · exact aestronglyMeasurable_dbnHeatCosIntegrand t z
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (z * (u : ℂ))‖ ≤
        Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖z‖ * u) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_cos_mul_real_le z hu0
      _ ≤ (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + ‖z‖ * u) *
          ‖deBruijnNewmanPhi u‖ := by
        rw [Real.exp_add]
        calc
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ * Real.exp (‖z‖ * u) =
              1 * (Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by
            gcongr
            nlinarith [sq_nonneg u]
          _ = _ := by ring

private theorem integrableOn_dbnHeatFirstMomentIntegrand (t : ℝ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          (-(u : ℂ) * Complex.sin (z * (u : ℂ))))) (Ioi 0) := by
  have hmajor := integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
    |t| (abs_nonneg t) ‖z‖
  apply Integrable.mono' hmajor
  · exact aestronglyMeasurable_dbnHeatFirstMomentIntegrand t z
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs,
      norm_mul, norm_neg, norm_real]
    rw [show ‖u‖ = u by rw [Real.norm_eq_abs, abs_of_nonneg hu0]]
    calc
      Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * ‖Complex.sin (z * (u : ℂ))‖) ≤
        Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * Real.exp (‖z‖ * u)) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_sin_mul_real_le z hu0
      _ ≤ (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + ‖z‖ * u) *
          ‖deBruijnNewmanPhi u‖ := by
        rw [Real.exp_add]
        have huBound : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
        calc
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                (u * Real.exp (‖z‖ * u)) =
              u * (Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by gcongr
          _ = _ := by ring

theorem integrableOn_dbnHeatSecondMomentIntegrand (t : ℝ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ ↦
        (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (Ioi 0) := by
  have hmajor := integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
    |t| (abs_nonneg t) ‖z‖
  apply Integrable.mono' hmajor
  · exact aestronglyMeasurable_dbnHeatSecondMomentIntegrand t z
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg u), abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      u ^ 2 * Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (z * (u : ℂ))‖ ≤
        u ^ 2 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖z‖ * u) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_cos_mul_real_le z hu0
      _ ≤ (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + ‖z‖ * u) *
          ‖deBruijnNewmanPhi u‖ := by
        rw [Real.exp_add]
        calc
          u ^ 2 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                Real.exp (‖z‖ * u) =
              u ^ 2 * (Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp (|t| * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by
            gcongr
            nlinarith [sq_nonneg u]
          _ = _ := by ring

theorem continuousAt_deBruijnNewmanHSpatialFirstMoment_joint (p : ℝ × ℂ) :
    ContinuousAt (fun q : ℝ × ℂ ↦ deBruijnNewmanHSpatialFirstMoment q.1 q.2) p := by
  change Tendsto (fun q : ℝ × ℂ ↦ deBruijnNewmanHSpatialFirstMoment q.1 q.2) (𝓝 p)
    (𝓝 (deBruijnNewmanHSpatialFirstMoment p.1 p.2))
  let F : (ℝ × ℂ) → ℝ → ℂ := fun q u ↦
    (((Real.exp (q.1 * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      (-(u : ℂ) * Complex.sin (q.2 * (u : ℂ))))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) *
      Real.exp ((|p.1| + 1) * u ^ 2 + (‖p.2‖ + 1) * u) *
        ‖deBruijnNewmanPhi u‖
  have htime : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.1 ∈ Metric.ball p.1 1 :=
    continuousAt_fst (Metric.ball_mem_nhds p.1 one_pos)
  have hspace : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.2 ∈ Metric.ball p.2 1 :=
    continuousAt_snd (Metric.ball_mem_nhds p.2 one_pos)
  have hF_meas : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      AEStronglyMeasurable (F q) (volume.restrict (Ioi 0)) := by
    filter_upwards with q
    exact aestronglyMeasurable_dbnHeatFirstMomentIntegrand q.1 q.2
  have h_bound : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      ∀ᵐ u ∂volume.restrict (Ioi 0), ‖F q u‖ ≤ bound u := by
    filter_upwards [htime, hspace] with q hqt hqz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hqtAbs : |q.1| ≤ |p.1| + 1 := by
      calc
        |q.1| = |p.1 + (q.1 - p.1)| := by congr 1; ring
        _ ≤ |p.1| + |q.1 - p.1| := abs_add_le _ _
        _ ≤ |p.1| + 1 := by
          gcongr
          simpa only [Real.dist_eq] using hqt.le
    have hqtUpper : q.1 ≤ |p.1| + 1 := (le_abs_self q.1).trans hqtAbs
    have hqzNorm : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
      calc
        ‖q.2‖ = ‖p.2 + (q.2 - p.2)‖ := by congr 1; ring
        _ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := norm_add_le _ _
        _ ≤ ‖p.2‖ + 1 := by
          gcongr
          simpa only [Complex.dist_eq] using (Metric.mem_ball.mp hqz).le
    dsimp only [F, bound]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs,
      norm_mul, norm_neg, norm_real]
    rw [show ‖u‖ = u by rw [Real.norm_eq_abs, abs_of_nonneg hu0]]
    calc
      Real.exp (q.1 * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * ‖Complex.sin (q.2 * (u : ℂ))‖) ≤
        Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * Real.exp (‖q.2‖ * u)) := by
        gcongr
        exact norm_complex_sin_mul_real_le q.2 hu0
      _ ≤ Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * Real.exp ((‖p.2‖ + 1) * u)) := by gcongr
      _ ≤ bound u := by
        dsimp only [bound]
        rw [Real.exp_add]
        have huBound : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
        calc
          Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                (u * Real.exp ((‖p.2‖ + 1) * u)) =
              u * (Real.exp ((|p.1| + 1) * u ^ 2) *
                Real.exp ((‖p.2‖ + 1) * u) * ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp ((|p.1| + 1) * u ^ 2) *
                Real.exp ((‖p.2‖ + 1) * u) * ‖deBruijnNewmanPhi u‖) := by gcongr
          _ = _ := by ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|p.1| + 1) (by positivity) (‖p.2‖ + 1)
  have h_lim : ∀ᵐ u ∂volume.restrict (Ioi 0),
      Tendsto (fun q : ℝ × ℂ ↦ F q u) (𝓝 p) (𝓝 (F p u)) := by
    filter_upwards with u
    exact (by fun_prop : ContinuousAt (fun q : ℝ × ℂ ↦ F q u) p)
  have hmain := tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound
    hbound_int h_lim
  simpa only [F, deBruijnNewmanHSpatialFirstMoment] using hmain

theorem continuous_deBruijnNewmanHSpatialFirstMoment_joint :
    Continuous (fun p : ℝ × ℂ ↦ deBruijnNewmanHSpatialFirstMoment p.1 p.2) :=
  continuous_iff_continuousAt.mpr continuousAt_deBruijnNewmanHSpatialFirstMoment_joint

theorem continuousAt_deBruijnNewmanHSecondMoment_joint (p : ℝ × ℂ) :
    ContinuousAt (fun q : ℝ × ℂ ↦ deBruijnNewmanHSecondMoment q.1 q.2) p := by
  change Tendsto (fun q : ℝ × ℂ ↦ deBruijnNewmanHSecondMoment q.1 q.2) (𝓝 p)
    (𝓝 (deBruijnNewmanHSecondMoment p.1 p.2))
  let F : (ℝ × ℂ) → ℝ → ℂ := fun q u ↦
    (((u ^ 2 * Real.exp (q.1 * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (q.2 * (u : ℂ)))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) *
      Real.exp ((|p.1| + 1) * u ^ 2 + (‖p.2‖ + 1) * u) *
        ‖deBruijnNewmanPhi u‖
  have htime : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.1 ∈ Metric.ball p.1 1 :=
    continuousAt_fst (Metric.ball_mem_nhds p.1 one_pos)
  have hspace : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.2 ∈ Metric.ball p.2 1 :=
    continuousAt_snd (Metric.ball_mem_nhds p.2 one_pos)
  have hF_meas : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      AEStronglyMeasurable (F q) (volume.restrict (Ioi 0)) := by
    filter_upwards with q
    exact aestronglyMeasurable_dbnHeatSecondMomentIntegrand q.1 q.2
  have h_bound : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      ∀ᵐ u ∂volume.restrict (Ioi 0), ‖F q u‖ ≤ bound u := by
    filter_upwards [htime, hspace] with q hqt hqz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hqtAbs : |q.1| ≤ |p.1| + 1 := by
      calc
        |q.1| = |p.1 + (q.1 - p.1)| := by congr 1; ring
        _ ≤ |p.1| + |q.1 - p.1| := abs_add_le _ _
        _ ≤ |p.1| + 1 := by
          gcongr
          simpa only [Real.dist_eq] using hqt.le
    have hqtUpper : q.1 ≤ |p.1| + 1 := (le_abs_self q.1).trans hqtAbs
    have hqzNorm : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
      calc
        ‖q.2‖ = ‖p.2 + (q.2 - p.2)‖ := by congr 1; ring
        _ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := norm_add_le _ _
        _ ≤ ‖p.2‖ + 1 := by
          gcongr
          simpa only [Complex.dist_eq] using (Metric.mem_ball.mp hqz).le
    dsimp only [F, bound]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg u), abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      u ^ 2 * Real.exp (q.1 * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (q.2 * (u : ℂ))‖ ≤
        u ^ 2 * Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖q.2‖ * u) := by
        gcongr
        exact norm_complex_cos_mul_real_le q.2 hu0
      _ ≤ u ^ 2 * Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp ((‖p.2‖ + 1) * u) := by gcongr
      _ ≤ bound u := by
        dsimp only [bound]
        rw [Real.exp_add]
        calc
          u ^ 2 * Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                Real.exp ((‖p.2‖ + 1) * u) =
              u ^ 2 * (Real.exp ((|p.1| + 1) * u ^ 2) *
                Real.exp ((‖p.2‖ + 1) * u) * ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp ((|p.1| + 1) * u ^ 2) *
                Real.exp ((‖p.2‖ + 1) * u) * ‖deBruijnNewmanPhi u‖) := by
            gcongr
            nlinarith [sq_nonneg u]
          _ = _ := by ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|p.1| + 1) (by positivity) (‖p.2‖ + 1)
  have h_lim : ∀ᵐ u ∂volume.restrict (Ioi 0),
      Tendsto (fun q : ℝ × ℂ ↦ F q u) (𝓝 p) (𝓝 (F p u)) := by
    filter_upwards with u
    exact (by fun_prop : ContinuousAt (fun q : ℝ × ℂ ↦ F q u) p)
  have hmain := tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound
    hbound_int h_lim
  simpa only [F, deBruijnNewmanHSecondMoment] using hmain

theorem continuous_deBruijnNewmanHSecondMoment_joint :
    Continuous (fun p : ℝ × ℂ ↦ deBruijnNewmanHSecondMoment p.1 p.2) :=
  continuous_iff_continuousAt.mpr continuousAt_deBruijnNewmanHSecondMoment_joint

private theorem hasDerivAt_dbnHeatTimeExp (t u : ℝ) :
    HasDerivAt (fun tau : ℝ ↦ Real.exp (tau * u ^ 2))
      (u ^ 2 * Real.exp (t * u ^ 2)) t := by
  simpa only [smul_eq_mul, ← Real.exp_eq_exp_ℝ] using
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := ℝ) (u ^ 2) t)

private theorem hasDerivAt_dbnHeatCosIntegrand_time (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun tau : ℝ ↦
        (((Real.exp (tau * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))))
      (((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ))) t := by
  have hreal := (hasDerivAt_dbnHeatTimeExp t u).mul_const (deBruijnNewmanPhi u)
  have hcomplex := hreal.ofReal_comp
  simpa only [mul_assoc] using hcomplex.mul_const (Complex.cos (z * (u : ℂ)))

theorem hasDerivAt_deBruijnNewmanH_time (t : ℝ) (z : ℂ) :
    HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanH tau z)
      (deBruijnNewmanHSecondMoment t z) t := by
  let F : ℝ → ℝ → ℂ := fun tau u ↦
    (((Real.exp (tau * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (z * (u : ℂ)))
  let F' : ℝ → ℝ → ℂ := fun tau u ↦
    (((u ^ 2 * Real.exp (tau * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (z * (u : ℂ)))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp ((|t| + 1) * u ^ 2 + ‖z‖ * u) *
      ‖deBruijnNewmanPhi u‖
  have hs : Metric.ball t 1 ∈ 𝓝 t := Metric.ball_mem_nhds t one_pos
  have hF_meas : ∀ᶠ tau in 𝓝 t,
      AEStronglyMeasurable (F tau) (volume.restrict (Ioi 0)) := by
    filter_upwards with tau
    exact aestronglyMeasurable_dbnHeatCosIntegrand tau z
  have hF_int : Integrable (F t) (volume.restrict (Ioi 0)) := by
    exact integrableOn_dbnHeatCosIntegrand t z
  have hF'_meas : AEStronglyMeasurable (F' t) (volume.restrict (Ioi 0)) := by
    exact aestronglyMeasurable_dbnHeatSecondMomentIntegrand t z
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ∀ tau ∈ Metric.ball t 1, ‖F' tau u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu tau htau
    have hu0 : 0 ≤ u := hu.le
    have htauAbs : |tau| ≤ |t| + 1 := by
      calc
        |tau| = |t + (tau - t)| := by congr 1; ring
        _ ≤ |t| + |tau - t| := abs_add_le _ _
        _ ≤ |t| + 1 := by
          gcongr
          simpa only [Real.dist_eq] using htau.le
    have htauUpper : tau ≤ |t| + 1 := (le_abs_self tau).trans htauAbs
    dsimp only [F', bound]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg u), abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      u ^ 2 * Real.exp (tau * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (z * (u : ℂ))‖ ≤
        u ^ 2 * Real.exp ((|t| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖z‖ * u) := by
        gcongr
        · exact norm_complex_cos_mul_real_le z hu0
      _ ≤ bound u := by
        dsimp only [bound]
        rw [Real.exp_add]
        calc
          u ^ 2 * Real.exp ((|t| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                Real.exp (‖z‖ * u) =
              u ^ 2 * (Real.exp ((|t| + 1) * u ^ 2) * Real.exp (‖z‖ * u) *
                ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp ((|t| + 1) * u ^ 2) *
                Real.exp (‖z‖ * u) * ‖deBruijnNewmanPhi u‖) := by
            gcongr
            nlinarith [sq_nonneg u]
          _ = _ := by ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    exact integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|t| + 1) (by positivity) ‖z‖
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ∀ tau ∈ Metric.ball t 1, HasDerivAt (F · u) (F' tau u) tau := by
    filter_upwards with u tau _
    exact hasDerivAt_dbnHeatCosIntegrand_time tau z u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa only [F, F', deBruijnNewmanH, deBruijnNewmanHSecondMoment] using hmain.2

private theorem hasDerivAt_dbnCos_spatial (z : ℂ) (u : ℝ) :
    HasDerivAt (fun w : ℂ ↦ Complex.cos (w * (u : ℂ)))
      (-(u : ℂ) * Complex.sin (z * (u : ℂ))) z := by
  convert! (Complex.hasDerivAt_cos (z * (u : ℂ))).comp z
    ((hasDerivAt_id z).mul_const (u : ℂ)) using 1
  ring

private theorem hasDerivAt_dbnHeatCosIntegrand_spatial (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ ↦
        (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          Complex.cos (w * (u : ℂ))))
      (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
        (-(u : ℂ) * Complex.sin (z * (u : ℂ)))) z := by
  simpa only using (hasDerivAt_dbnCos_spatial z u).const_mul
    ((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ)

theorem hasDerivAt_deBruijnNewmanH_spatial (t : ℝ) (z : ℂ) :
    HasDerivAt (deBruijnNewmanH t) (deBruijnNewmanHSpatialFirstMoment t z) z := by
  let F : ℂ → ℝ → ℂ := fun w u ↦
    (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (w * (u : ℂ)))
  let F' : ℂ → ℝ → ℂ := fun w u ↦
    (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      (-(u : ℂ) * Complex.sin (w * (u : ℂ))))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + (‖z‖ + 1) * u) *
      ‖deBruijnNewmanPhi u‖
  have hs : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z one_pos
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards with w
    exact aestronglyMeasurable_dbnHeatCosIntegrand t w
  have hF_int : Integrable (F z) (volume.restrict (Ioi 0)) := by
    exact integrableOn_dbnHeatCosIntegrand t z
  have hF'_meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    exact aestronglyMeasurable_dbnHeatFirstMomentIntegrand t z
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
        _ ≤ ‖z‖ + 1 := by
          gcongr
    dsimp only [F', bound]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs,
      norm_mul, norm_neg, norm_real]
    rw [show ‖u‖ = u by rw [Real.norm_eq_abs, abs_of_nonneg hu0]]
    calc
      Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * ‖Complex.sin (w * (u : ℂ))‖) ≤
        Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * Real.exp (‖w‖ * u)) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_sin_mul_real_le w hu0
      _ ≤ Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          (u * Real.exp ((‖z‖ + 1) * u)) := by
        gcongr
      _ ≤ bound u := by
        dsimp only [bound]
        rw [Real.exp_add]
        have huBound : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
        calc
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                (u * Real.exp ((‖z‖ + 1) * u)) =
              u * (Real.exp (|t| * u ^ 2) * Real.exp ((‖z‖ + 1) * u) *
                ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp (|t| * u ^ 2) *
                Real.exp ((‖z‖ + 1) * u) * ‖deBruijnNewmanPhi u‖) := by gcongr
          _ = _ := by ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    exact integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      |t| (abs_nonneg t) (‖z‖ + 1)
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z 1, HasDerivAt (F · u) (F' w u) w := by
    filter_upwards with u w _
    exact hasDerivAt_dbnHeatCosIntegrand_spatial t w u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa only [F, F', deBruijnNewmanH, deBruijnNewmanHSpatialFirstMoment] using! hmain.2

theorem differentiable_deBruijnNewmanH (t : ℝ) :
    Differentiable ℂ (deBruijnNewmanH t) :=
  fun z ↦ (hasDerivAt_deBruijnNewmanH_spatial t z).differentiableAt

theorem deriv_deBruijnNewmanH (t : ℝ) (z : ℂ) :
    deriv (deBruijnNewmanH t) z = deBruijnNewmanHSpatialFirstMoment t z :=
  (hasDerivAt_deBruijnNewmanH_spatial t z).deriv

theorem deriv_deBruijnNewmanH_zero (t : ℝ) :
    deriv (deBruijnNewmanH t) 0 = 0 := by
  rw [deriv_deBruijnNewmanH, deBruijnNewmanHSpatialFirstMoment]
  simp

private theorem hasDerivAt_dbnFirstSpatialFactor (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ ↦ -(u : ℂ) * Complex.sin (w * (u : ℂ)))
      (-((u : ℂ) ^ 2) * Complex.cos (z * (u : ℂ))) z := by
  have hsin := (Complex.hasDerivAt_sin (z * (u : ℂ))).comp z
    ((hasDerivAt_id z).mul_const (u : ℂ))
  convert! hsin.const_mul (-(u : ℂ)) using 1
  ring

private theorem hasDerivAt_dbnHeatFirstMomentIntegrand_spatial
    (t : ℝ) (z : ℂ) (u : ℝ) :
    HasDerivAt
      (fun w : ℂ ↦
        (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          (-(u : ℂ) * Complex.sin (w * (u : ℂ)))))
      (-(((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ)))) z := by
  have h := (hasDerivAt_dbnFirstSpatialFactor z u).const_mul
    ((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ)
  convert! h using 1
  push_cast
  ring

private theorem hasDerivAt_deBruijnNewmanHSpatialFirstMoment
    (t : ℝ) (z : ℂ) :
    HasDerivAt (deBruijnNewmanHSpatialFirstMoment t)
      (-deBruijnNewmanHSecondMoment t z) z := by
  let F : ℂ → ℝ → ℂ := fun w u ↦
    (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      (-(u : ℂ) * Complex.sin (w * (u : ℂ))))
  let F' : ℂ → ℝ → ℂ := fun w u ↦
    -(((u ^ 2 * Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (w * (u : ℂ)))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + (‖z‖ + 1) * u) *
      ‖deBruijnNewmanPhi u‖
  have hs : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z one_pos
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards with w
    exact aestronglyMeasurable_dbnHeatFirstMomentIntegrand t w
  have hF_int : Integrable (F z) (volume.restrict (Ioi 0)) := by
    exact integrableOn_dbnHeatFirstMomentIntegrand t z
  have hF'_meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    exact (aestronglyMeasurable_dbnHeatSecondMomentIntegrand t z).neg
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
        _ ≤ ‖z‖ + 1 := by
          gcongr
    dsimp only [F', bound]
    rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (sq_nonneg u), abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      u ^ 2 * Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (w * (u : ℂ))‖ ≤
        u ^ 2 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖w‖ * u) := by
        gcongr
        · exact le_abs_self t
        · exact norm_complex_cos_mul_real_le w hu0
      _ ≤ u ^ 2 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp ((‖z‖ + 1) * u) := by
        gcongr
      _ ≤ bound u := by
        dsimp only [bound]
        rw [Real.exp_add]
        calc
          u ^ 2 * Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                Real.exp ((‖z‖ + 1) * u) =
              u ^ 2 * (Real.exp (|t| * u ^ 2) * Real.exp ((‖z‖ + 1) * u) *
                ‖deBruijnNewmanPhi u‖) := by ring
          _ ≤ (1 + u ^ 2) * (Real.exp (|t| * u ^ 2) *
                Real.exp ((‖z‖ + 1) * u) * ‖deBruijnNewmanPhi u‖) := by
            gcongr
            nlinarith [sq_nonneg u]
          _ = _ := by ring
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    exact integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      |t| (abs_nonneg t) (‖z‖ + 1)
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z 1, HasDerivAt (F · u) (F' w u) w := by
    filter_upwards with u w _
    exact hasDerivAt_dbnHeatFirstMomentIntegrand_spatial t w u
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa only [F, F', deBruijnNewmanHSpatialFirstMoment,
    deBruijnNewmanHSecondMoment, integral_neg] using! hmain.2

theorem hasDerivAt_deriv_deBruijnNewmanH (t : ℝ) (z : ℂ) :
    HasDerivAt (deriv (deBruijnNewmanH t))
      (-deBruijnNewmanHSecondMoment t z) z := by
  have hfun : deriv (deBruijnNewmanH t) = deBruijnNewmanHSpatialFirstMoment t := by
    funext w
    exact deriv_deBruijnNewmanH t w
  rw [hfun]
  exact hasDerivAt_deBruijnNewmanHSpatialFirstMoment t z

theorem deriv_deriv_deBruijnNewmanH (t : ℝ) (z : ℂ) :
    deriv (deriv (deBruijnNewmanH t)) z = -deBruijnNewmanHSecondMoment t z :=
  (hasDerivAt_deriv_deBruijnNewmanH t z).deriv

/-- The source-normalized de Bruijn-Newman family satisfies the backward heat equation on all
real times and all complex spatial parameters. -/
theorem deBruijnNewmanH_backward_heat_equation (t : ℝ) (z : ℂ) :
    deriv (fun tau : ℝ ↦ deBruijnNewmanH tau z) t =
      -deriv (deriv (deBruijnNewmanH t)) z := by
  rw [(hasDerivAt_deBruijnNewmanH_time t z).deriv,
    deriv_deriv_deBruijnNewmanH]
  ring

end

end LeanLab.Riemann
