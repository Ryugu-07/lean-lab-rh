import LeanLab.Riemann.DeBruijnNewmanPolymathBoydNormalizedCoordinate
import LeanLab.Riemann.DeBruijnNewmanPolymathBoydAdjacentSaddleCauchy

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Adjacent landing and inverse Jacobian for the normalized Boyd coordinate

This module applies the global normalized-coordinate inverse to the two adjacent Boyd contours.
It first exposes the actual inverse Jacobian and its Cauchy expansion, then proves the radial
landing statements and the resulting maximal centered continuation radius.
-/

namespace LeanLab.Riemann

open Complex Filter Metric Set
open scoped Topology

noncomputable section

/-- The actual normalized-coordinate inverse is analytic throughout its natural disk. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticOnNhd :
    AnalyticOnNhd ℂ deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
      deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
  fun _ hw => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hw

/-- The actual inverse takes every point of the coordinate disk back to the first phase domain. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_mem_originPhaseDomain
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w ∈
      deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk := ⟨w, hw⟩
  rw [show deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w =
      (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD : ℂ) by
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_apply wD]
  exact (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD).property

/-- The global normalized coordinate is a right inverse to the actual ambient inverse on the
coordinate disk. -/
theorem deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_inverse
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
        (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) = w := by
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk := ⟨w, hw⟩
  rw [show deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w =
      (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD : ℂ) by
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_apply wD]
  have happly := congrArg Subtype.val
    (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.apply_symm_apply wD)
  simpa only [deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph_apply,
    deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain] using happly

/-- The actual inverse satisfies the phase equation on the complete first coordinate disk. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_phase
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) = w ^ 2 / 2 := by
  apply deBruijnNewmanPolymathBoydOriginInverseBranch_phaseOn_ball
      (U := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse)
      (R := 2 * Real.sqrt Real.pi) (by positivity)
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticOnNhd
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local
  simpa [deBruijnNewmanPolymathBoydOpenCoordinateDisk] using hw

/-- Chain-rule form of the inverse Jacobian identity for the global coordinate. -/
theorem deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_mul
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) *
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w = 1 := by
  let U := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
  let G := deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
  have hU : HasDerivAt U (deriv U w) w :=
    (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hw).differentiableAt.hasDerivAt
  have hmem : U w ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_mem_originPhaseDomain hw
  have hG : HasDerivAt G (deriv G (U w)) (U w) :=
    (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt hmem.1).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (G ∘ U) (deriv G (U w) * deriv U w) w :=
    hG.comp w hU
  have hopen : IsOpen deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball
  have hright : (G ∘ U) =ᶠ[𝓝 w] id := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_inverse hz
  have hid : HasDerivAt (G ∘ U) 1 w := (hasDerivAt_id w).congr_of_eventuallyEq hright
  exact hcomp.unique hid

/-- Differentiating the phase equation gives the source-normalized inverse-Jacobian identity. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverseJacobian_phase
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    (Complex.exp (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) - 1) *
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w = w := by
  let U := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
  let phase := deBruijnNewmanPolymathBoydComplexSaddlePhase
  have hU : HasDerivAt U (deriv U w) w :=
    (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hw).differentiableAt.hasDerivAt
  have hphase : HasDerivAt phase (Complex.exp (U w) - 1) (U w) := by
    have hraw :=
      (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt (U w)).differentiableAt.hasDerivAt
    rw [deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase] at hraw
    exact hraw
  have hcomp : HasDerivAt (phase ∘ U)
      ((Complex.exp (U w) - 1) * deriv U w) w := hphase.comp w hU
  have hopen : IsOpen deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball
  have heq : (phase ∘ U) =ᶠ[𝓝 w] fun z : ℂ => z ^ 2 / 2 := by
    filter_upwards [hopen.mem_nhds hw] with z hz
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_phase hz
  have hquadratic : HasDerivAt (fun z : ℂ => z ^ 2 / 2) w w := by
    have hraw := ((hasDerivAt_id w).pow 2).div_const 2
    simpa only [Pi.pow_apply, id_eq] using
      hraw.congr_deriv (by simp only [id_eq]; ring)
  exact hcomp.unique (hquadratic.congr_of_eventuallyEq heq)

/-- The normalized inverse has derivative one at the origin. -/
theorem deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero :
    deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse 0 = 1 := by
  have hzero : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskZero.property
  have hproduct :=
    deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_mul hzero
  have hUzero : deBruijnNewmanPolymathBoydNormalizedCoordinateInverse 0 = 0 := by
    have hlocal :=
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local.self_of_nhds
    rw [hlocal]
    have hleft :=
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_left.self_of_nhds
    simpa using hleft
  simpa [hUzero, deriv_deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero] using hproduct

/-- The actual inverse Jacobian has its Cauchy power series on every smaller centered disk. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverseJacobian_hasCauchyPowerSeriesOnBall
    {r : NNReal} (hr0 : 0 < r)
    (hr : (r : ℝ) < 2 * Real.sqrt Real.pi) :
    HasFPowerSeriesOnBall
      (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse)
      (cauchyPowerSeries
        (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) 0 r)
      0 r := by
  exact deBruijnNewmanPolymathBoydOriginInverseJacobian_hasCauchyPowerSeriesOnBall
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticOnNhd hr0 hr

private theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_neg_lt_two_pi
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter (-t) < 2 * Real.pi := by
  let y := deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter (-t)
  have hy := deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem (-t)
  have hmag := deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_liftParameter (-t)
  have htle : t ≤ 2 * Real.pi := ht.le
  simp only [neg_neg, max_eq_left ht0, min_eq_left htle] at hmag
  have hyne : y ≠ 2 * Real.pi := by
    intro heq
    change deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter (-t) =
      2 * Real.pi at heq
    rw [heq,
      deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_two_pi] at hmag
    linarith
  exact lt_of_le_of_ne hy.2 hyne

/-- Every nonterminal point of the upper adjacent contour lies in the actual first phase domain. -/
theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_mem_originPhaseDomain
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t) ∈
      deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  constructor
  · rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
      deBruijnNewmanPolymathBoydAdjacentContourPlus_im]
    have hy0 :=
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem (-t)).1
    rw [abs_of_nonneg hy0]
    exact deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_neg_lt_two_pi ht0 ht
  · have hphase :=
      deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPhaseLift
        (s := -t) ⟨by linarith, neg_nonpos.mpr ht0⟩
    rw [hphase, norm_mul, norm_real, norm_I, mul_one]
    simpa [Real.norm_eq_abs, abs_of_nonneg ht0] using ht

/-- Every nonterminal point of the lower adjacent contour lies in the actual first phase domain. -/
theorem deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_mem_originPhaseDomain
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t ∈
      deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  constructor
  · rw [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift, Complex.conj_im,
      abs_neg, deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
      deBruijnNewmanPolymathBoydAdjacentContourPlus_im]
    have hy0 :=
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem (-t)).1
    rw [abs_of_nonneg hy0]
    exact deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_neg_lt_two_pi ht0 ht
  · have hphase :=
      deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourNegativePhaseLift
        (s := t) ⟨ht0, ht.le⟩
    rw [hphase, norm_mul, norm_real, norm_I, mul_one]
    simpa [Real.norm_eq_abs, abs_of_nonneg ht0] using ht

private theorem deBruijnNewmanPolymathBoydGlobalCoordinate_upper_eventually_eq_principal :
    (fun t : ℝ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))) =ᶠ[𝓝 0]
    (fun t : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))) := by
  have hlift : Tendsto
      (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))
      (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt
        (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) 0 :=
      (continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift.comp
        continuous_id.neg).continuousAt
    change Tendsto
      (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))
      (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-(0 : ℝ)))) at hcont
    rw [neg_zero, deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_zero] at hcont
    exact hcont
  exact hlift deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_eventually_eq_local

/-- The Loop 23 global coordinate has the Loop 19 sign along the upper adjacent contour. -/
theorem deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_upper
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simp [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero]
  · have hevent :=
      deBruijnNewmanPolymathBoydGlobalCoordinate_upper_eventually_eq_principal
    rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hεsub⟩
    let δ : ℝ := min (t / 2) (ε / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos htpos) (half_pos hε)
    have hδt : δ ≤ t := by
      calc
        δ ≤ t / 2 := min_le_left _ _
        _ ≤ t := half_le_self htpos.le
    have hδlt : δ < 2 * Real.pi := hδt.trans_lt ht
    have hδball : δ ∈ ball (0 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
      exact (min_le_right (t / 2) (ε / 2)).trans_lt (half_lt_self hε)
    have hanchor :
        deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-δ)) =
          deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-δ)) :=
      hεsub hδball
    have hsub : Icc δ t ⊆ Icc 0 (2 * Real.pi) := by
      intro r hr
      exact ⟨hδpos.le.trans hr.1, hr.2.trans ht.le⟩
    have hglobalContinuous : ContinuousOn
        (fun r : ℝ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r))) (Icc δ t) := by
      intro r hr
      have hr0 : 0 ≤ r := hδpos.le.trans hr.1
      have hrlt : r < 2 * Real.pi := hr.2.trans_lt ht
      have hcoordinate :=
        (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_mem_originPhaseDomain
            hr0 hrlt).1).continuousAt
      have hlift : ContinuousAt
          (fun s : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-s)) r :=
        (continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift.comp
          continuous_id.neg).continuousAt
      exact (ContinuousAt.comp'
        (f := fun s : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-s))
        hcoordinate hlift).continuousWithinAt
    have hprincipalContinuous : ContinuousOn
        (fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r))) (Icc δ t) := by
      change ContinuousOn deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift
        (Icc δ t)
      exact continuousOn_deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift.mono hsub
    have hsq : Set.EqOn
        ((fun r : ℝ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r))) ^ 2)
        ((fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r))) ^ 2)
        (Icc δ t) := by
      intro r hr
      change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) ^ 2 =
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) ^ 2
      have hr0 : 0 ≤ r := hδpos.le.trans hr.1
      have hrlt : r < 2 * Real.pi := hr.2.trans_lt ht
      have hglobal := deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_sq
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_mem_originPhaseDomain
          hr0 hrlt).1
      have hprincipal := deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r))
      linear_combination 2 * hglobal - 2 * hprincipal
    have hprincipal_ne : ∀ {r : ℝ}, r ∈ Icc δ t →
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) ≠ 0 := by
      intro r hr
      have hr0 : 0 ≤ r := hδpos.le.trans hr.1
      have hrmem : r ∈ Icc 0 (2 * Real.pi) := hsub hr
      have hray :=
        deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_eq_radialRay hrmem
      change deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) ≠ 0
      rw [show deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-r)) =
          deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 r by
        simpa [deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift] using hray]
      have hrpos : 0 < r := hδpos.trans_le hr.1
      have hscale : Real.sqrt r / Real.sqrt (2 * Real.pi) ≠ 0 :=
        div_ne_zero (Real.sqrt_ne_zero'.mpr hrpos) (by positivity)
      unfold deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
      exact mul_ne_zero (by exact_mod_cast hscale)
        (deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero (by norm_num))
    have hall := isPreconnected_Icc.eq_of_sq_eq hglobalContinuous hprincipalContinuous
      hsq hprincipal_ne (show δ ∈ Icc δ t from ⟨le_rfl, hδt⟩) hanchor
    calc
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) =
          deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) :=
        hall ⟨hδt, le_rfl⟩
      _ = deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t := by
        simpa [deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift] using
          deBruijnNewmanPolymathBoydAdjacentContourUpperCoordinateLift_eq_radialRay
            (show t ∈ Icc 0 (2 * Real.pi) from ⟨htpos.le, ht.le⟩)

private theorem deBruijnNewmanPolymathBoydGlobalCoordinate_lower_eventually_eq_principal :
    (fun t : ℝ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)) =ᶠ[𝓝 0]
    (fun t : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t)) := by
  have hlift : Tendsto deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift
      (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt
        deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift 0 :=
      continuous_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift.continuousAt
    change Tendsto deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift
      (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift 0)) at hcont
    rw [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_zero] at hcont
    exact hcont
  exact hlift deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_eventually_eq_local

/-- The Loop 23 global coordinate has the Loop 19 sign along the lower adjacent contour. -/
theorem deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_lower
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t) =
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · simp [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero]
  · have hevent :=
      deBruijnNewmanPolymathBoydGlobalCoordinate_lower_eventually_eq_principal
    rcases Metric.mem_nhds_iff.mp hevent with ⟨ε, hε, hεsub⟩
    let δ : ℝ := min (t / 2) (ε / 2)
    have hδpos : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos htpos) (half_pos hε)
    have hδt : δ ≤ t := by
      calc
        δ ≤ t / 2 := min_le_left _ _
        _ ≤ t := half_le_self htpos.le
    have hδball : δ ∈ ball (0 : ℝ) ε := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
      exact (min_le_right (t / 2) (ε / 2)).trans_lt (half_lt_self hε)
    have hanchor :
        deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift δ) =
          deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift δ) :=
      hεsub hδball
    have hsub : Icc δ t ⊆ Icc 0 (2 * Real.pi) := by
      intro r hr
      exact ⟨hδpos.le.trans hr.1, hr.2.trans ht.le⟩
    have hglobalContinuous : ContinuousOn
        (fun r : ℝ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r)) (Icc δ t) := by
      intro r hr
      have hr0 : 0 ≤ r := hδpos.le.trans hr.1
      have hrlt : r < 2 * Real.pi := hr.2.trans_lt ht
      have hcoordinate :=
        (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_mem_originPhaseDomain
            hr0 hrlt).1).continuousAt
      exact (ContinuousAt.comp'
        (f := deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift)
        hcoordinate
        continuous_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift.continuousAt
        ).continuousWithinAt
    have hprincipalContinuous : ContinuousOn
        (fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r)) (Icc δ t) := by
      change ContinuousOn deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift
        (Icc δ t)
      exact continuousOn_deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift.mono hsub
    have hsq : Set.EqOn
        ((fun r : ℝ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r)) ^ 2)
        ((fun r : ℝ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r)) ^ 2)
        (Icc δ t) := by
      intro r hr
      change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r) ^ 2 =
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r) ^ 2
      have hr0 : 0 ≤ r := hδpos.le.trans hr.1
      have hrlt : r < 2 * Real.pi := hr.2.trans_lt ht
      have hglobal := deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_sq
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_mem_originPhaseDomain
          hr0 hrlt).1
      have hprincipal := deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r)
      linear_combination 2 * hglobal - 2 * hprincipal
    have hprincipal_ne : ∀ {r : ℝ}, r ∈ Icc δ t →
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r) ≠ 0 := by
      intro r hr
      have hrmem : r ∈ Icc 0 (2 * Real.pi) := hsub hr
      have hray :=
        deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_eq_radialRay hrmem
      change deBruijnNewmanPolymathBoydComplexSaddleCoordinate
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r) ≠ 0
      rw [show deBruijnNewmanPolymathBoydComplexSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift r) =
          deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) r by
        simpa [deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift] using hray]
      have hrpos : 0 < r := hδpos.trans_le hr.1
      have hscale : Real.sqrt r / Real.sqrt (2 * Real.pi) ≠ 0 :=
        div_ne_zero (Real.sqrt_ne_zero'.mpr hrpos) (by positivity)
      unfold deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay
      exact mul_ne_zero (by exact_mod_cast hscale)
        (deBruijnNewmanPolymathBoydComplexSaddleImage_ne_zero (by norm_num))
    have hall := isPreconnected_Icc.eq_of_sq_eq hglobalContinuous hprincipalContinuous
      hsq hprincipal_ne (show δ ∈ Icc δ t from ⟨le_rfl, hδt⟩) hanchor
    calc
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
          (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t) =
          deBruijnNewmanPolymathBoydComplexSaddleCoordinate
            (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t) :=
        hall ⟨hδt, le_rfl⟩
      _ = deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t := by
        simpa [deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift] using
          deBruijnNewmanPolymathBoydAdjacentContourLowerCoordinateLift_eq_radialRay
            (show t ∈ Icc 0 (2 * Real.pi) from ⟨htpos.le, ht.le⟩)

private theorem deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_one_mem_coordinateDisk
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t ∈
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  have hu := deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_mem_originPhaseDomain ht0 ht
  have hmem :=
    (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain ⟨_, hu⟩).property
  change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) ∈
    deBruijnNewmanPolymathBoydOpenCoordinateDisk at hmem
  rw [deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_upper ht0 ht] at hmem
  exact hmem

private theorem deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_neg_one_mem_coordinateDisk
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t ∈
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  have hu :=
    deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_mem_originPhaseDomain ht0 ht
  have hmem :=
    (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain ⟨_, hu⟩).property
  change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
      (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t) ∈
    deBruijnNewmanPolymathBoydOpenCoordinateDisk at hmem
  rw [deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_lower ht0 ht] at hmem
  exact hmem

/-- The actual disk inverse lifts the upper adjacent radial ray to the upper Boyd contour. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t) := by
  let uD : deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    ⟨deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t),
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_mem_originPhaseDomain ht0 ht⟩
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    ⟨deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t,
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_one_mem_coordinateDisk ht0 ht⟩
  have hcoordinate :
      deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph uD = wD := by
    apply Subtype.ext
    exact deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_upper ht0 ht
  have hinverse :
      deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD = uD := by
    rw [← hcoordinate]
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm_apply_apply uD
  calc
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
        (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD : ℂ) :=
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_apply wD
    _ = deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t) :=
      congrArg Subtype.val hinverse

/-- The actual disk inverse lifts the lower adjacent radial ray to the lower Boyd contour. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
      deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t := by
  let uD : deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    ⟨deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t,
      deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_mem_originPhaseDomain ht0 ht⟩
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    ⟨deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t,
      deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_neg_one_mem_coordinateDisk ht0 ht⟩
  have hcoordinate :
      deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph uD = wD := by
    apply Subtype.ext
    exact deBruijnNewmanPolymathBoydGlobalCoordinate_adjacentContour_lower ht0 ht
  have hinverse :
      deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD = uD := by
    rw [← hcoordinate]
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm_apply_apply uD
  calc
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
        (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD : ℂ) :=
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_apply wD
    _ = deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t :=
      congrArg Subtype.val hinverse

/-- The actual origin branch lands at the upper adjacent Boyd saddle. -/
theorem tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper :
    Tendsto
      (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t))
      (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint 1)) := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[Iio (2 * Real.pi)] (2 * Real.pi), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  have heq :
      (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) =ᶠ[
          𝓝[Iio (2 * Real.pi)] (2 * Real.pi)]
      (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) := by
    filter_upwards [eventually_mem_nhdsWithin, hpos] with t ht htp
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper
      htp.le ht
  have hcont : Tendsto
      (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))
      (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint 1)) := by
    have hfull : ContinuousAt
        (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))
        (2 * Real.pi) :=
      (continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift.comp
        continuous_id.neg).continuousAt
    change Tendsto
      (fun t : ℝ => deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t))
      (𝓝 (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-(2 * Real.pi)))) at hfull
    rw [show -(2 * Real.pi) = -2 * Real.pi by ring,
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_two_pi] at hfull
    exact hfull.mono_left inf_le_left
  exact Tendsto.congr' heq.symm hcont

/-- The actual origin branch lands at the lower adjacent Boyd saddle. -/
theorem tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower :
    Tendsto
      (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t))
      (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint (-1))) := by
  have hpos : ∀ᶠ t : ℝ in 𝓝[Iio (2 * Real.pi)] (2 * Real.pi), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  have heq :
      (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t)) =ᶠ[
          𝓝[Iio (2 * Real.pi)] (2 * Real.pi)]
      deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift := by
    filter_upwards [eventually_mem_nhdsWithin, hpos] with t ht htp
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower
      htp.le ht
  exact Tendsto.congr' heq.symm
    tendsto_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_at_two_pi

/-- Every centered analytic continuation of the origin inverse germ is bounded by the first
adjacent critical images. The landing premise in Loop 17 is now discharged by the actual radial
limit. -/
theorem deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent_unconditional
    {V : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hV : AnalyticOnNhd ℂ V (ball 0 R))
    (hlocal : V =ᶠ[𝓝 0] deBruijnNewmanPolymathBoydComplexSaddleLocalInverse) :
    R ≤ 2 * Real.sqrt Real.pi := by
  by_contra hnot
  have hradius : 2 * Real.sqrt Real.pi < R := lt_of_not_ge hnot
  have hsub : deBruijnNewmanPolymathBoydOpenCoordinateDisk ⊆ ball (0 : ℂ) R := by
    intro z hz
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk, mem_ball, dist_zero_right] at hz
    rw [mem_ball, dist_zero_right]
    exact hz.trans hradius
  have hVon : AnalyticOnNhd ℂ V deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    fun z hz => hV z (hsub hz)
  have hevent : V =ᶠ[𝓝 0]
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse :=
    hlocal.trans
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local.symm
  have heqOn : EqOn V deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    apply hVon.eqOn_of_preconnected_of_eventuallyEq
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticOnNhd
    · rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
      exact (convex_ball (0 : ℂ) (2 * Real.sqrt Real.pi)).isPreconnected
    · exact deBruijnNewmanPolymathBoydOpenCoordinateDiskZero.property
    · exact hevent
  have hpos : ∀ᶠ t : ℝ in 𝓝[Iio (2 * Real.pi)] (2 * Real.pi), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  have heqPath :
      (fun t : ℝ => V (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) =ᶠ[
          𝓝[Iio (2 * Real.pi)] (2 * Real.pi)]
      (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) := by
    filter_upwards [eventually_mem_nhdsWithin, hpos] with t ht htp
    exact heqOn
      (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_one_mem_coordinateDisk htp.le ht)
  have hlandingV : Tendsto
      (fun t : ℝ => V (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t))
      (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint 1)) :=
    Tendsto.congr' heqPath.symm
      tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper
  have hc_mem : deBruijnNewmanPolymathBoydComplexSaddleImage 1 ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right,
      norm_deBruijnNewmanPolymathBoydComplexSaddleImage_one]
    exact hradius
  have hray : Tendsto (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1)
      (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddleImage 1)) := by
    have hfull : ContinuousAt (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1)
        (2 * Real.pi) :=
      (continuous_deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1).continuousAt
    change Tendsto (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1)
      (𝓝 (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 (2 * Real.pi))) at hfull
    rw [deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay_two_pi] at hfull
    exact hfull.mono_left inf_le_left
  have hlandingContinuous : Tendsto
      (fun t : ℝ => V (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t))
      (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (V (deBruijnNewmanPolymathBoydComplexSaddleImage 1))) := by
    exact Filter.Tendsto.comp (hV _ hc_mem).continuousAt hray
  have hlands : V (deBruijnNewmanPolymathBoydComplexSaddleImage 1) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint 1 :=
    tendsto_nhds_unique hlandingContinuous hlandingV
  have hbound := deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent
    (n := (1 : ℤ)) (Or.inl rfl) hR hV hlocal hlands
  exact (not_le_of_gt hradius) hbound

/-- Aggregate certificate for the actual inverse Jacobian, both adjacent landings, and the exact
maximal centered continuation radius. -/
theorem deBruijnNewmanPolymathBoydAdjacentLandingJacobianCertificate :
    AnalyticOnNhd ℂ deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
      (∀ w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        deBruijnNewmanPolymathBoydComplexSaddlePhase
            (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) = w ^ 2 / 2) ∧
      deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse 0 = 1 ∧
      Tendsto
        (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t))
        (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
        (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint 1)) ∧
      Tendsto
        (fun t : ℝ => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t))
        (𝓝[Iio (2 * Real.pi)] (2 * Real.pi))
        (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint (-1))) ∧
      (∀ {V : ℂ → ℂ} {R : ℝ}, 0 < R → AnalyticOnNhd ℂ V (ball 0 R) →
        V =ᶠ[𝓝 0] deBruijnNewmanPolymathBoydComplexSaddleLocalInverse →
        R ≤ 2 * Real.sqrt Real.pi) := by
  exact ⟨
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticOnNhd,
    fun _ hw => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_phase hw,
    deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
    tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper,
    tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower,
    (by
      intro V R hR hV hlocal
      exact deBruijnNewmanPolymathBoydOriginInverseBranch_radius_le_adjacent_unconditional
        (V := V) (R := R) hR hV hlocal)⟩

end

end LeanLab.Riemann
