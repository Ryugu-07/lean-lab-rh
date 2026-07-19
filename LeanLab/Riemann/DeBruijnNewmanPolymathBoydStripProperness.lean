import LeanLab.Riemann.DeBruijnNewmanPolymathBoydCoordinateRays
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Properness of the Boyd phase below its first adjacent critical values

This module proves that the Boyd phase, restricted to the horizontal strip between the first
adjacent saddles and to the first critical-value disk, is a proper map. In particular, inverse
paths over compact subdisks cannot escape to infinity inside the strip.
-/

namespace LeanLab.Riemann

open Complex Metric Set
open scoped Topology

noncomputable section

/-- The open horizontal strip between the first adjacent Boyd saddles. -/
def deBruijnNewmanPolymathBoydOriginPhaseStrip : Set ℂ :=
  {u | |u.im| < 2 * Real.pi}

/-- The part of the first phase-value disk lying over the origin strip. -/
def deBruijnNewmanPolymathBoydOriginPhaseDomain : Set ℂ :=
  {u | |u.im| < 2 * Real.pi ∧
    ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ < 2 * Real.pi}

/-- The phase-value disk bounded by the first adjacent critical values. -/
def deBruijnNewmanPolymathBoydOpenPhaseDisk : Set ℂ :=
  ball 0 (2 * Real.pi)

/-- The Boyd phase as a map from the origin strip component candidate to its first value disk. -/
def deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    deBruijnNewmanPolymathBoydOriginPhaseDomain →
      deBruijnNewmanPolymathBoydOpenPhaseDisk :=
  fun u => ⟨deBruijnNewmanPolymathBoydComplexSaddlePhase u, by
    rw [deBruijnNewmanPolymathBoydOpenPhaseDisk, mem_ball, dist_zero_right]
    exact u.property.2⟩

theorem continuous_deBruijnNewmanPolymathBoydComplexSaddlePhase :
    Continuous deBruijnNewmanPolymathBoydComplexSaddlePhase := by
  unfold deBruijnNewmanPolymathBoydComplexSaddlePhase
  fun_prop

theorem continuous_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    Continuous deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  apply Continuous.subtype_mk
  exact continuous_deBruijnNewmanPolymathBoydComplexSaddlePhase.comp continuous_subtype_val

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_norm_ge_two_pi_of_abs_im_eq
    {u : ℂ} (hu : |u.im| = 2 * Real.pi) :
    2 * Real.pi ≤ ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ := by
  rcases (abs_eq (by positivity : 0 ≤ 2 * Real.pi)).mp hu with him | him
  · calc
      2 * Real.pi =
          |(deBruijnNewmanPolymathBoydComplexSaddlePhase u).im| := by
            simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_im, him,
              abs_of_pos Real.pi_pos]
      _ ≤ ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ :=
        Complex.abs_im_le_norm _
  · calc
      2 * Real.pi =
          |(deBruijnNewmanPolymathBoydComplexSaddlePhase u).im| := by
            simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_im, him,
              abs_of_pos Real.pi_pos]
      _ ≤ ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ :=
        Complex.abs_im_le_norm _

private theorem deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel_re_lower
    {r : ℝ} (hr : 0 ≤ r) {u : ℂ}
    (hu : |u.im| ≤ 2 * Real.pi ∧
      ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ ≤ r) :
    -r - 2 ≤ u.re := by
  by_cases hx : u.re ≤ 0
  · have hexp : Real.exp u.re ≤ 1 := by
      simpa using Real.exp_le_one_iff.mpr hx
    have hcos : -1 ≤ Real.cos u.im := Real.neg_one_le_cos _
    have hmul : -1 ≤ Real.exp u.re * Real.cos u.im := by
      have hnonneg : 0 ≤ Real.exp u.re := Real.exp_nonneg _
      have h₁ : -(Real.exp u.re) ≤ Real.exp u.re * Real.cos u.im := by
        nlinarith
      linarith
    have hre :
        (deBruijnNewmanPolymathBoydComplexSaddlePhase u).re =
          Real.exp u.re * Real.cos u.im - u.re - 1 := by
      simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_re]
    have hre_le_norm :
        (deBruijnNewmanPolymathBoydComplexSaddlePhase u).re ≤
          ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [hre] at hre_le_norm
    linarith [hu.2]
  · have : 0 ≤ u.re := le_of_not_ge hx
    linarith

private theorem deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel_re_upper
    {r : ℝ} (hr : 0 ≤ r) {u : ℂ}
    (hu : |u.im| ≤ 2 * Real.pi ∧
      ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ ≤ r) :
    u.re ≤ 2 * (r + 2 * Real.pi) + 1 := by
  by_cases hx : 0 ≤ u.re
  · have hphase_add :
        Complex.exp u = deBruijnNewmanPolymathBoydComplexSaddlePhase u + (u + 1) := by
      unfold deBruijnNewmanPolymathBoydComplexSaddlePhase
      ring
    have hexp_norm :
        Real.exp u.re ≤
          ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ + ‖u + 1‖ := by
      rw [← Complex.norm_exp, hphase_add]
      exact norm_add_le _ _
    have hu_add : ‖u + 1‖ ≤ u.re + 1 + |u.im| := by
      calc
        ‖u + 1‖ ≤ |(u + 1).re| + |(u + 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = u.re + 1 + |u.im| := by
          simp [abs_of_nonneg (by linarith : 0 ≤ u.re + 1)]
    have hexp_upper : Real.exp u.re ≤ r + (u.re + 1 + 2 * Real.pi) := by
      linarith [hu.1, hu.2, hu_add]
    have hquad := Real.quadratic_le_exp_of_nonneg hx
    have hsq : u.re ^ 2 ≤ 2 * (r + 2 * Real.pi) := by
      nlinarith
    nlinarith [sq_nonneg (u.re - 1)]
  · have hx' : u.re ≤ 0 := le_of_not_ge hx
    have : 0 ≤ 2 * (r + 2 * Real.pi) + 1 := by positivity
    linarith

theorem isCompact_deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel
    {r : ℝ} (hr : 0 ≤ r) :
    IsCompact {u : ℂ | |u.im| ≤ 2 * Real.pi ∧
      ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ ≤ r} := by
  rw [isCompact_iff_isClosed_bounded]
  constructor
  · exact (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const).inter
      (isClosed_le
        (continuous_norm.comp continuous_deBruijnNewmanPolymathBoydComplexSaddlePhase)
        continuous_const)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨2 * r + 6 * Real.pi + 2, ?_⟩
    intro u hu
    rw [mem_closedBall, dist_zero_right]
    have hlower :=
      deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel_re_lower hr hu
    have hupper :=
      deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel_re_upper hr hu
    have hre_abs : |u.re| ≤ 2 * r + 4 * Real.pi + 2 := by
      rw [abs_le]
      constructor <;> nlinarith [Real.pi_pos.le]
    exact (Complex.norm_le_abs_re_add_abs_im u).trans (by linarith [hu.1])

theorem deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel_subset_originStrip
    {r : ℝ} (hr : r < 2 * Real.pi) :
    {u : ℂ | |u.im| ≤ 2 * Real.pi ∧
      ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ ≤ r} ⊆
      deBruijnNewmanPolymathBoydOriginPhaseStrip := by
  intro u hu
  change |u.im| < 2 * Real.pi
  exact hu.1.lt_of_ne fun him => by
    have hboundary :=
      deBruijnNewmanPolymathBoydComplexSaddlePhase_norm_ge_two_pi_of_abs_im_eq him
    linarith [hu.2]

/-- The ambient closed-strip realization of the inverse image of a target set. -/
def deBruijnNewmanPolymathBoydAmbientPhasePreimage
    (K : Set deBruijnNewmanPolymathBoydOpenPhaseDisk) : Set ℂ :=
  {u | |u.im| ≤ 2 * Real.pi ∧
    deBruijnNewmanPolymathBoydComplexSaddlePhase u ∈
      ((↑) '' K : Set ℂ)}

private theorem isClosed_deBruijnNewmanPolymathBoydAmbientPhasePreimage
    {K : Set deBruijnNewmanPolymathBoydOpenPhaseDisk} (hK : IsCompact K) :
    IsClosed (deBruijnNewmanPolymathBoydAmbientPhasePreimage K) := by
  exact (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const).inter
    ((hK.image continuous_subtype_val).isClosed.preimage
      continuous_deBruijnNewmanPolymathBoydComplexSaddlePhase)

theorem isCompact_deBruijnNewmanPolymathBoydAmbientPhasePreimage
    {K : Set deBruijnNewmanPolymathBoydOpenPhaseDisk} (hK : IsCompact K) :
    IsCompact (deBruijnNewmanPolymathBoydAmbientPhasePreimage K) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp [deBruijnNewmanPolymathBoydAmbientPhasePreimage]
  · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKne
      (continuous_norm.comp continuous_subtype_val).continuousOn
    let r : ℝ := ‖(z : ℂ)‖
    have hr_nonneg : 0 ≤ r := norm_nonneg _
    have hr_lt : r < 2 * Real.pi := by
      have hzmem : (z : ℂ) ∈ ball 0 (2 * Real.pi) := z.property
      have hzdist := mem_ball.mp hzmem
      rw [dist_zero_right] at hzdist
      exact hzdist
    apply (isCompact_deBruijnNewmanPolymathBoyd_closedStripPhaseSublevel hr_nonneg).of_isClosed_subset
      (isClosed_deBruijnNewmanPolymathBoydAmbientPhasePreimage hK)
    intro u hu
    refine ⟨hu.1, ?_⟩
    rcases hu.2 with ⟨w, hwK, hw⟩
    rw [← hw]
    exact hzmax hwK

private theorem deBruijnNewmanPolymathBoyd_coe_image_phasePreimage_eq_ambient
    (K : Set deBruijnNewmanPolymathBoydOpenPhaseDisk) :
    ((↑) : deBruijnNewmanPolymathBoydOriginPhaseDomain → ℂ) ''
        (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' K) =
      deBruijnNewmanPolymathBoydAmbientPhasePreimage K := by
  ext u
  constructor
  · rintro ⟨v, hvK, rfl⟩
    refine ⟨v.property.1.le, ?_⟩
    exact ⟨deBruijnNewmanPolymathBoydPhaseOnOriginDomain v, hvK, rfl⟩
  · intro hu
    rcases hu.2 with ⟨z, hzK, hz⟩
    have hphase_lt :
        ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ < 2 * Real.pi := by
      rw [← hz]
      have hzmem : (z : ℂ) ∈ ball 0 (2 * Real.pi) := z.property
      have hzdist := mem_ball.mp hzmem
      rwa [dist_zero_right] at hzdist
    have him_lt : |u.im| < 2 * Real.pi := hu.1.lt_of_ne fun him => by
      have hboundary :=
        deBruijnNewmanPolymathBoydComplexSaddlePhase_norm_ge_two_pi_of_abs_im_eq him
      linarith
    let v : deBruijnNewmanPolymathBoydOriginPhaseDomain :=
      ⟨u, him_lt, hphase_lt⟩
    refine ⟨v, ?_, rfl⟩
    change deBruijnNewmanPolymathBoydPhaseOnOriginDomain v ∈ K
    have hvz : deBruijnNewmanPolymathBoydPhaseOnOriginDomain v = z := by
      apply Subtype.ext
      exact hz.symm
    rwa [hvz]

theorem isCompact_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain
    {K : Set deBruijnNewmanPolymathBoydOpenPhaseDisk} (hK : IsCompact K) :
    IsCompact (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' K) := by
  rw [Subtype.isCompact_iff,
    deBruijnNewmanPolymathBoyd_coe_image_phasePreimage_eq_ambient]
  exact isCompact_deBruijnNewmanPolymathBoydAmbientPhasePreimage hK

theorem isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    IsProperMap deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  rw [isProperMap_iff_isCompact_preimage]
  exact ⟨continuous_deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
    fun _ hK => isCompact_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain hK⟩

end

end LeanLab.Riemann
