import LeanLab.Riemann.DeBruijnNewmanPolymathBoydR2JacobianRemainder

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Adjacent Puiseux sheets and inverse-Jacobian jump for Boyd's Gamma saddle

This module translates the actual normalized inverse germ to the first adjacent saddles.  The
translation exposes the two local sheets, their phase-Jacobians, and the leading coefficient of
their jump.  It then identifies the sheet selected by the actual upper and lower Boyd contours.
-/

namespace LeanLab.Riemann

open Complex Filter Metric Set
open scoped Topology

noncomputable section

/-- The positive local uniformizer sheet translated to the integer saddle `n`. -/
def deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus (n : ℤ) (eta : ℂ) : ℂ :=
  deBruijnNewmanPolymathBoydComplexSaddlePoint n +
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta

/-- The companion local sheet, obtained by reversing the uniformizer. -/
def deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus (n : ℤ) (eta : ℂ) : ℂ :=
  deBruijnNewmanPolymathBoydComplexSaddlePoint n +
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)

/-- The positive-sheet derivative with respect to the translated phase. -/
def deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus (eta : ℂ) : ℂ :=
  deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta / eta

/-- The negative-sheet derivative with respect to the translated phase. -/
def deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus (eta : ℂ) : ℂ :=
  -deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta) / eta

/-- Translation by an integer saddle adds the corresponding critical phase value. -/
theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_add_saddle
    (n : ℤ) (v : ℂ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydComplexSaddlePoint n + v) =
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) +
        deBruijnNewmanPolymathBoydComplexSaddlePhase v := by
  rw [deBruijnNewmanPolymathBoydComplexSaddlePhase,
    deBruijnNewmanPolymathBoydComplexSaddlePhase,
    deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_add,
    deBruijnNewmanPolymathBoydComplexSaddlePoint_exp]
  ring

/-- The positive adjacent sheet is analytic on the complete natural coordinate disk. -/
theorem deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus_analyticOnNhd (n : ℤ) :
    AnalyticOnNhd ℂ (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n)
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  intro eta heta
  exact analyticAt_const.add
    (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt heta)

/-- Negation preserves the natural coordinate disk. -/
theorem neg_mem_deBruijnNewmanPolymathBoydOpenCoordinateDisk
    {eta : ℂ} (heta : eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    -eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  simpa [deBruijnNewmanPolymathBoydOpenCoordinateDisk] using heta

/-- The negative adjacent sheet is analytic on the complete natural coordinate disk. -/
theorem deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus_analyticOnNhd (n : ℤ) :
    AnalyticOnNhd ℂ (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n)
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  intro eta heta
  have hU := deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt
    (neg_mem_deBruijnNewmanPolymathBoydOpenCoordinateDisk heta)
  exact analyticAt_const.add (hU.comp analyticAt_id.neg)

/-- Both translated sheets solve the same exact phase equation. -/
theorem deBruijnNewmanPolymathBoydAdjacentPuiseux_phase
    (n : ℤ) {eta : ℂ}
    (heta : eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n eta) =
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2 ∧
      deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n eta) =
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2 := by
  constructor
  · rw [deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus,
      deBruijnNewmanPolymathBoydComplexSaddlePhase_add_saddle,
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_phase heta]
  · rw [deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus,
      deBruijnNewmanPolymathBoydComplexSaddlePhase_add_saddle,
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_phase
        (neg_mem_deBruijnNewmanPolymathBoydOpenCoordinateDisk heta)]
    ring

/-- Reversing the uniformizer exchanges the two adjacent sheets. -/
theorem deBruijnNewmanPolymathBoydAdjacentPuiseux_involution
    (n : ℤ) (eta : ℂ) :
    deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n (-eta) =
        deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n eta ∧
      deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n (-eta) =
        deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n eta := by
  simp [deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus,
    deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus]

/-- Exact uniformizer derivative of the positive sheet. -/
theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus
    (n : ℤ) {eta : ℂ}
    (heta : eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    HasDerivAt (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n)
      (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta) eta := by
  exact (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt
    heta).differentiableAt.hasDerivAt.const_add
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n)

/-- Exact uniformizer derivative of the negative sheet. -/
theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus
    (n : ℤ) {eta : ℂ}
    (heta : eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    HasDerivAt (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n)
      (-deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)) eta := by
  unfold deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus
  simpa only [Function.comp_apply, mul_neg, mul_one] using
    ((deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt
      (neg_mem_deBruijnNewmanPolymathBoydOpenCoordinateDisk heta)).differentiableAt.hasDerivAt.comp
        eta (hasDerivAt_neg' eta)).const_add
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n)

/-- The translated phase has uniformizer derivative `eta`. -/
theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentTranslatedPhase
    (n : ℤ) (eta : ℂ) :
    HasDerivAt
      (fun z : ℂ =>
        deBruijnNewmanPolymathBoydComplexSaddlePhase
            (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + z ^ 2 / 2)
      eta eta := by
  have hraw := (((hasDerivAt_id eta).pow 2).div_const 2).const_add
    (deBruijnNewmanPolymathBoydComplexSaddlePhase
      (deBruijnNewmanPolymathBoydComplexSaddlePoint n))
  convert hraw using 1 <;> try rfl
  simp

/-- On the punctured disk, both quotients are the exact phase-Jacobians in chain-rule form. -/
theorem deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_chainRule
    (n : ℤ) {eta : ℂ}
    (heta : eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) (heta0 : eta ≠ 0) :
    HasDerivAt (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n)
        (eta * deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta) eta ∧
      HasDerivAt (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n)
        (eta * deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta) eta ∧
      HasDerivAt
        (fun z : ℂ =>
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + z ^ 2 / 2)
        eta eta := by
  have hplus := hasDerivAt_deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n heta
  have hminus := hasDerivAt_deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n heta
  constructor
  · convert hplus using 1
    exact mul_div_cancel₀ _ heta0
  · constructor
    · convert hminus using 1
      exact mul_div_cancel₀ _ heta0
    · exact hasDerivAt_deBruijnNewmanPolymathBoydAdjacentTranslatedPhase n eta

/-- Exact algebraic jump of the two phase-Jacobians. -/
theorem deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_jump
    {eta : ℂ} (_heta : eta ≠ 0) :
    deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
        deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta =
      (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)) / eta := by
  simp [deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus,
    deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus]
  ring

/-- Multiplication by the uniformizer removes the exact simple pole in the jump. -/
theorem deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_regularizedJump
    {eta : ℂ} (heta : eta ≠ 0) :
    eta * (deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
        deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta) =
      deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta) := by
  rw [deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_jump heta]
  exact mul_div_cancel₀ _ heta

/-- The regularized adjacent-sheet jump has source-normalized leading coefficient two. -/
theorem tendsto_deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_regularizedJump :
    Tendsto
      (fun eta : ℂ => eta *
        (deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
          deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta))
      (nhdsWithin 0 {0}ᶜ) (nhds 2) := by
  have hzero : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskZero.property
  have hcontinuous : ContinuousAt
      (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse) 0 :=
    (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hzero).deriv.continuousAt
  have hnegative : ContinuousAt
      (fun eta : ℂ =>
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta))
      0 := by
    have hneg : ContinuousAt (fun eta : ℂ => -eta) 0 := continuousAt_id.neg
    simpa [Function.comp_def] using hcontinuous.comp_of_eq hneg (by simp)
  have hsum := hcontinuous.add hnegative
  change ContinuousAt
    (fun eta : ℂ =>
      deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)) 0 at hsum
  have hsource : nhdsWithin (0 : ℂ) ({0} : Set ℂ)ᶜ ≤ nhds 0 := inf_le_left
  have hsum' : Tendsto
      (fun eta : ℂ =>
        deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
          deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta))
      (nhdsWithin 0 {0}ᶜ) (nhds 2) := by
    simpa only [deriv_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero,
      neg_zero, one_add_one_eq_two] using hsum.tendsto.mono_left hsource
  apply Tendsto.congr' _ hsum'
  filter_upwards [eventually_mem_nhdsWithin] with eta heta
  exact (deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_regularizedJump heta).symm

/-- The actual upper origin branch, translated back from the first positive saddle. -/
def deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint (t : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
      (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) -
    deBruijnNewmanPolymathBoydComplexSaddlePoint 1

/-- The actual lower origin branch, translated back from the first negative saddle. -/
def deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint (t : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
      (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) -
    deBruijnNewmanPolymathBoydComplexSaddlePoint (-1)

/-- The local uniformizer selected by the actual upper radial branch. -/
def deBruijnNewmanPolymathBoydAdjacentUpperUniformizer (t : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
    (deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint t)

/-- The local uniformizer selected by the actual lower radial branch. -/
def deBruijnNewmanPolymathBoydAdjacentLowerUniformizer (t : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
    (deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint t)

/-- The translated actual upper branch lands at the origin. -/
theorem tendsto_deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint :
    Tendsto deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0) := by
  have hconst : Tendsto
      (fun _ : ℝ => deBruijnNewmanPolymathBoydComplexSaddlePoint 1)
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)))
      (nhds (deBruijnNewmanPolymathBoydComplexSaddlePoint 1)) := tendsto_const_nhds
  have h :=
    tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper.sub hconst
  change Tendsto
    (fun t : ℝ =>
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) -
        deBruijnNewmanPolymathBoydComplexSaddlePoint 1)
    (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0)
  simpa using h

/-- The translated actual lower branch lands at the origin. -/
theorem tendsto_deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint :
    Tendsto deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0) := by
  have hconst : Tendsto
      (fun _ : ℝ => deBruijnNewmanPolymathBoydComplexSaddlePoint (-1))
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)))
      (nhds (deBruijnNewmanPolymathBoydComplexSaddlePoint (-1))) := tendsto_const_nhds
  have h :=
    tendsto_deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower.sub hconst
  change Tendsto
    (fun t : ℝ =>
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) -
        deBruijnNewmanPolymathBoydComplexSaddlePoint (-1))
    (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0)
  simpa using h

/-- Near the upper endpoint, the translated actual branch lies in the origin phase domain. -/
theorem deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint_eventually_mem_originPhaseDomain :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint t ∈
        deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  exact tendsto_deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint
    (isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain.mem_nhds
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero.property)

/-- Near the lower endpoint, the translated actual branch lies in the origin phase domain. -/
theorem deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint_eventually_mem_originPhaseDomain :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint t ∈
        deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  exact tendsto_deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint
    (isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain.mem_nhds
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero.property)

/-- The actual inverse is also a left inverse to the global coordinate on the origin domain. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_globalSaddleCoordinate
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u) = u := by
  let uD : deBruijnNewmanPolymathBoydOriginPhaseDomain := ⟨u, hu⟩
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph uD
  have hinverse :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm_apply_apply uD
  calc
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
        (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u) =
        (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm wD : ℂ) := by
      exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_apply wD
    _ = u := congrArg Subtype.val hinverse

/-- The actual upper uniformizer tends to the adjacent branch value zero. -/
theorem tendsto_deBruijnNewmanPolymathBoydAdjacentUpperUniformizer :
    Tendsto deBruijnNewmanPolymathBoydAdjacentUpperUniformizer
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0) := by
  have hcoordinate : ContinuousAt
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate 0 :=
    (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero.property.1).continuousAt
  have h := hcoordinate.tendsto.comp
    tendsto_deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint
  change Tendsto
    (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate ∘
      deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint)
    (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0)
  simpa only [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero] using h

/-- The actual lower uniformizer tends to the adjacent branch value zero. -/
theorem tendsto_deBruijnNewmanPolymathBoydAdjacentLowerUniformizer :
    Tendsto deBruijnNewmanPolymathBoydAdjacentLowerUniformizer
      (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0) := by
  have hcoordinate : ContinuousAt
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate 0 :=
    (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero.property.1).continuousAt
  have h := hcoordinate.tendsto.comp
    tendsto_deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint
  change Tendsto
    (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate ∘
      deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint)
    (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0)
  simpa only [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero] using h

/-- Near the upper endpoint, the actual uniformizer lies in the natural coordinate disk. -/
theorem deBruijnNewmanPolymathBoydAdjacentUpperUniformizer_eventually_mem_coordinateDisk :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t ∈
        deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  filter_upwards [
    deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint_eventually_mem_originPhaseDomain]
      with t ht
  exact (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain
    ⟨deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint t, ht⟩).property

/-- Near the lower endpoint, the actual uniformizer lies in the natural coordinate disk. -/
theorem deBruijnNewmanPolymathBoydAdjacentLowerUniformizer_eventually_mem_coordinateDisk :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t ∈
        deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  filter_upwards [
    deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint_eventually_mem_originPhaseDomain]
      with t ht
  exact (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain
    ⟨deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint t, ht⟩).property

/-- The actual upper Loop 24 branch is the positive Puiseux sheet; the negative sheet has the
same phase and is its certified local companion. -/
theorem deBruijnNewmanPolymathBoydAdjacentUpper_actualSheets_eventually :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint t ∈
          deBruijnNewmanPolymathBoydOriginPhaseDomain ∧
        deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t ∈
          deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
        deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
          deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus 1
            (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t) ∧
        deBruijnNewmanPolymathBoydComplexSaddlePhase
            (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus 1
              (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t)) =
          deBruijnNewmanPolymathBoydComplexSaddlePhase
            (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
              (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) ∧
        deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
          deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t) := by
  have hpos : ∀ᶠ t : ℝ in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  filter_upwards [
      deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint_eventually_mem_originPhaseDomain,
      deBruijnNewmanPolymathBoydAdjacentUpperUniformizer_eventually_mem_coordinateDisk,
      eventually_mem_nhdsWithin, hpos]
    with t htranslated heta ht htp
  have hinverse :
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t) =
        deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint t := by
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_globalSaddleCoordinate
      htranslated
  have hplus :
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
        deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus 1
          (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t) := by
    rw [deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus, hinverse]
    unfold deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint
    ring
  have hcompanion :
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus 1
            (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t)) =
        deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) := by
    have hphase := deBruijnNewmanPolymathBoydAdjacentPuiseux_phase 1 heta
    calc
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus 1
            (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t)) =
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydComplexSaddlePoint 1) +
            deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t ^ 2 / 2 := hphase.2
      _ = deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus 1
            (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t)) := hphase.1.symm
      _ = deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) :=
        congrArg deBruijnNewmanPolymathBoydComplexSaddlePhase hplus.symm
  exact ⟨htranslated, heta, hplus, hcompanion,
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_upper htp.le ht⟩

/-- The actual lower Loop 24 branch is the positive Puiseux sheet at the negative saddle; the
negative uniformizer value is its certified local companion. -/
theorem deBruijnNewmanPolymathBoydAdjacentLower_actualSheets_eventually :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint t ∈
          deBruijnNewmanPolymathBoydOriginPhaseDomain ∧
        deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t ∈
          deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
        deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
          deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus (-1)
            (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t) ∧
        deBruijnNewmanPolymathBoydComplexSaddlePhase
            (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus (-1)
              (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t)) =
          deBruijnNewmanPolymathBoydComplexSaddlePhase
            (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
              (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t)) ∧
        deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
          deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t := by
  have hpos : ∀ᶠ t : ℝ in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  filter_upwards [
      deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint_eventually_mem_originPhaseDomain,
      deBruijnNewmanPolymathBoydAdjacentLowerUniformizer_eventually_mem_coordinateDisk,
      eventually_mem_nhdsWithin, hpos]
    with t htranslated heta ht htp
  have hinverse :
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t) =
        deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint t := by
    exact deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_globalSaddleCoordinate
      htranslated
  have hplus :
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
        deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus (-1)
          (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t) := by
    rw [deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus, hinverse]
    unfold deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint
    ring
  have hcompanion :
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus (-1)
            (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t)) =
        deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t)) := by
    have hphase := deBruijnNewmanPolymathBoydAdjacentPuiseux_phase (-1) heta
    calc
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus (-1)
            (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t)) =
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydComplexSaddlePoint (-1)) +
            deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t ^ 2 / 2 := hphase.2
      _ = deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus (-1)
            (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t)) := hphase.1.symm
      _ = deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
            (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t)) :=
        congrArg deBruijnNewmanPolymathBoydComplexSaddlePhase hplus.symm
  exact ⟨htranslated, heta, hplus, hcompanion,
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_radialRay_lower htp.le ht⟩

/-- The positive first adjacent saddle is outside the open origin phase domain. -/
theorem deBruijnNewmanPolymathBoydComplexSaddlePoint_one_not_mem_originPhaseDomain :
    deBruijnNewmanPolymathBoydComplexSaddlePoint 1 ∉
      deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  intro hmem
  have him := hmem.1
  change |(deBruijnNewmanPolymathBoydComplexSaddlePoint 1).im| < 2 * Real.pi at him
  norm_num [deBruijnNewmanPolymathBoydComplexSaddlePoint, abs_of_pos Real.pi_pos] at him

/-- The negative first adjacent saddle is outside the open origin phase domain. -/
theorem deBruijnNewmanPolymathBoydComplexSaddlePoint_neg_one_not_mem_originPhaseDomain :
    deBruijnNewmanPolymathBoydComplexSaddlePoint (-1) ∉
      deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  intro hmem
  have him := hmem.1
  change |(deBruijnNewmanPolymathBoydComplexSaddlePoint (-1)).im| < 2 * Real.pi at him
  norm_num [deBruijnNewmanPolymathBoydComplexSaddlePoint, abs_of_pos Real.pi_pos] at him

/-- The uniformizer selected by the actual upper branch is punctured before the endpoint. -/
theorem deBruijnNewmanPolymathBoydAdjacentUpperUniformizer_eventually_ne_zero :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t ≠ 0 := by
  have hpos : ∀ᶠ t : ℝ in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  filter_upwards [deBruijnNewmanPolymathBoydAdjacentUpper_actualSheets_eventually,
      eventually_mem_nhdsWithin, hpos]
    with t hsheets ht htp
  intro heta0
  have hactual :
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
        deBruijnNewmanPolymathBoydComplexSaddlePoint 1 := by
    rw [hsheets.2.2.1, heta0]
    simp [deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus,
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero]
  have hcontour :
      deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t) =
        deBruijnNewmanPolymathBoydComplexSaddlePoint 1 :=
    hsheets.2.2.2.2.symm.trans hactual
  apply deBruijnNewmanPolymathBoydComplexSaddlePoint_one_not_mem_originPhaseDomain
  rw [← hcontour]
  exact deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_mem_originPhaseDomain
    htp.le ht

/-- The uniformizer selected by the actual lower branch is punctured before the endpoint. -/
theorem deBruijnNewmanPolymathBoydAdjacentLowerUniformizer_eventually_ne_zero :
    ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
      deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t ≠ 0 := by
  have hpos : ∀ᶠ t : ℝ in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)), 0 < t :=
    (eventually_gt_nhds (by positivity : (0 : ℝ) < 2 * Real.pi)).filter_mono inf_le_left
  filter_upwards [deBruijnNewmanPolymathBoydAdjacentLower_actualSheets_eventually,
      eventually_mem_nhdsWithin, hpos]
    with t hsheets ht htp
  intro heta0
  have hactual :
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
          (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
        deBruijnNewmanPolymathBoydComplexSaddlePoint (-1) := by
    rw [hsheets.2.2.1, heta0]
    simp [deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus,
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_zero]
  have hcontour :
      deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t =
        deBruijnNewmanPolymathBoydComplexSaddlePoint (-1) :=
    hsheets.2.2.2.2.symm.trans hactual
  apply deBruijnNewmanPolymathBoydComplexSaddlePoint_neg_one_not_mem_originPhaseDomain
  rw [← hcontour]
  exact deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_mem_originPhaseDomain
    htp.le ht

/-- Exact aggregate proposition for both first adjacent Puiseux sheets, their phase-Jacobian jump,
and the actual upper and lower Loop 24 sheet selections. -/
def deBruijnNewmanPolymathBoydAdjacentPuiseuxJumpCertificateStatement : Prop :=
    (∀ n : ℤ, n = 1 ∨ n = -1 →
      AnalyticOnNhd ℂ (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n)
          deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
        AnalyticOnNhd ℂ (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n)
          deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
        ∀ {eta : ℂ}, eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk →
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n eta) =
                deBruijnNewmanPolymathBoydComplexSaddlePhase
                    (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2 ∧
            deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n eta) =
                deBruijnNewmanPolymathBoydComplexSaddlePhase
                    (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2) ∧
      (∀ n : ℤ, ∀ eta : ℂ,
        deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n (-eta) =
            deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n eta ∧
          deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n (-eta) =
            deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n eta) ∧
      (∀ n : ℤ, n = 1 ∨ n = -1 → ∀ {eta : ℂ},
        eta ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk → eta ≠ 0 →
          HasDerivAt (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n)
              (eta * deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta) eta ∧
            HasDerivAt (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n)
              (eta * deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta) eta ∧
            HasDerivAt
              (fun z : ℂ =>
                deBruijnNewmanPolymathBoydComplexSaddlePhase
                    (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + z ^ 2 / 2)
              eta eta) ∧
      (∀ {eta : ℂ}, eta ≠ 0 →
        deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
              deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta =
            (deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
              deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)) / eta ∧
          eta * (deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
              deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta) =
            deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse eta +
              deriv deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (-eta)) ∧
      Tendsto
        (fun eta : ℂ => eta *
          (deBruijnNewmanPolymathBoydAdjacentPhaseJacobianPlus eta -
            deBruijnNewmanPolymathBoydAdjacentPhaseJacobianMinus eta))
        (nhdsWithin 0 {0}ᶜ) (nhds 2) ∧
      (Tendsto deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint
          (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0) ∧
        Tendsto deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint
          (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0)) ∧
      (Tendsto deBruijnNewmanPolymathBoydAdjacentUpperUniformizer
          (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0) ∧
        Tendsto deBruijnNewmanPolymathBoydAdjacentLowerUniformizer
          (nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi))) (nhds 0)) ∧
      (∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
        deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint t ∈
            deBruijnNewmanPolymathBoydOriginPhaseDomain ∧
          deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t ∈
            deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
          deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
              (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
            deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus 1
              (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t) ∧
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus 1
                (deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t)) =
            deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
                (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t)) ∧
          deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
              (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay 1 t) =
            deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-t)) ∧
      (∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
        deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint t ∈
            deBruijnNewmanPolymathBoydOriginPhaseDomain ∧
          deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t ∈
            deBruijnNewmanPolymathBoydOpenCoordinateDisk ∧
          deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
              (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
            deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus (-1)
              (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t) ∧
          deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus (-1)
                (deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t)) =
            deBruijnNewmanPolymathBoydComplexSaddlePhase
              (deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
                (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t)) ∧
          deBruijnNewmanPolymathBoydNormalizedCoordinateInverse
              (deBruijnNewmanPolymathBoydAdjacentSaddleRadialRay (-1) t) =
            deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift t) ∧
      (∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
          deBruijnNewmanPolymathBoydAdjacentUpperUniformizer t ≠ 0) ∧
        ∀ᶠ t in nhdsWithin (2 * Real.pi) (Iio (2 * Real.pi)),
          deBruijnNewmanPolymathBoydAdjacentLowerUniformizer t ≠ 0

/-- Aggregate certificate for both first adjacent Puiseux sheets, their phase-Jacobian jump, and
the actual upper and lower Loop 24 sheet selections. -/
theorem deBruijnNewmanPolymathBoydAdjacentPuiseuxJumpCertificate :
    deBruijnNewmanPolymathBoydAdjacentPuiseuxJumpCertificateStatement := by
  unfold deBruijnNewmanPolymathBoydAdjacentPuiseuxJumpCertificateStatement
  refine ⟨?_, ?_, ?_, ?_,
    tendsto_deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_regularizedJump,
    ⟨tendsto_deBruijnNewmanPolymathBoydAdjacentUpperTranslatedPoint,
      tendsto_deBruijnNewmanPolymathBoydAdjacentLowerTranslatedPoint⟩,
    ⟨tendsto_deBruijnNewmanPolymathBoydAdjacentUpperUniformizer,
      tendsto_deBruijnNewmanPolymathBoydAdjacentLowerUniformizer⟩,
    deBruijnNewmanPolymathBoydAdjacentUpper_actualSheets_eventually,
    deBruijnNewmanPolymathBoydAdjacentLower_actualSheets_eventually,
    deBruijnNewmanPolymathBoydAdjacentUpperUniformizer_eventually_ne_zero,
    deBruijnNewmanPolymathBoydAdjacentLowerUniformizer_eventually_ne_zero⟩
  · intro n _
    refine ⟨deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus_analyticOnNhd n,
      deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus_analyticOnNhd n,
      ?_⟩
    intro eta heta
    exact deBruijnNewmanPolymathBoydAdjacentPuiseux_phase n heta
  · exact deBruijnNewmanPolymathBoydAdjacentPuiseux_involution
  · intro n _ eta heta heta0
    exact deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_chainRule n heta heta0
  · intro eta heta0
    exact ⟨deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_jump heta0,
      deBruijnNewmanPolymathBoydAdjacentPhaseJacobian_regularizedJump heta0⟩

/-- The coordinate-plane radicand centered at the critical image of saddle `n`. -/
def deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand (n : ℤ) (w : ℂ) : ℂ :=
  w ^ 2 - deBruijnNewmanPolymathBoydComplexSaddleImage n ^ 2

/-- Principal slit-plane uniformizer for the adjacent saddle chart. -/
def deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer (n : ℤ) (w : ℂ) : ℂ :=
  Complex.sqrt (deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand n w)

/-- Positive principal-sheet continuation candidate in the original coordinate variable. -/
def deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationPlus (n : ℤ) (w : ℂ) : ℂ :=
  deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus n
    (deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer n w)

/-- Negative principal-sheet continuation candidate in the original coordinate variable. -/
def deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationMinus (n : ℤ) (w : ℂ) : ℂ :=
  deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus n
    (deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer n w)

/-- The principal complex square root squares to its argument. -/
theorem deBruijnNewmanPolymathBoyd_principalSqrt_sq (z : ℂ) :
    Complex.sqrt z ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul]
  ring_nf
  exact Complex.exp_log hz

/-- On the principal slit and while the adjacent uniformizer remains in the natural disk, both
coordinate-plane continuation candidates are analytic. -/
theorem deBruijnNewmanPolymathBoydAdjacentPrincipalContinuations_analyticAt
    {n : ℤ} {w : ℂ}
    (hslit : deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand n w ∈
      Complex.slitPlane)
    (hdisk : deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer n w ∈
      deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    AnalyticAt ℂ (deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationPlus n) w ∧
      AnalyticAt ℂ (deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationMinus n) w := by
  have hradicand : AnalyticAt ℂ
      (deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand n) w := by
    unfold deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand
    exact (analyticAt_id.pow 2).sub analyticAt_const
  have hsqrt : AnalyticAt ℂ Complex.sqrt
      (deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand n w) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds hslit)
  have huniformizer : AnalyticAt ℂ
      (deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer n) w := by
    unfold deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer
    exact hsqrt.comp hradicand
  constructor
  · exact (deBruijnNewmanPolymathBoydAdjacentPuiseuxPlus_analyticOnNhd n _ hdisk).comp
      huniformizer
  · exact (deBruijnNewmanPolymathBoydAdjacentPuiseuxMinus_analyticOnNhd n _ hdisk).comp
      huniformizer

/-- Both principal continuation candidates solve the original coordinate phase equation. -/
theorem deBruijnNewmanPolymathBoydAdjacentPrincipalContinuations_phase
    (n : ℤ) {w : ℂ}
    (hdisk : deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer n w ∈
      deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationPlus n w) = w ^ 2 / 2 ∧
      deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationMinus n w) = w ^ 2 / 2 := by
  let eta := deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer n w
  have hphase := deBruijnNewmanPolymathBoydAdjacentPuiseux_phase n hdisk
  have heta_sq : eta ^ 2 =
      deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand n w := by
    exact deBruijnNewmanPolymathBoyd_principalSqrt_sq _
  have hcritical :
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) =
        deBruijnNewmanPolymathBoydComplexSaddleImage n ^ 2 / 2 := by
    rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_saddle,
      deBruijnNewmanPolymathBoydComplexSaddleImage,
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq_saddle]
    ring
  have hvalue :
      deBruijnNewmanPolymathBoydComplexSaddlePhase
          (deBruijnNewmanPolymathBoydComplexSaddlePoint n) + eta ^ 2 / 2 =
        w ^ 2 / 2 := by
    rw [hcritical, heta_sq]
    unfold deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand
    ring
  constructor
  · rw [deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationPlus]
    exact hphase.1.trans hvalue
  · rw [deBruijnNewmanPolymathBoydAdjacentPrincipalContinuationMinus]
    exact hphase.2.trans hvalue

/-- The positive adjacent principal chart meets the origin coordinate exactly on the boundary of
the available uniformizer disk. -/
theorem norm_deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer_one_zero :
    ‖deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer 1 0‖ =
      2 * Real.sqrt Real.pi := by
  have hsquare := congrArg norm <|
    deBruijnNewmanPolymathBoyd_principalSqrt_sq
      (deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand 1 0)
  have hradicand :
      ‖deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand 1 0‖ = 4 * Real.pi := by
    rw [deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand,
      show (0 : ℂ) ^ 2 = 0 by norm_num, zero_sub,
      norm_neg, norm_pow, norm_deBruijnNewmanPolymathBoydComplexSaddleImage_one,
      mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  rw [norm_pow, hradicand] at hsquare
  change ‖deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer 1 0‖ ^ 2 =
    4 * Real.pi at hsquare
  have hnonneg : 0 ≤ ‖deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer 1 0‖ :=
    norm_nonneg _
  have hsqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.sqrt_nonneg Real.pi]

/-- The negative adjacent principal chart has the same exact boundary contact at the origin
coordinate. -/
theorem norm_deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer_neg_one_zero :
    ‖deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer (-1) 0‖ =
      2 * Real.sqrt Real.pi := by
  have hsquare := congrArg norm <|
    deBruijnNewmanPolymathBoyd_principalSqrt_sq
      (deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand (-1) 0)
  have hradicand :
      ‖deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand (-1) 0‖ = 4 * Real.pi := by
    rw [deBruijnNewmanPolymathBoydAdjacentCoordinateRadicand,
      show (0 : ℂ) ^ 2 = 0 by norm_num, zero_sub,
      norm_neg, norm_pow, norm_deBruijnNewmanPolymathBoydComplexSaddleImage_neg_one,
      mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  rw [norm_pow, hradicand] at hsquare
  change ‖deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer (-1) 0‖ ^ 2 =
    4 * Real.pi at hsquare
  have hnonneg : 0 ≤ ‖deBruijnNewmanPolymathBoydAdjacentPrincipalUniformizer (-1) 0‖ :=
    norm_nonneg _
  have hsqrt : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.sqrt_nonneg Real.pi]

end

end LeanLab.Riemann
