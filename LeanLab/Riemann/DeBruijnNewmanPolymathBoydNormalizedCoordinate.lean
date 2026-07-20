import LeanLab.Riemann.DeBruijnNewmanPolymathBoydBranchedDegreeTwo
import LeanLab.Riemann.AnalyticLogBranch
import Mathlib.Analysis.Complex.CoveringMap

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The global normalized coordinate for the first Boyd phase domain

This module first records the exact no-cut premise for the principal normalized Boyd coordinate.
It then bypasses that premise by constructing a normalized holomorphic square root on the whole
first saddle strip and proves that the resulting coordinate is a global analytic homeomorphism
with an analytic disk inverse extending the previously compiled local germ.
-/

namespace LeanLab.Riemann

open Complex Metric Set
open TopologicalSpace
open scoped Topology

noncomputable section

/-- The natural target disk for the normalized coordinate `w`, where `w^2 / 2` lies in the first
phase disk. -/
def deBruijnNewmanPolymathBoydOpenCoordinateDisk : Set ℂ :=
  ball 0 (2 * Real.sqrt Real.pi)

/-- The origin in the normalized-coordinate disk. -/
def deBruijnNewmanPolymathBoydOpenCoordinateDiskZero :
    deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
  ⟨0, by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk, mem_ball, dist_self]
    positivity⟩

private theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_norm_lt
    {u : ℂ} (hu : ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ < 2 * Real.pi) :
    ‖deBruijnNewmanPolymathBoydComplexSaddleCoordinate u‖ <
      2 * Real.sqrt Real.pi := by
  have hnorm := congrArg norm
    (deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq u)
  rw [norm_div, norm_pow, norm_ofNat] at hnorm
  have hsqrt_sq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hcoord_nonneg : 0 ≤ ‖deBruijnNewmanPolymathBoydComplexSaddleCoordinate u‖ :=
    norm_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  nlinarith

/-- The already defined principal normalized coordinate, restricted to the actual first phase
source and its natural coordinate disk. This definition does not assert global continuity. -/
def deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain :
    deBruijnNewmanPolymathBoydOriginPhaseDomain →
      deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
  fun u => ⟨deBruijnNewmanPolymathBoydComplexSaddleCoordinate u, by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk, mem_ball, dist_zero_right]
    exact deBruijnNewmanPolymathBoydComplexSaddleCoordinate_norm_lt u.property.2⟩

/-- The square map from the normalized-coordinate disk to the first phase disk. -/
def deBruijnNewmanPolymathBoydSquareOnCoordinateDisk :
    deBruijnNewmanPolymathBoydOpenCoordinateDisk →
      deBruijnNewmanPolymathBoydOpenPhaseDisk :=
  fun w => ⟨w ^ 2 / 2, by
    rw [deBruijnNewmanPolymathBoydOpenPhaseDisk, mem_ball, dist_zero_right,
      norm_div, norm_pow, norm_ofNat]
    have hw := w.property
    unfold deBruijnNewmanPolymathBoydOpenCoordinateDisk at hw
    rw [mem_ball, dist_zero_right] at hw
    have hsqrt_sq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
      Real.sq_sqrt Real.pi_pos.le
    have hnorm_nonneg : 0 ≤ ‖(w : ℂ)‖ := norm_nonneg _
    have hsqrt_nonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    nlinarith⟩

@[simp]
theorem deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_zero :
    deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain
        deBruijnNewmanPolymathBoydOriginPhaseDomainZero =
      deBruijnNewmanPolymathBoydOpenCoordinateDiskZero := by
  apply Subtype.ext
  exact deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero

@[simp]
theorem deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_zero :
    deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
        deBruijnNewmanPolymathBoydOpenCoordinateDiskZero =
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero := by
  apply Subtype.ext
  simp [deBruijnNewmanPolymathBoydSquareOnCoordinateDisk,
    deBruijnNewmanPolymathBoydOpenCoordinateDiskZero,
    deBruijnNewmanPolymathBoydOpenPhaseDiskZero]

/-- The normalized coordinate is an algebraic morphism from the Boyd phase to the standard square
map, independently of any global branch-continuity claim. -/
theorem deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_comp_coordinate :
    deBruijnNewmanPolymathBoydSquareOnCoordinateDisk ∘
        deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain =
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  funext u
  apply Subtype.ext
  exact deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq u

theorem deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_of_factor_mem_slitPlane
    {u : ℂ}
    (hslit : deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate u := by
  have hfactor : AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
    by_cases hu : u = 0
    · simpa [hu] using deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_zero
    · exact deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_of_ne hu
  have hsqrt : AnalyticAt ℂ Complex.sqrt
      (deBruijnNewmanPolymathBoydComplexSaddleFactor u) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds hslit)
  unfold deBruijnNewmanPolymathBoydComplexSaddleCoordinate
  unfold deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor
  exact analyticAt_id.mul (hsqrt.comp_of_eq hfactor rfl)

/-- The removable phase factor is analytic at every complex point; the piecewise definition only
records its filled value at the double zero. -/
theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt (u : ℂ) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
  by_cases hu : u = 0
  · simpa [hu] using deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_zero
  · exact deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt_of_ne hu

/-- The removable phase factor never vanishes in the first phase domain. -/
theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_ne_zero_of_mem_originPhaseDomain
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deBruijnNewmanPolymathBoydComplexSaddleFactor u ≠ 0 := by
  by_cases hzero : u = 0
  · simp [hzero]
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor, if_neg hzero]
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact (deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff_of_abs_im_lt_two_pi
        hu.1).not.mpr hzero
  · exact pow_ne_zero 2 hzero

/-- The analytic nonzero factor as an actual map from the phase domain to the punctured complex
plane. -/
def deBruijnNewmanPolymathBoydFactorOnOriginPhaseDomain :
    deBruijnNewmanPolymathBoydOriginPhaseDomain → {z : ℂ // z ≠ 0} :=
  fun u => ⟨deBruijnNewmanPolymathBoydComplexSaddleFactor u,
    deBruijnNewmanPolymathBoydComplexSaddleFactor_ne_zero_of_mem_originPhaseDomain u.property⟩

theorem continuous_deBruijnNewmanPolymathBoydFactorOnOriginPhaseDomain :
    Continuous deBruijnNewmanPolymathBoydFactorOnOriginPhaseDomain := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro u
  exact (deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt u).continuousAt.comp
    continuous_subtype_val.continuousAt

theorem isOpen_deBruijnNewmanPolymathBoydOriginPhaseStrip :
    IsOpen deBruijnNewmanPolymathBoydOriginPhaseStrip := by
  rw [deBruijnNewmanPolymathBoydOriginPhaseStrip]
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem convex_deBruijnNewmanPolymathBoydOriginPhaseStrip :
    Convex ℝ deBruijnNewmanPolymathBoydOriginPhaseStrip := by
  rw [deBruijnNewmanPolymathBoydOriginPhaseStrip]
  have hset : {u : ℂ | |u.im| < 2 * Real.pi} =
      {u : ℂ | -(2 * Real.pi) < u.im} ∩ {u : ℂ | u.im < 2 * Real.pi} := by
    ext u
    simp only [mem_setOf_eq, mem_inter_iff, abs_lt]
  rw [hset]
  exact (convex_halfSpace_im_gt (-(2 * Real.pi))).inter
    (convex_halfSpace_im_lt (2 * Real.pi))

theorem isSimplyConnected_deBruijnNewmanPolymathBoydOriginPhaseStrip :
    IsSimplyConnected deBruijnNewmanPolymathBoydOriginPhaseStrip := by
  letI : ContractibleSpace deBruijnNewmanPolymathBoydOriginPhaseStrip :=
    convex_deBruijnNewmanPolymathBoydOriginPhaseStrip.contractibleSpace
      ⟨0, by
        rw [deBruijnNewmanPolymathBoydOriginPhaseStrip]
        simpa using (show (0 : ℝ) < 2 * Real.pi by positivity)⟩
  change SimplyConnectedSpace deBruijnNewmanPolymathBoydOriginPhaseStrip
  infer_instance

theorem deBruijnNewmanPolymathBoydComplexSaddleFactor_ne_zero_of_mem_originPhaseStrip
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip) :
    deBruijnNewmanPolymathBoydComplexSaddleFactor u ≠ 0 := by
  have hu_im : |u.im| < 2 * Real.pi := hu
  by_cases hzero : u = 0
  · simp [hzero]
  rw [deBruijnNewmanPolymathBoydComplexSaddleFactor, if_neg hzero]
  apply div_ne_zero
  · apply mul_ne_zero
    · norm_num
    · exact (deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff_of_abs_im_lt_two_pi
        hu_im).not.mpr hzero
  · exact pow_ne_zero 2 hzero

/-- The zero-free analytic removable factor has a normalized holomorphic square root on the whole
first saddle strip. -/
theorem exists_deBruijnNewmanPolymathBoydNormalizedSqrtFactor :
    ∃ root : ℂ → ℂ,
      DifferentiableOn ℂ root deBruijnNewmanPolymathBoydOriginPhaseStrip ∧
      root 0 = 1 ∧
      ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip,
        root u ^ 2 = deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
  have hfactor_diff : DifferentiableOn ℂ deBruijnNewmanPolymathBoydComplexSaddleFactor
      deBruijnNewmanPolymathBoydOriginPhaseStrip := by
    intro u _
    exact (deBruijnNewmanPolymathBoydComplexSaddleFactor_analyticAt u).differentiableAt
      |>.differentiableWithinAt
  have hfactor_zero_free :
      0 ∉ deBruijnNewmanPolymathBoydComplexSaddleFactor ''
        deBruijnNewmanPolymathBoydOriginPhaseStrip := by
    rintro ⟨u, hu, hzero⟩
    exact deBruijnNewmanPolymathBoydComplexSaddleFactor_ne_zero_of_mem_originPhaseStrip
      hu hzero
  obtain ⟨logBranch, hlog_diff, hlog_exp, _⟩ :=
    Complex.exists_differentiableOn_eqOn_exp_comp_of_isSimplyConnected
      isSimplyConnected_deBruijnNewmanPolymathBoydOriginPhaseStrip
      isOpen_deBruijnNewmanPolymathBoydOriginPhaseStrip hfactor_diff hfactor_zero_free
  let rawRoot : ℂ → ℂ := fun u => Complex.exp (logBranch u / 2)
  have hraw_diff : DifferentiableOn ℂ rawRoot
      deBruijnNewmanPolymathBoydOriginPhaseStrip := by
    intro u hu
    exact ((hlog_diff u hu).div_const 2).cexp
  have hraw_sq : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip,
      rawRoot u ^ 2 = deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
    intro u hu
    have hexp : Complex.exp (logBranch u) =
        deBruijnNewmanPolymathBoydComplexSaddleFactor u := by
      simpa [Function.comp_apply] using hlog_exp hu
    change Complex.exp (logBranch u / 2) ^ 2 =
      deBruijnNewmanPolymathBoydComplexSaddleFactor u
    rw [← Complex.exp_nat_mul]
    change Complex.exp ((2 : ℂ) * (logBranch u / 2)) =
      deBruijnNewmanPolymathBoydComplexSaddleFactor u
    rw [show (2 : ℂ) * (logBranch u / 2) = logBranch u by ring]
    exact hexp
  let root : ℂ → ℂ := fun u => rawRoot 0 * rawRoot u
  have hzero_mem : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip := by
    rw [deBruijnNewmanPolymathBoydOriginPhaseStrip]
    simpa using (show (0 : ℝ) < 2 * Real.pi by positivity)
  have hraw_zero_sq : rawRoot 0 ^ 2 = 1 := by
    simpa using hraw_sq 0 hzero_mem
  refine ⟨root, ?_, ?_, ?_⟩
  · exact (differentiableOn_const (c := rawRoot 0)).mul hraw_diff
  · change rawRoot 0 * rawRoot 0 = 1
    simpa [pow_two] using hraw_zero_sq
  · intro u hu
    change (rawRoot 0 * rawRoot u) ^ 2 =
      deBruijnNewmanPolymathBoydComplexSaddleFactor u
    rw [mul_pow, hraw_zero_sq, one_mul, hraw_sq u hu]

/-- A canonical choice of the normalized holomorphic square root supplied by the strip theorem. -/
noncomputable def deBruijnNewmanPolymathBoydGlobalSqrtFactor : ℂ → ℂ :=
  Classical.choose exists_deBruijnNewmanPolymathBoydNormalizedSqrtFactor

theorem differentiableOn_deBruijnNewmanPolymathBoydGlobalSqrtFactor :
    DifferentiableOn ℂ deBruijnNewmanPolymathBoydGlobalSqrtFactor
      deBruijnNewmanPolymathBoydOriginPhaseStrip :=
  (Classical.choose_spec exists_deBruijnNewmanPolymathBoydNormalizedSqrtFactor).1

@[simp]
theorem deBruijnNewmanPolymathBoydGlobalSqrtFactor_zero :
    deBruijnNewmanPolymathBoydGlobalSqrtFactor 0 = 1 :=
  (Classical.choose_spec exists_deBruijnNewmanPolymathBoydNormalizedSqrtFactor).2.1

theorem deBruijnNewmanPolymathBoydGlobalSqrtFactor_sq
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip) :
    deBruijnNewmanPolymathBoydGlobalSqrtFactor u ^ 2 =
      deBruijnNewmanPolymathBoydComplexSaddleFactor u :=
  (Classical.choose_spec exists_deBruijnNewmanPolymathBoydNormalizedSqrtFactor).2.2 u hu

theorem deBruijnNewmanPolymathBoydGlobalSqrtFactor_analyticAt
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydGlobalSqrtFactor u :=
  differentiableOn_deBruijnNewmanPolymathBoydGlobalSqrtFactor.analyticAt
    (isOpen_deBruijnNewmanPolymathBoydOriginPhaseStrip.mem_nhds hu)

/-- The globally normalized Boyd coordinate built from the holomorphic strip square root. -/
def deBruijnNewmanPolymathBoydGlobalSaddleCoordinate (u : ℂ) : ℂ :=
  u * deBruijnNewmanPolymathBoydGlobalSqrtFactor u

@[simp]
theorem deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate]

theorem deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_sq
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip) :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u ^ 2 / 2 =
      deBruijnNewmanPolymathBoydComplexSaddlePhase u := by
  rw [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate, mul_pow,
    deBruijnNewmanPolymathBoydGlobalSqrtFactor_sq hu,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_sq_mul_factor]
  ring

theorem deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u := by
  unfold deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
  exact analyticAt_id.mul
    (deBruijnNewmanPolymathBoydGlobalSqrtFactor_analyticAt hu)

@[simp]
theorem deriv_deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero :
    deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate 0 = 1 := by
  have hzero_mem : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip := by
    rw [deBruijnNewmanPolymathBoydOriginPhaseStrip]
    simpa using (show (0 : ℝ) < 2 * Real.pi by positivity)
  unfold deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
  rw [deriv_fun_mul]
  · simp [deriv_id'']
  · fun_prop
  · exact (deBruijnNewmanPolymathBoydGlobalSqrtFactor_analyticAt hzero_mem).differentiableAt

theorem deriv_deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_ne_zero_of_mem_originPhaseDomain
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u ≠ 0 := by
  have hu_strip : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip := hu.1
  by_cases hzero : u = 0
  · simp [hzero]
  have hphase_deriv : deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_ne_zero_of_norm_lt_two_pi
      hzero hu.2
  have hcoordinate : AnalyticAt ℂ deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u :=
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt hu_strip
  have hsquare : HasDerivAt
      (fun z : ℂ => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate z ^ 2 / 2)
      (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u *
        deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u) u := by
    have hraw := (hcoordinate.differentiableAt.hasDerivAt.pow 2).div_const 2
    apply hraw.congr_deriv
    norm_num
    ring
  have hphase : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddlePhase
      (deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u) u :=
    (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt u).differentiableAt.hasDerivAt
  have hnear_strip : ∀ᶠ z in 𝓝 u,
      z ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip :=
    isOpen_deBruijnNewmanPolymathBoydOriginPhaseStrip.mem_nhds hu_strip
  have hmul :
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u *
          deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u =
        deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u :=
    (hphase.unique <| hsquare.congr_of_eventuallyEq <|
      hnear_strip.mono fun z hz =>
        (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_sq hz).symm).symm
  intro hderiv
  apply hphase_deriv
  rw [← hmul, hderiv, mul_zero]

private theorem deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_norm_lt
    {u : ℂ} (hu_strip : u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip)
    (hu_phase : ‖deBruijnNewmanPolymathBoydComplexSaddlePhase u‖ < 2 * Real.pi) :
    ‖deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u‖ <
      2 * Real.sqrt Real.pi := by
  have hnorm := congrArg norm
    (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_sq hu_strip)
  rw [norm_div, norm_pow, norm_ofNat] at hnorm
  have hsqrt_sq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  have hcoord_nonneg : 0 ≤ ‖deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u‖ :=
    norm_nonneg _
  have hsqrt_nonneg : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  nlinarith

/-- The holomorphic normalized coordinate on the actual first phase source. -/
def deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain :
    deBruijnNewmanPolymathBoydOriginPhaseDomain →
      deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
  fun u => ⟨deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u, by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk, mem_ball, dist_zero_right]
    exact deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_norm_lt
      u.property.1 u.property.2⟩

@[simp]
theorem deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain_zero :
    deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain
        deBruijnNewmanPolymathBoydOriginPhaseDomainZero =
      deBruijnNewmanPolymathBoydOpenCoordinateDiskZero := by
  apply Subtype.ext
  exact deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_zero

theorem deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_comp_globalCoordinate :
    deBruijnNewmanPolymathBoydSquareOnCoordinateDisk ∘
        deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain =
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  funext u
  apply Subtype.ext
  exact deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_sq u.property.1

theorem continuous_deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain :
    Continuous deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro u
  exact (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt u.property.1).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- A no-cut certificate on the first phase domain makes the principal normalized coordinate
continuous on the actual source subtype. -/
theorem continuous_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    Continuous deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro u
  exact (deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_of_factor_mem_slitPlane
    (hslit u u.property)).continuousAt.comp continuous_subtype_val.continuousAt

theorem continuous_deBruijnNewmanPolymathBoydSquareOnCoordinateDisk :
    Continuous deBruijnNewmanPolymathBoydSquareOnCoordinateDisk := by
  apply Continuous.subtype_mk
  fun_prop

theorem deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ne_zero_of_mem_originPhaseDomain
    {u : ℂ} (hu : u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain)
    (hslit : deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate u ≠ 0 := by
  by_cases hzero : u = 0
  · simpa [hzero] using deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_zero_ne
  have hphase_deriv : deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_ne_zero_of_norm_lt_two_pi
      hzero hu.2
  have hcoordinate : AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate u :=
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_of_factor_mem_slitPlane hslit
  have hsquare : HasDerivAt
      (fun z : ℂ => deBruijnNewmanPolymathBoydComplexSaddleCoordinate z ^ 2 / 2)
      (deBruijnNewmanPolymathBoydComplexSaddleCoordinate u *
        deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate u) u := by
    have hraw := (hcoordinate.differentiableAt.hasDerivAt.pow 2).div_const 2
    apply hraw.congr_deriv
    norm_num
    ring
  have hphase : HasDerivAt deBruijnNewmanPolymathBoydComplexSaddlePhase
      (deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u) u :=
    (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt u).differentiableAt.hasDerivAt
  have hmul :
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate u *
          deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate u =
        deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u :=
    (hphase.unique <| hsquare.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun z =>
        (deBruijnNewmanPolymathBoydComplexSaddleCoordinate_sq z).symm).symm
  intro hderiv
  apply hphase_deriv
  rw [← hmul, hderiv, mul_zero]

private def deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate : Opens ℂ :=
  ⟨deBruijnNewmanPolymathBoydOriginPhaseDomain,
    isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain⟩

private def deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen : Opens ℂ :=
  ⟨deBruijnNewmanPolymathBoydOpenCoordinateDisk, by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball⟩

private theorem exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    ∃ e : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
        deBruijnNewmanPolymathBoydOpenCoordinateDisk,
      u ∈ e.source ∧ e = deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain := by
  have hu_analytic : AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate u :=
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_of_factor_mem_slitPlane
      (hslit u u.property)
  have hu_deriv : deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate u ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ne_zero_of_mem_originPhaseDomain
      u.property (hslit u u.property)
  let hstrict := hu_analytic.hasStrictDerivAt.hasStrictFDerivAt_equiv hu_deriv
  let ambient : OpenPartialHomeomorph ℂ ℂ :=
    hstrict.toOpenPartialHomeomorph deBruijnNewmanPolymathBoydComplexSaddleCoordinate
  have hD : Nonempty deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate :=
    ⟨deBruijnNewmanPolymathBoydOriginPhaseDomainZero⟩
  have hW : Nonempty deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen :=
    ⟨deBruijnNewmanPolymathBoydOpenCoordinateDiskZero⟩
  let targetCoe : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOpenCoordinateDisk ℂ :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen.openPartialHomeomorphSubtypeCoe hW
  let e : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
      deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    (ambient.subtypeRestr hD).trans targetCoe.symm
  have hu_source :
      (⟨u, u.property⟩ : deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate) ∈
        ((ambient.subtypeRestr hD).trans targetCoe.symm).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hstrict.mem_toOpenPartialHomeomorph_source
    · rw [OpenPartialHomeomorph.symm_source]
      change deBruijnNewmanPolymathBoydComplexSaddleCoordinate u ∈
        (deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen
          |>.openPartialHomeomorphSubtypeCoe hW).target
      rw [Opens.openPartialHomeomorphSubtypeCoe_target]
      exact (deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain u).property
  let f0 : deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate →
      deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen :=
    fun x => ⟨deBruijnNewmanPolymathBoydComplexSaddleCoordinate x,
      (deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain x).property⟩
  have hfun :
      (fun x : deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate =>
          ((ambient.subtypeRestr hD).trans targetCoe.symm) x) =
        f0 := by
    funext x
    apply Subtype.ext
    rw [OpenPartialHomeomorph.trans_apply]
    change targetCoe (targetCoe.symm
      (deBruijnNewmanPolymathBoydComplexSaddleCoordinate x)) =
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate x
    apply targetCoe.right_inv
    change deBruijnNewmanPolymathBoydComplexSaddleCoordinate x ∈
      (deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen
        |>.openPartialHomeomorphSubtypeCoe hW).target
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact (f0 x).property
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e]
    exact hu_source
  · funext x
    dsimp only [e]
    exact congrFun hfun ⟨x, x.property⟩

theorem isLocalHomeomorph_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    IsLocalHomeomorph deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain := by
  apply IsLocalHomeomorph.mk
  intro u
  obtain ⟨e, hu, he⟩ :=
    exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain hslit u
  refine ⟨e, hu, ?_⟩
  rw [he]
  exact fun _ _ => rfl

theorem isProperMap_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    IsProperMap deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain := by
  apply isProperMap_of_comp_of_t2
    (continuous_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
      hslit)
    continuous_deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
  rw [deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_comp_coordinate]
  exact isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain

private theorem finite_preimage_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    (w : deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    (deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain ⁻¹' {w}).Finite := by
  have hlocal :
      ∀ u ∈ deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain ⁻¹' {w},
        ∃ e : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
            deBruijnNewmanPolymathBoydOpenCoordinateDisk,
          u ∈ e.source ∧ e =
            deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain := by
    intro u _
    exact
      exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain hslit u
  exact
    (isProperMap_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
      hslit |>.isCompact_preimage isCompact_singleton).finite
      (IsDiscrete.of_openPartialHomeomorph
        deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain subset_rfl hlocal)

/-- Under the exact no-cut premise, the normalized coordinate itself is a covering map of its
natural open disk. -/
theorem isCoveringMap_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    IsCoveringMap deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply (isProperMap_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
    hslit).isClosedMap.isCoveringMapOn_of_openPartialHomeomorph
  · intro w _
    exact
      finite_preimage_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
        hslit w
  · intro u _
    exact
      exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain hslit u

/-- The no-cut premise upgrades the principal normalized coordinate to a global homeomorphism from
the first Boyd phase domain onto its natural coordinate disk. -/
noncomputable def deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    deBruijnNewmanPolymathBoydOriginPhaseDomain ≃ₜ
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  letI : ContractibleSpace deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact Metric.contractibleSpace_ball (by positivity)
  letI : LocPathConnectedSpace deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball.locPathConnectedSpace
  letI : ConnectedSpace deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    isConnected_iff_connectedSpace.mp
      isConnected_deBruijnNewmanPolymathBoydOriginPhaseDomain
  let coordinate := deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain
  have hcont : Continuous coordinate :=
    continuous_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
      hslit
  have hlocal : IsLocalHomeomorph coordinate :=
    isLocalHomeomorph_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
      hslit
  have hcover : IsCoveringMap coordinate :=
    isCoveringMap_deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_of_factor_mem_slitPlane
      hslit
  let idW : C(deBruijnNewmanPolymathBoydOpenCoordinateDisk,
      deBruijnNewmanPolymathBoydOpenCoordinateDisk) := ContinuousMap.id _
  have hzero : coordinate deBruijnNewmanPolymathBoydOriginPhaseDomainZero =
      idW deBruijnNewmanPolymathBoydOpenCoordinateDiskZero := by
    exact deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain_zero
  have hinverse_exists :=
    hcover.existsUnique_continuousMap_lifts idW
      deBruijnNewmanPolymathBoydOpenCoordinateDiskZero
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero hzero
  let inverse := Classical.choose hinverse_exists.exists
  have hinverse := Classical.choose_spec hinverse_exists.exists
  have hright : Function.RightInverse inverse coordinate := by
    intro w
    exact congrFun hinverse.2 w
  have hleft_fun : inverse ∘ coordinate = id := by
    refine hcover.eq_of_comp_eq (inverse.continuous.comp hcont) continuous_id ?_
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero ?_
    · funext u
      exact hright (coordinate u)
    · change inverse
        (coordinate deBruijnNewmanPolymathBoydOriginPhaseDomainZero) =
          deBruijnNewmanPolymathBoydOriginPhaseDomainZero
      rw [hzero]
      exact hinverse.1
  have hleft : Function.LeftInverse inverse coordinate := by
    intro u
    exact congrFun hleft_fun u
  exact hlocal.toHomeomorphOfBijective ⟨hleft.injective, hright.surjective⟩

@[simp]
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane_apply
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit u =
      deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain u := rfl

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane_square
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
        (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit u) =
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain u := by
  change deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
      (deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain u) =
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain u
  exact congrFun deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_comp_coordinate u

/-- Conditional closure certificate: the single no-cut premise gives the global coordinate
homeomorphism, its square relation, and both inverse identities. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphConditionalCertificate
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    (∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit u) =
          deBruijnNewmanPolymathBoydPhaseOnOriginDomain u) ∧
      (∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit).symm
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit u) =
          u) ∧
      (∀ w : deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit
            ((deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane
              hslit).symm w) =
          w) := by
  exact ⟨
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane_square hslit,
    (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane
      hslit).symm_apply_apply,
    (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane
      hslit).apply_symm_apply⟩

/-- Ambient extension of the inverse normalized coordinate. Its value outside the natural disk is
irrelevant; inside the disk it is the inverse of the conditional global homeomorphism. -/
noncomputable def deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    (w : ℂ) : ℂ := by
  classical
  exact if hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk then
      ((deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane
        hslit).symm ⟨w, hw⟩ : ℂ)
    else 0

@[simp]
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane_apply
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    (w : deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane hslit w =
      ((deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane
        hslit).symm w : ℂ) := by
  simp [deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane, w.property]

/-- The ambient inverse is analytic at every point of the natural coordinate disk. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane_analyticAt
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane)
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    AnalyticAt ℂ
      (deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane hslit) w := by
  let e :=
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphOfFactorMemSlitPlane hslit
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk := ⟨w, hw⟩
  let uD : deBruijnNewmanPolymathBoydOriginPhaseDomain := e.symm wD
  have he_u : e uD = wD := e.apply_symm_apply wD
  have hcoordinate_u :
      deBruijnNewmanPolymathBoydCoordinateOnOriginPhaseDomain uD = wD := by
    simpa [e] using he_u
  have hcoordinate_u_val :
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate uD = w :=
    congrArg Subtype.val hcoordinate_u
  have hu_analytic : AnalyticAt ℂ
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate uD :=
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_of_factor_mem_slitPlane
      (hslit uD uD.property)
  have hu_deriv : deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate uD ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydComplexSaddleCoordinate_ne_zero_of_mem_originPhaseDomain
      uD.property (hslit uD uD.property)
  let localInverse : ℂ → ℂ :=
    hu_analytic.hasStrictDerivAt.localInverse
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate
      (deriv deBruijnNewmanPolymathBoydComplexSaddleCoordinate uD) uD hu_deriv
  have hlocal_analytic : AnalyticAt ℂ localInverse w := by
    rw [← hcoordinate_u_val]
    simpa [localInverse] using hu_analytic.analyticAt_localInverse hu_deriv
  have hlocal_at : localInverse w = uD := by
    rw [← hcoordinate_u_val]
    exact (hu_analytic.hasStrictDerivAt.eventually_left_inverse hu_deriv).self_of_nhds
  have hlocal_right : ∀ᶠ z in 𝓝 w,
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate (localInverse z) = z := by
    rw [← hcoordinate_u_val]
    simpa [localInverse] using
      hu_analytic.hasStrictDerivAt.eventually_right_inverse hu_deriv
  have hlocal_mem_domain : ∀ᶠ z in 𝓝 w,
      localInverse z ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain := by
    have hdomain_nhds :
        deBruijnNewmanPolymathBoydOriginPhaseDomain ∈ 𝓝 (localInverse w) := by
      rw [hlocal_at]
      exact isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain.mem_nhds uD.property
    exact hlocal_analytic.continuousAt hdomain_nhds
  have htarget_nhds :
      deBruijnNewmanPolymathBoydOpenCoordinateDisk ∈ 𝓝 w := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball.mem_nhds hw
  apply hlocal_analytic.congr
  filter_upwards [hlocal_right, hlocal_mem_domain, htarget_nhds] with z hz_right hz_domain hz_target
  rw [deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane,
    dif_pos hz_target]
  change localInverse z = (e.symm ⟨z, hz_target⟩ : ℂ)
  have hsubtype :
      (⟨localInverse z, hz_domain⟩ :
          deBruijnNewmanPolymathBoydOriginPhaseDomain) =
        e.symm ⟨z, hz_target⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hz_right
  exact congrArg Subtype.val hsubtype

/-- Conditional analytic closure certificate, including the disk-wide analytic inverse. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateAnalyticConditionalCertificate
    (hslit : ∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
      deBruijnNewmanPolymathBoydComplexSaddleFactor u ∈ Complex.slitPlane) :
    (∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
        AnalyticAt ℂ deBruijnNewmanPolymathBoydComplexSaddleCoordinate u) ∧
      (∀ w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        AnalyticAt ℂ
          (deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane hslit) w) := by
  exact ⟨fun u hu =>
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate_analyticAt_of_factor_mem_slitPlane
      (hslit u hu),
    fun _ hw =>
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverseOfFactorMemSlitPlane_analyticAt
        hslit hw⟩

private theorem exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydGlobalCoordinate
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    ∃ e : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
        deBruijnNewmanPolymathBoydOpenCoordinateDisk,
      u ∈ e.source ∧ e = deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain := by
  have hu_analytic : AnalyticAt ℂ deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u :=
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt u.property.1
  have hu_deriv : deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_ne_zero_of_mem_originPhaseDomain
      u.property
  let hstrict := hu_analytic.hasStrictDerivAt.hasStrictFDerivAt_equiv hu_deriv
  let ambient : OpenPartialHomeomorph ℂ ℂ :=
    hstrict.toOpenPartialHomeomorph deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
  have hD : Nonempty deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate :=
    ⟨deBruijnNewmanPolymathBoydOriginPhaseDomainZero⟩
  have hW : Nonempty deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen :=
    ⟨deBruijnNewmanPolymathBoydOpenCoordinateDiskZero⟩
  let targetCoe : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOpenCoordinateDisk ℂ :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen.openPartialHomeomorphSubtypeCoe hW
  let e : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
      deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    (ambient.subtypeRestr hD).trans targetCoe.symm
  have hu_source :
      (⟨u, u.property⟩ : deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate) ∈
        ((ambient.subtypeRestr hD).trans targetCoe.symm).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hstrict.mem_toOpenPartialHomeomorph_source
    · rw [OpenPartialHomeomorph.symm_source]
      change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u ∈
        (deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen
          |>.openPartialHomeomorphSubtypeCoe hW).target
      rw [Opens.openPartialHomeomorphSubtypeCoe_target]
      exact (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain u).property
  let f0 : deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate →
      deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen :=
    fun x => ⟨deBruijnNewmanPolymathBoydGlobalSaddleCoordinate x,
      (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain x).property⟩
  have hfun :
      (fun x : deBruijnNewmanPolymathBoydOriginPhaseDomainOpenForCoordinate =>
          ((ambient.subtypeRestr hD).trans targetCoe.symm) x) =
        f0 := by
    funext x
    apply Subtype.ext
    rw [OpenPartialHomeomorph.trans_apply]
    change targetCoe (targetCoe.symm
      (deBruijnNewmanPolymathBoydGlobalSaddleCoordinate x)) =
        deBruijnNewmanPolymathBoydGlobalSaddleCoordinate x
    apply targetCoe.right_inv
    change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate x ∈
      (deBruijnNewmanPolymathBoydOpenCoordinateDiskOpen
        |>.openPartialHomeomorphSubtypeCoe hW).target
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact (f0 x).property
  refine ⟨e, ?_, ?_⟩
  · dsimp only [e]
    exact hu_source
  · funext x
    dsimp only [e]
    exact congrFun hfun ⟨x, x.property⟩

theorem isLocalHomeomorph_deBruijnNewmanPolymathBoydGlobalCoordinate :
    IsLocalHomeomorph
      deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain := by
  apply IsLocalHomeomorph.mk
  intro u
  obtain ⟨e, hu, he⟩ :=
    exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydGlobalCoordinate u
  refine ⟨e, hu, ?_⟩
  rw [he]
  exact fun _ _ => rfl

theorem isProperMap_deBruijnNewmanPolymathBoydGlobalCoordinate :
    IsProperMap deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain := by
  apply isProperMap_of_comp_of_t2
    continuous_deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain
    continuous_deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
  rw [deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_comp_globalCoordinate]
  exact isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain

private theorem finite_preimage_deBruijnNewmanPolymathBoydGlobalCoordinate
    (w : deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain ⁻¹' {w}).Finite := by
  have hlocal :
      ∀ u ∈ deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain ⁻¹' {w},
        ∃ e : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
            deBruijnNewmanPolymathBoydOpenCoordinateDisk,
          u ∈ e.source ∧ e =
            deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain := by
    intro u _
    exact exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydGlobalCoordinate u
  exact
    (isProperMap_deBruijnNewmanPolymathBoydGlobalCoordinate.isCompact_preimage
      isCompact_singleton).finite
      (IsDiscrete.of_openPartialHomeomorph
        deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain subset_rfl hlocal)

theorem isCoveringMap_deBruijnNewmanPolymathBoydGlobalCoordinate :
    IsCoveringMap deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply isProperMap_deBruijnNewmanPolymathBoydGlobalCoordinate.isClosedMap
    |>.isCoveringMapOn_of_openPartialHomeomorph
  · intro w _
    exact finite_preimage_deBruijnNewmanPolymathBoydGlobalCoordinate w
  · intro u _
    exact exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydGlobalCoordinate u

/-- The normalized Boyd coordinate is an unconditional global homeomorphism from the first phase
domain onto its natural coordinate disk. -/
noncomputable def deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph :
    deBruijnNewmanPolymathBoydOriginPhaseDomain ≃ₜ
      deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
  letI : ContractibleSpace deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact Metric.contractibleSpace_ball (by positivity)
  letI : LocPathConnectedSpace deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball.locPathConnectedSpace
  letI : ConnectedSpace deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    isConnected_iff_connectedSpace.mp
      isConnected_deBruijnNewmanPolymathBoydOriginPhaseDomain
  let coordinate := deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain
  have hcont : Continuous coordinate :=
    continuous_deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain
  have hlocal : IsLocalHomeomorph coordinate :=
    isLocalHomeomorph_deBruijnNewmanPolymathBoydGlobalCoordinate
  have hcover : IsCoveringMap coordinate :=
    isCoveringMap_deBruijnNewmanPolymathBoydGlobalCoordinate
  let idW : C(deBruijnNewmanPolymathBoydOpenCoordinateDisk,
      deBruijnNewmanPolymathBoydOpenCoordinateDisk) := ContinuousMap.id _
  have hzero : coordinate deBruijnNewmanPolymathBoydOriginPhaseDomainZero =
      idW deBruijnNewmanPolymathBoydOpenCoordinateDiskZero := by
    exact deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain_zero
  have hinverse_exists :=
    hcover.existsUnique_continuousMap_lifts idW
      deBruijnNewmanPolymathBoydOpenCoordinateDiskZero
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero hzero
  let inverse := Classical.choose hinverse_exists.exists
  have hinverse := Classical.choose_spec hinverse_exists.exists
  have hright : Function.RightInverse inverse coordinate := by
    intro w
    exact congrFun hinverse.2 w
  have hleft_fun : inverse ∘ coordinate = id := by
    refine hcover.eq_of_comp_eq (inverse.continuous.comp hcont) continuous_id ?_
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero ?_
    · funext u
      exact hright (coordinate u)
    · change inverse
        (coordinate deBruijnNewmanPolymathBoydOriginPhaseDomainZero) =
          deBruijnNewmanPolymathBoydOriginPhaseDomainZero
      rw [hzero]
      exact hinverse.1
  have hleft : Function.LeftInverse inverse coordinate := by
    intro u
    exact congrFun hleft_fun u
  exact hlocal.toHomeomorphOfBijective ⟨hleft.injective, hright.surjective⟩

@[simp]
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph_apply
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph u =
      deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain u := rfl

theorem deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph_square
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain) :
    deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
        (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph u) =
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain u := by
  change deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
      (deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain u) =
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain u
  exact congrFun deBruijnNewmanPolymathBoydSquareOnCoordinateDisk_comp_globalCoordinate u

/-- Unconditional closure certificate for the normalized coordinate and both inverse identities. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphCertificate :
    (∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph u) =
          deBruijnNewmanPolymathBoydPhaseOnOriginDomain u) ∧
      (∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph u) = u) ∧
      (∀ w : deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm w) = w) := by
  exact ⟨
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph_square,
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm_apply_apply,
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.apply_symm_apply⟩

/-- Ambient extension of the unconditional inverse normalized coordinate. -/
noncomputable def deBruijnNewmanPolymathBoydNormalizedCoordinateInverse (w : ℂ) : ℂ := by
  classical
  exact if hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk then
      (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm ⟨w, hw⟩ : ℂ)
    else 0

@[simp]
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_apply
    (w : deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w =
      (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm w : ℂ) := by
  simp [deBruijnNewmanPolymathBoydNormalizedCoordinateInverse, w.property]

/-- The unconditional ambient inverse is analytic at every point of the natural coordinate disk. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt
    {w : ℂ} (hw : w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk) :
    AnalyticAt ℂ deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w := by
  let e := deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph
  let wD : deBruijnNewmanPolymathBoydOpenCoordinateDisk := ⟨w, hw⟩
  let uD : deBruijnNewmanPolymathBoydOriginPhaseDomain := e.symm wD
  have he_u : e uD = wD := e.apply_symm_apply wD
  have hcoordinate_u :
      deBruijnNewmanPolymathBoydGlobalCoordinateOnOriginPhaseDomain uD = wD := by
    simpa [e] using he_u
  have hcoordinate_u_val :
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate uD = w :=
    congrArg Subtype.val hcoordinate_u
  have hu_analytic : AnalyticAt ℂ
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate uD :=
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt uD.property.1
  have hu_deriv : deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate uD ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_ne_zero_of_mem_originPhaseDomain
      uD.property
  let localInverse : ℂ → ℂ :=
    hu_analytic.hasStrictDerivAt.localInverse
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate
      (deriv deBruijnNewmanPolymathBoydGlobalSaddleCoordinate uD) uD hu_deriv
  have hlocal_analytic : AnalyticAt ℂ localInverse w := by
    rw [← hcoordinate_u_val]
    simpa [localInverse] using hu_analytic.analyticAt_localInverse hu_deriv
  have hlocal_at : localInverse w = uD := by
    rw [← hcoordinate_u_val]
    exact (hu_analytic.hasStrictDerivAt.eventually_left_inverse hu_deriv).self_of_nhds
  have hlocal_right : ∀ᶠ z in 𝓝 w,
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate (localInverse z) = z := by
    rw [← hcoordinate_u_val]
    simpa [localInverse] using
      hu_analytic.hasStrictDerivAt.eventually_right_inverse hu_deriv
  have hlocal_mem_domain : ∀ᶠ z in 𝓝 w,
      localInverse z ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain := by
    have hdomain_nhds :
        deBruijnNewmanPolymathBoydOriginPhaseDomain ∈ 𝓝 (localInverse w) := by
      rw [hlocal_at]
      exact isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain.mem_nhds uD.property
    exact hlocal_analytic.continuousAt hdomain_nhds
  have htarget_nhds :
      deBruijnNewmanPolymathBoydOpenCoordinateDisk ∈ 𝓝 w := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball.mem_nhds hw
  apply hlocal_analytic.congr
  filter_upwards [hlocal_right, hlocal_mem_domain, htarget_nhds] with z hz_right hz_domain hz_target
  rw [deBruijnNewmanPolymathBoydNormalizedCoordinateInverse, dif_pos hz_target]
  change localInverse z = (e.symm ⟨z, hz_target⟩ : ℂ)
  have hsubtype :
      (⟨localInverse z, hz_domain⟩ :
          deBruijnNewmanPolymathBoydOriginPhaseDomain) = e.symm ⟨z, hz_target⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hz_right
  exact congrArg Subtype.val hsubtype

/-- The global coordinate and inverse are analytic throughout their natural open domains. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateAnalyticCertificate :
    (∀ u ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain,
        AnalyticAt ℂ deBruijnNewmanPolymathBoydGlobalSaddleCoordinate u) ∧
      (∀ w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        AnalyticAt ℂ deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) := by
  exact ⟨
    fun _ hu => deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_analyticAt hu.1,
    fun _ hw => deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_analyticAt hw⟩

/-- The strip square root has the normalized sign selected by the Loop 15 principal germ. -/
theorem deBruijnNewmanPolymathBoydGlobalSqrtFactor_eventually_eq_principal :
    deBruijnNewmanPolymathBoydGlobalSqrtFactor =ᶠ[𝓝 0]
      deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor := by
  have hzero_mem : (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip := by
    rw [deBruijnNewmanPolymathBoydOriginPhaseStrip]
    simpa using (show (0 : ℝ) < 2 * Real.pi by positivity)
  have hstrip : ∀ᶠ u in 𝓝 (0 : ℂ),
      u ∈ deBruijnNewmanPolymathBoydOriginPhaseStrip :=
    isOpen_deBruijnNewmanPolymathBoydOriginPhaseStrip.mem_nhds hzero_mem
  have hsum_cont : ContinuousAt
      (fun u : ℂ => deBruijnNewmanPolymathBoydGlobalSqrtFactor u +
        deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u) 0 :=
    (deBruijnNewmanPolymathBoydGlobalSqrtFactor_analyticAt hzero_mem).continuousAt.add
      deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_analyticAt_zero.continuousAt
  have hsum_ne : ∀ᶠ u in 𝓝 (0 : ℂ),
      deBruijnNewmanPolymathBoydGlobalSqrtFactor u +
          deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u ≠ 0 :=
    hsum_cont.eventually_ne (by norm_num)
  filter_upwards [hstrip, hsum_ne] with u hu hsum
  apply sub_eq_zero.mp
  have hproduct :
      (deBruijnNewmanPolymathBoydGlobalSqrtFactor u -
          deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u) *
        (deBruijnNewmanPolymathBoydGlobalSqrtFactor u +
          deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u) = 0 := by
    rw [show
      (deBruijnNewmanPolymathBoydGlobalSqrtFactor u -
          deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u) *
        (deBruijnNewmanPolymathBoydGlobalSqrtFactor u +
          deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u) =
        deBruijnNewmanPolymathBoydGlobalSqrtFactor u ^ 2 -
          deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor u ^ 2 by ring,
      deBruijnNewmanPolymathBoydGlobalSqrtFactor_sq hu,
      deBruijnNewmanPolymathBoydComplexSaddleSqrtFactor_sq]
    ring
  exact (mul_eq_zero.mp hproduct).resolve_right hsum

/-- Consequently, the global normalized coordinate is the Loop 15 coordinate germ at zero. -/
theorem deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_eventually_eq_local :
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate =ᶠ[𝓝 0]
      deBruijnNewmanPolymathBoydComplexSaddleCoordinate := by
  filter_upwards
    [deBruijnNewmanPolymathBoydGlobalSqrtFactor_eventually_eq_principal] with u hu
  simp only [deBruijnNewmanPolymathBoydGlobalSaddleCoordinate,
    deBruijnNewmanPolymathBoydComplexSaddleCoordinate, hu]

/-- The disk-wide inverse genuinely extends the Loop 15 local inverse germ. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local :
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse =ᶠ[𝓝 0]
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse := by
  let localInverse := deBruijnNewmanPolymathBoydComplexSaddleLocalInverse
  have hlocal_zero : localInverse 0 = 0 := by
    have hleft :=
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_left.self_of_nhds
    simpa [localInverse] using hleft
  have hlocal_tendsto : Filter.Tendsto localInverse (𝓝 0) (𝓝 0) := by
    have hcont : ContinuousAt localInverse 0 :=
      deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_analyticAt_zero.continuousAt
    change Filter.Tendsto localInverse (𝓝 0) (𝓝 (localInverse 0)) at hcont
    simpa only [hlocal_zero] using hcont
  have hdomain_zero :
      (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    deBruijnNewmanPolymathBoydOriginPhaseDomainZero.property
  have hlocal_domain : ∀ᶠ z in 𝓝 (0 : ℂ),
      localInverse z ∈ deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    hlocal_tendsto
      (isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain.mem_nhds hdomain_zero)
  have hcoordinate_at_local : ∀ᶠ z in 𝓝 (0 : ℂ),
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate (localInverse z) =
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate (localInverse z) :=
    hlocal_tendsto
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_eventually_eq_local
  have htarget_zero :
      (0 : ℂ) ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk :=
    deBruijnNewmanPolymathBoydOpenCoordinateDiskZero.property
  have htarget : ∀ᶠ z in 𝓝 (0 : ℂ),
      z ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk := by
    rw [deBruijnNewmanPolymathBoydOpenCoordinateDisk]
    exact isOpen_ball.mem_nhds htarget_zero
  filter_upwards [hlocal_domain, hcoordinate_at_local, htarget,
    deBruijnNewmanPolymathBoydComplexSaddleLocalInverse_eventually_right]
      with z hz_domain hz_coordinate hz_target hz_right
  rw [deBruijnNewmanPolymathBoydNormalizedCoordinateInverse, dif_pos hz_target]
  let e := deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph
  have heq : e ⟨localInverse z, hz_domain⟩ = ⟨z, hz_target⟩ := by
    apply Subtype.ext
    change deBruijnNewmanPolymathBoydGlobalSaddleCoordinate (localInverse z) = z
    rw [hz_coordinate]
    exact hz_right
  have hinverse : e.symm ⟨z, hz_target⟩ = ⟨localInverse z, hz_domain⟩ := by
    rw [← heq]
    exact e.symm_apply_apply _
  exact congrArg Subtype.val hinverse

/-- Aggregate certificate for the global normalized coordinate, analytic inverse, and Loop 15
germ compatibility. -/
theorem deBruijnNewmanPolymathBoydNormalizedCoordinateGlobalCertificate :
    ((∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        deBruijnNewmanPolymathBoydSquareOnCoordinateDisk
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph u) =
          deBruijnNewmanPolymathBoydPhaseOnOriginDomain u) ∧
      (∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph u) = u) ∧
      (∀ w : deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph
            (deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorph.symm w) = w)) ∧
      (∀ w ∈ deBruijnNewmanPolymathBoydOpenCoordinateDisk,
        AnalyticAt ℂ deBruijnNewmanPolymathBoydNormalizedCoordinateInverse w) ∧
      deBruijnNewmanPolymathBoydGlobalSaddleCoordinate =ᶠ[𝓝 0]
        deBruijnNewmanPolymathBoydComplexSaddleCoordinate ∧
      deBruijnNewmanPolymathBoydNormalizedCoordinateInverse =ᶠ[𝓝 0]
        deBruijnNewmanPolymathBoydComplexSaddleLocalInverse := by
  exact ⟨
    deBruijnNewmanPolymathBoydNormalizedCoordinateHomeomorphCertificate,
    deBruijnNewmanPolymathBoydNormalizedCoordinateAnalyticCertificate.2,
    deBruijnNewmanPolymathBoydGlobalSaddleCoordinate_eventually_eq_local,
    deBruijnNewmanPolymathBoydNormalizedCoordinateInverse_eventually_eq_local⟩

end

end LeanLab.Riemann
