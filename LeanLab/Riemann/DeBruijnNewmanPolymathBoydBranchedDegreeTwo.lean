import LeanLab.Riemann.DeBruijnNewmanPolymathBoydPhaseDomainConnectedness
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Lifting

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The branched degree of the first Boyd phase domain

This module proves that the proper first-strip Boyd phase is a covering away from its unique branch
value and that every nonzero fiber in the first phase disk has exactly two points.
-/

namespace LeanLab.Riemann

open Complex Metric Set
open TopologicalSpace
open scoped ComplexConjugate Topology

noncomputable section

private theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_im_eq_zero_of_im_nonneg_of_posReal
    {u : ℂ} {r : ℝ} (him_nonneg : 0 ≤ u.im) (him_lt : u.im < 2 * Real.pi)
    (hr : 0 < r) (hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = (r : ℂ)) :
    u.im = 0 := by
  have hre : Real.exp u.re * Real.cos u.im - u.re - 1 = r := by
    have h := congrArg Complex.re hphase
    simpa [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_re] using h
  have him : Real.exp u.re * Real.sin u.im = u.im := by
    have h := congrArg Complex.im hphase
    simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_im] at h
    linarith
  by_contra him_ne
  have him_pos : 0 < u.im := lt_of_le_of_ne him_nonneg (Ne.symm him_ne)
  by_cases hpi : Real.pi ≤ u.im
  · have hsin_nonpos : Real.sin u.im ≤ 0 := by
      rw [← Real.sin_sub_two_pi u.im]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
    have hproduct_nonpos : Real.exp u.re * Real.sin u.im ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hsin_nonpos
    linarith
  · have him_pi : u.im < Real.pi := lt_of_not_ge hpi
    have hsin_pos : 0 < Real.sin u.im :=
      Real.sin_pos_of_pos_of_lt_pi him_pos him_pi
    have hexp_gt_one : 1 < Real.exp u.re := by
      have hsin_lt := Real.sin_lt him_pos
      nlinarith
    have hre_pos : 0 < u.re := Real.one_lt_exp_iff.mp hexp_gt_one
    by_cases hhalf : Real.pi / 2 ≤ u.im
    · have hcos_nonpos : Real.cos u.im ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le hhalf (by linarith [Real.pi_pos])
      have hproduct_nonpos : Real.exp u.re * Real.cos u.im ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hcos_nonpos
      linarith
    · have him_half : u.im < Real.pi / 2 := lt_of_not_ge hhalf
      have hcos_pos : 0 < Real.cos u.im :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], him_half⟩
      have htan_eq :
          (Real.exp u.re * Real.cos u.im) * Real.tan u.im = u.im := by
        rw [Real.tan_eq_sin_div_cos]
        field_simp [hcos_pos.ne']
        nlinarith
      have hlt_tan := Real.lt_tan him_pos him_half
      have htan_pos := Real.tan_pos_of_pos_of_lt_pi_div_two him_pos him_half
      have hproduct_lt_one : Real.exp u.re * Real.cos u.im < 1 := by
        nlinarith
      linarith

/-- A positive real phase value in the first saddle strip has only real preimages. -/
theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_im_eq_zero_of_eq_posReal
    {u : ℂ} {r : ℝ} (hu : |u.im| < 2 * Real.pi) (hr : 0 < r)
    (hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = (r : ℂ)) :
    u.im = 0 := by
  by_cases him : 0 ≤ u.im
  · exact deBruijnNewmanPolymathBoydComplexSaddlePhase_im_eq_zero_of_im_nonneg_of_posReal
      him (lt_of_le_of_lt (le_abs_self _) hu) hr hphase
  · have hconj_im_nonneg : 0 ≤ (conj u).im := by
      simp only [Complex.conj_im]
      exact (neg_pos.mpr (lt_of_not_ge him)).le
    have hconj_im_lt : (conj u).im < 2 * Real.pi := by
      simp only [Complex.conj_im]
      exact lt_of_le_of_lt (neg_le_abs _) hu
    have hconj_phase :
        deBruijnNewmanPolymathBoydComplexSaddlePhase (conj u) = (r : ℂ) := by
      rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_conj, hphase]
      simp
    have hzero :=
      deBruijnNewmanPolymathBoydComplexSaddlePhase_im_eq_zero_of_im_nonneg_of_posReal
        hconj_im_nonneg hconj_im_lt hr hconj_phase
    simpa using hzero

/-- The positive real value one, as a point of the open target phase disk. -/
def deBruijnNewmanPolymathBoydOpenPhaseDiskOne :
    deBruijnNewmanPolymathBoydOpenPhaseDisk :=
  ⟨1, by
    rw [deBruijnNewmanPolymathBoydOpenPhaseDisk, mem_ball, dist_zero_right, norm_one]
    linarith [Real.pi_gt_three]⟩

private theorem deBruijnNewmanPolymathBoydRealSaddlePhase_inverse_neg_sqrt_two :
    deBruijnNewmanPolymathBoydRealSaddlePhase
        (deBruijnNewmanPolymathBoydRealSaddleInverse (-Real.sqrt 2)) = 1 := by
  rw [← deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq,
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_inverse]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private theorem deBruijnNewmanPolymathBoydRealSaddlePhase_inverse_sqrt_two :
    deBruijnNewmanPolymathBoydRealSaddlePhase
        (deBruijnNewmanPolymathBoydRealSaddleInverse (Real.sqrt 2)) = 1 := by
  rw [← deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq,
    deBruijnNewmanPolymathBoydRealSaddleCoordinate_inverse]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The negative real preimage of the phase value one in the first saddle domain. -/
def deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage :
    deBruijnNewmanPolymathBoydOriginPhaseDomain :=
  ⟨(deBruijnNewmanPolymathBoydRealSaddleInverse (-Real.sqrt 2) : ℂ), by
    constructor
    · simp only [ofReal_im, abs_zero]
      positivity
    · rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal,
        deBruijnNewmanPolymathBoydRealSaddlePhase_inverse_neg_sqrt_two]
      rw [Complex.norm_real, norm_one]
      linarith [Real.pi_gt_three]⟩

/-- The positive real preimage of the phase value one in the first saddle domain. -/
def deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage :
    deBruijnNewmanPolymathBoydOriginPhaseDomain :=
  ⟨(deBruijnNewmanPolymathBoydRealSaddleInverse (Real.sqrt 2) : ℂ), by
    constructor
    · simp only [ofReal_im, abs_zero]
      positivity
    · rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal,
        deBruijnNewmanPolymathBoydRealSaddlePhase_inverse_sqrt_two]
      rw [Complex.norm_real, norm_one]
      linarith [Real.pi_gt_three]⟩

theorem deBruijnNewmanPolymathBoydPhaseOnOriginDomain_negativeOnePreimage :
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain
        deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage =
      deBruijnNewmanPolymathBoydOpenPhaseDiskOne := by
  apply Subtype.ext
  simp [deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
    deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage,
    deBruijnNewmanPolymathBoydOpenPhaseDiskOne,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal,
    deBruijnNewmanPolymathBoydRealSaddlePhase_inverse_neg_sqrt_two]

theorem deBruijnNewmanPolymathBoydPhaseOnOriginDomain_positiveOnePreimage :
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain
        deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage =
      deBruijnNewmanPolymathBoydOpenPhaseDiskOne := by
  apply Subtype.ext
  simp [deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
    deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage,
    deBruijnNewmanPolymathBoydOpenPhaseDiskOne,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal,
    deBruijnNewmanPolymathBoydRealSaddlePhase_inverse_sqrt_two]

theorem deBruijnNewmanPolymathBoydOriginPhaseDomain_onePreimages_ne :
    deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage ≠
      deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage := by
  intro h
  have hre := congrArg (fun u : deBruijnNewmanPolymathBoydOriginPhaseDomain => u.val.re) h
  have hinv :
      deBruijnNewmanPolymathBoydRealSaddleInverse (-Real.sqrt 2) =
        deBruijnNewmanPolymathBoydRealSaddleInverse (Real.sqrt 2) := by
    simpa [deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage,
      deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage] using hre
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have harg := deBruijnNewmanPolymathBoydRealSaddleOrderIso.symm.injective hinv
  linarith

/-- The fiber over phase value one consists exactly of the two real inverse-coordinate points. -/
theorem deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_one :
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
        {deBruijnNewmanPolymathBoydOpenPhaseDiskOne} =
      {deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage,
        deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage} := by
  ext u
  simp only [mem_preimage, mem_singleton_iff, mem_insert_iff]
  constructor
  · intro hu
    have hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = (1 : ℂ) := by
      simpa [deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
        deBruijnNewmanPolymathBoydOpenPhaseDiskOne] using congrArg Subtype.val hu
    have him : u.val.im = 0 :=
      deBruijnNewmanPolymathBoydComplexSaddlePhase_im_eq_zero_of_eq_posReal
        u.property.1 (by norm_num) hphase
    have hu_ofReal : u.val = (u.val.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hreal : deBruijnNewmanPolymathBoydRealSaddlePhase u.val.re = 1 := by
      have hphase' := hphase
      rw [hu_ofReal, deBruijnNewmanPolymathBoydComplexSaddlePhase_ofReal] at hphase'
      simpa using congrArg Complex.re hphase'
    have hcoordinate_sq :
        deBruijnNewmanPolymathBoydRealSaddleCoordinate u.val.re ^ 2 = 2 := by
      nlinarith [deBruijnNewmanPolymathBoydRealSaddleCoordinate_sq u.val.re]
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hcases :
        deBruijnNewmanPolymathBoydRealSaddleCoordinate u.val.re = Real.sqrt 2 ∨
          deBruijnNewmanPolymathBoydRealSaddleCoordinate u.val.re = -Real.sqrt 2 :=
      sq_eq_sq_iff_eq_or_eq_neg.mp (hcoordinate_sq.trans hsqrt_sq.symm)
    rcases hcases with hpositive | hnegative
    · right
      apply Subtype.ext
      apply Complex.ext
      · simp only [deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage, ofReal_re]
        calc
          u.val.re = deBruijnNewmanPolymathBoydRealSaddleInverse
              (deBruijnNewmanPolymathBoydRealSaddleCoordinate u.val.re) :=
            (deBruijnNewmanPolymathBoydRealSaddleInverse_coordinate u.val.re).symm
          _ = deBruijnNewmanPolymathBoydRealSaddleInverse (Real.sqrt 2) := by rw [hpositive]
      · simpa [deBruijnNewmanPolymathBoydOriginPhaseDomainPositiveOnePreimage] using him
    · left
      apply Subtype.ext
      apply Complex.ext
      · simp only [deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage, ofReal_re]
        calc
          u.val.re = deBruijnNewmanPolymathBoydRealSaddleInverse
              (deBruijnNewmanPolymathBoydRealSaddleCoordinate u.val.re) :=
            (deBruijnNewmanPolymathBoydRealSaddleInverse_coordinate u.val.re).symm
          _ = deBruijnNewmanPolymathBoydRealSaddleInverse (-Real.sqrt 2) := by rw [hnegative]
      · simpa [deBruijnNewmanPolymathBoydOriginPhaseDomainNegativeOnePreimage] using him
  · rintro (rfl | rfl)
    · exact deBruijnNewmanPolymathBoydPhaseOnOriginDomain_negativeOnePreimage
    · exact deBruijnNewmanPolymathBoydPhaseOnOriginDomain_positiveOnePreimage

private def deBruijnNewmanPolymathBoydOriginPhaseDomainOpen : Opens ℂ :=
  ⟨deBruijnNewmanPolymathBoydOriginPhaseDomain,
    isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain⟩

private def deBruijnNewmanPolymathBoydOpenPhaseDiskOpen : Opens ℂ :=
  ⟨deBruijnNewmanPolymathBoydOpenPhaseDisk, by
    rw [deBruijnNewmanPolymathBoydOpenPhaseDisk]
    exact isOpen_ball⟩

private theorem exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydPhaseOnOriginDomain
    (u : deBruijnNewmanPolymathBoydOriginPhaseDomain)
    (hu : deBruijnNewmanPolymathBoydPhaseOnOriginDomain u ≠
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero) :
    ∃ φ : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
        deBruijnNewmanPolymathBoydOpenPhaseDisk,
      u ∈ φ.source ∧ φ = deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  have hu_ne : (u : ℂ) ≠ 0 := by
    intro hzero
    apply hu
    apply Subtype.ext
    simp [deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero, hzero]
  have hderiv : deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u ≠ 0 :=
    deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_ne_zero_of_norm_lt_two_pi
      hu_ne u.property.2
  let hstrict :=
    (deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt (u : ℂ)).hasStrictDerivAt
      |>.hasStrictFDerivAt_equiv hderiv
  let e : OpenPartialHomeomorph ℂ ℂ :=
    hstrict.toOpenPartialHomeomorph deBruijnNewmanPolymathBoydComplexSaddlePhase
  have hD : Nonempty deBruijnNewmanPolymathBoydOriginPhaseDomainOpen :=
    ⟨deBruijnNewmanPolymathBoydOriginPhaseDomainZero⟩
  have hB : Nonempty deBruijnNewmanPolymathBoydOpenPhaseDiskOpen :=
    ⟨deBruijnNewmanPolymathBoydOpenPhaseDiskZero⟩
  let b : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOpenPhaseDisk ℂ :=
    deBruijnNewmanPolymathBoydOpenPhaseDiskOpen.openPartialHomeomorphSubtypeCoe hB
  let φ : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
      deBruijnNewmanPolymathBoydOpenPhaseDisk :=
    (e.subtypeRestr hD).trans b.symm
  have hu_source :
      (⟨u, u.property⟩ : deBruijnNewmanPolymathBoydOriginPhaseDomainOpen) ∈
        ((e.subtypeRestr hD).trans b.symm).source := by
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      exact hstrict.mem_toOpenPartialHomeomorph_source
    · rw [OpenPartialHomeomorph.symm_source]
      change deBruijnNewmanPolymathBoydComplexSaddlePhase u ∈
        (deBruijnNewmanPolymathBoydOpenPhaseDiskOpen.openPartialHomeomorphSubtypeCoe hB).target
      rw [Opens.openPartialHomeomorphSubtypeCoe_target]
      change deBruijnNewmanPolymathBoydComplexSaddlePhase u ∈
        deBruijnNewmanPolymathBoydOpenPhaseDisk
      rw [deBruijnNewmanPolymathBoydOpenPhaseDisk, mem_ball, dist_zero_right]
      exact u.property.2
  let f0 : deBruijnNewmanPolymathBoydOriginPhaseDomainOpen →
      deBruijnNewmanPolymathBoydOpenPhaseDiskOpen :=
    fun x => ⟨deBruijnNewmanPolymathBoydComplexSaddlePhase x, by
      change deBruijnNewmanPolymathBoydComplexSaddlePhase x ∈
        deBruijnNewmanPolymathBoydOpenPhaseDisk
      rw [deBruijnNewmanPolymathBoydOpenPhaseDisk, mem_ball, dist_zero_right]
      exact x.property.2⟩
  have hfun :
      (fun x : deBruijnNewmanPolymathBoydOriginPhaseDomainOpen =>
          ((e.subtypeRestr hD).trans b.symm) x) =
        f0 := by
    funext x
    apply Subtype.ext
    rw [OpenPartialHomeomorph.trans_apply]
    change b (b.symm (deBruijnNewmanPolymathBoydComplexSaddlePhase x)) =
      deBruijnNewmanPolymathBoydComplexSaddlePhase x
    apply b.right_inv
    change deBruijnNewmanPolymathBoydComplexSaddlePhase x ∈
      (deBruijnNewmanPolymathBoydOpenPhaseDiskOpen.openPartialHomeomorphSubtypeCoe hB).target
    rw [Opens.openPartialHomeomorphSubtypeCoe_target]
    exact (f0 x).property
  refine ⟨φ, ?_, ?_⟩
  · dsimp only [φ]
    exact hu_source
  · funext x
    dsimp only [φ]
    exact congrFun hfun ⟨x, x.property⟩

private theorem finite_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_of_ne_zero
    (z : deBruijnNewmanPolymathBoydOpenPhaseDisk)
    (hz : z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero) :
    (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z}).Finite := by
  have hlocal :
      ∀ u ∈ deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z},
        ∃ φ : OpenPartialHomeomorph deBruijnNewmanPolymathBoydOriginPhaseDomain
            deBruijnNewmanPolymathBoydOpenPhaseDisk,
          u ∈ φ.source ∧ φ = deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
    intro u hu
    apply exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydPhaseOnOriginDomain u
    intro hzero
    apply hz
    exact (mem_singleton_iff.mp hu).symm.trans hzero
  exact (isCompact_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain isCompact_singleton).finite
    (IsDiscrete.of_openPartialHomeomorph deBruijnNewmanPolymathBoydPhaseOnOriginDomain
      subset_rfl hlocal)

/-- Away from its unique branch value, the actual first-strip phase map is a covering map. -/
theorem isCoveringMapOn_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_away_zero :
    IsCoveringMapOn deBruijnNewmanPolymathBoydPhaseOnOriginDomain
      {deBruijnNewmanPolymathBoydOpenPhaseDiskZero}ᶜ := by
  apply isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain.isClosedMap
    |>.isCoveringMapOn_of_openPartialHomeomorph
  · intro z hz
    exact finite_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_of_ne_zero z (by simpa using hz)
  · intro u hu
    apply exists_openPartialHomeomorph_deBruijnNewmanPolymathBoydPhaseOnOriginDomain u
    simpa using hu

/-- The punctured first phase disk, with the unique branch value removed. -/
def deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :
    Set deBruijnNewmanPolymathBoydOpenPhaseDisk :=
  {deBruijnNewmanPolymathBoydOpenPhaseDiskZero}ᶜ

/-- The source of the phase map after removing the zero fiber. -/
def deBruijnNewmanPolymathBoydNonzeroOriginPhaseDomain :
    Set deBruijnNewmanPolymathBoydOriginPhaseDomain :=
  deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
    deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk

/-- The unbranched phase map between the punctured source and target subtypes. -/
def deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain :
    deBruijnNewmanPolymathBoydNonzeroOriginPhaseDomain →
      deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :=
  deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk.restrictPreimage
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain

/-- The punctured first-strip Boyd phase is an actual covering map. -/
theorem isCoveringMap_deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain :
    IsCoveringMap deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain := by
  change IsCoveringMap
    (({deBruijnNewmanPolymathBoydOpenPhaseDiskZero}ᶜ :
      Set deBruijnNewmanPolymathBoydOpenPhaseDisk).restrictPreimage
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain)
  exact isCoveringMapOn_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_away_zero
    |>.isCoveringMap_restrictPreimage

private def deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph :
    ℂ ≃ₜ deBruijnNewmanPolymathBoydOpenPhaseDisk := by
  exact (Homeomorph.Set.univ ℂ).symm
    |>.trans (Homeomorph.setCongr (by
      rw [OpenPartialHomeomorph.univBall_source (0 : ℂ) (2 * Real.pi)]))
    |>.trans (OpenPartialHomeomorph.univBall (0 : ℂ) (2 * Real.pi)).toHomeomorphSourceTarget
    |>.trans (Homeomorph.setCongr (by
      rw [OpenPartialHomeomorph.univBall_target (0 : ℂ) (by positivity)]
      rfl))

private theorem deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph_zero :
    deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph 0 =
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero := by
  apply Subtype.ext
  change OpenPartialHomeomorph.univBall (0 : ℂ) (2 * Real.pi) 0 = 0
  exact OpenPartialHomeomorph.univBall_apply_zero (0 : ℂ) (2 * Real.pi)

private def deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskHomeomorph :
    {z : ℂ // z ≠ 0} ≃ₜ deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :=
  deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph.subtype fun z => by
    change z ≠ 0 ↔ deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph z ≠
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero
    constructor
    · intro hz hzero
      apply hz
      apply deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph.injective
      rw [hzero, deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph_zero]
    · intro hz hzero
      apply hz
      rw [← deBruijnNewmanPolymathBoydOpenPhaseDiskHomeomorph_zero, hzero]

/-- Removing the unique branch value leaves a path-connected target disk. -/
theorem isPathConnected_deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :
    IsPathConnected deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk := by
  have hcomplex : IsPathConnected {z : ℂ | z ≠ 0} := by
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    rw [show {z : ℂ | z ≠ 0} = ({0} : Set ℂ)ᶜ by ext; simp]
    exact isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : ℂ)
  letI : PathConnectedSpace {z : ℂ // z ≠ 0} :=
    isPathConnected_iff_pathConnectedSpace.mp hcomplex
  letI : PathConnectedSpace deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :=
    deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskHomeomorph.surjective.pathConnectedSpace
      deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskHomeomorph.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

private theorem deBruijnNewmanPolymathBoydOpenPhaseDiskOne_ne_zero :
    deBruijnNewmanPolymathBoydOpenPhaseDiskOne ≠
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero := by
  intro h
  have := congrArg Subtype.val h
  change (1 : ℂ) = 0 at this
  exact one_ne_zero this

theorem natCard_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_one :
    Nat.card (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
      {deBruijnNewmanPolymathBoydOpenPhaseDiskOne}) = 2 := by
  rw [deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_one]
  simp [deBruijnNewmanPolymathBoydOriginPhaseDomain_onePreimages_ne]

private def deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskPoint
    (z : deBruijnNewmanPolymathBoydOpenPhaseDisk)
    (hz : z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero) :
    deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :=
  ⟨z, by
    change z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero
    exact hz⟩

private def deBruijnNewmanPolymathBoydPhaseFiberEquivPunctured
    (z : deBruijnNewmanPolymathBoydOpenPhaseDisk)
    (hz : z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero) :
    (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z}) ≃
      (deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain ⁻¹'
        {deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskPoint z hz}) where
  toFun x := by
    have hx : deBruijnNewmanPolymathBoydPhaseOnOriginDomain x = z :=
      mem_singleton_iff.mp x.property
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change deBruijnNewmanPolymathBoydPhaseOnOriginDomain x ≠
        deBruijnNewmanPolymathBoydOpenPhaseDiskZero
      rw [hx]
      exact hz
    · apply Subtype.ext
      exact hx
  invFun y := by
    refine ⟨y.val.val, ?_⟩
    apply mem_singleton_iff.mpr
    have hy := mem_singleton_iff.mp y.property
    exact congrArg Subtype.val hy
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl

/-- Every regular fiber in the first phase disk has exactly two points. -/
theorem natCard_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_eq_two_of_ne_zero
    (z : deBruijnNewmanPolymathBoydOpenPhaseDisk)
    (hz : z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero) :
    Nat.card (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z}) = 2 := by
  letI : PathConnectedSpace deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk :=
    isPathConnected_iff_pathConnectedSpace.mp
      isPathConnected_deBruijnNewmanPolymathBoydPuncturedOpenPhaseDisk
  let zOne := deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskPoint
    deBruijnNewmanPolymathBoydOpenPhaseDiskOne
    deBruijnNewmanPolymathBoydOpenPhaseDiskOne_ne_zero
  let zTarget := deBruijnNewmanPolymathBoydPuncturedOpenPhaseDiskPoint z hz
  let γ : Path zOne zTarget := PathConnectedSpace.somePath zOne zTarget
  let q : Path.Homotopic.Quotient zOne zTarget := .mk γ
  let cov := isCoveringMap_deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain
  let fiberEquiv :
      (deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain ⁻¹' {zOne}) ≃
        (deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain ⁻¹' {zTarget}) :=
    Equiv.ofBijective (cov.monodromy q) (cov.monodromy_bijective q)
  calc
    Nat.card (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z}) =
        Nat.card (deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain ⁻¹' {zTarget}) :=
      Nat.card_congr (deBruijnNewmanPolymathBoydPhaseFiberEquivPunctured z hz)
    _ = Nat.card (deBruijnNewmanPolymathBoydPhaseOnNonzeroOriginDomain ⁻¹' {zOne}) :=
      (Nat.card_congr fiberEquiv).symm
    _ = Nat.card (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
          {deBruijnNewmanPolymathBoydOpenPhaseDiskOne}) :=
      (Nat.card_congr
        (deBruijnNewmanPolymathBoydPhaseFiberEquivPunctured
          deBruijnNewmanPolymathBoydOpenPhaseDiskOne
          deBruijnNewmanPolymathBoydOpenPhaseDiskOne_ne_zero)).symm
    _ = 2 := natCard_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_one

/-- The complete branched degree-two certificate for the first-strip Boyd phase. -/
theorem deBruijnNewmanPolymathBoydPhaseOnOriginDomain_branchedDegreeTwoCertificate :
    (deBruijnNewmanPolymathBoydComplexSaddlePhase 0 = 0 ∧
        deriv deBruijnNewmanPolymathBoydComplexSaddlePhase 0 = 0 ∧
        deriv (deriv deBruijnNewmanPolymathBoydComplexSaddlePhase) 0 = 1) ∧
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
          {deBruijnNewmanPolymathBoydOpenPhaseDiskZero} =
        {deBruijnNewmanPolymathBoydOriginPhaseDomainZero} ∧
      (∀ u : deBruijnNewmanPolymathBoydOriginPhaseDomain,
        deriv deBruijnNewmanPolymathBoydComplexSaddlePhase u = 0 ↔
          u = deBruijnNewmanPolymathBoydOriginPhaseDomainZero) ∧
      ∀ z : deBruijnNewmanPolymathBoydOpenPhaseDisk,
        z ≠ deBruijnNewmanPolymathBoydOpenPhaseDiskZero →
          Nat.card (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹' {z}) = 2 := by
  refine ⟨⟨deBruijnNewmanPolymathBoydComplexSaddlePhase_zero,
    deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_zero,
    deriv_deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_zero⟩,
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_zero, ?_,
    natCard_preimage_deBruijnNewmanPolymathBoydPhaseOnOriginDomain_eq_two_of_ne_zero⟩
  intro u
  constructor
  · intro hcritical
    apply Subtype.ext
    by_contra hu_ne
    exact (deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_ne_zero_of_norm_lt_two_pi
      hu_ne u.property.2) hcritical
  · rintro rfl
    exact deriv_deBruijnNewmanPolymathBoydComplexSaddlePhase_zero

end

end LeanLab.Riemann
