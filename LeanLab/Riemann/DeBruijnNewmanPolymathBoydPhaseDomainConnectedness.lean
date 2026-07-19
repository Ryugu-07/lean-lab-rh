import LeanLab.Riemann.DeBruijnNewmanPolymathBoydStripProperness
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Connected.CardComponents

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Connectedness and surjectivity of the first Boyd phase domain

This module proves that the first-strip Boyd phase domain is connected and that its proper phase
map covers the full open phase disk. The key input beyond properness is that the phase has only its
double origin zero in the first strip.
-/

namespace LeanLab.Riemann

open Complex Metric Set
open scoped ComplexConjugate Topology

noncomputable section

private theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_of_im_nonneg
    {u : ℂ} (him_nonneg : 0 ≤ u.im) (him_lt : u.im < 2 * Real.pi)
    (hphase : deBruijnNewmanPolymathBoydComplexSaddlePhase u = 0) :
    u = 0 := by
  have hre : Real.exp u.re * Real.cos u.im = u.re + 1 := by
    have h := congrArg Complex.re hphase
    simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_re] at h
    linarith
  have him : Real.exp u.re * Real.sin u.im = u.im := by
    have h := congrArg Complex.im hphase
    simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_im] at h
    linarith
  have him_zero : u.im = 0 := by
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
      have hre_neg : u.re < 0 := by
        by_contra hre_not_neg
        have hre_nonneg : 0 ≤ u.re := le_of_not_gt hre_not_neg
        have hcos_pos : 0 < Real.cos u.im := by
          have hproduct_pos : 0 < Real.exp u.re * Real.cos u.im := by
            rw [hre]
            linarith
          rcases (mul_pos_iff.mp hproduct_pos) with hpos | hneg
          · exact hpos.2
          · exact (not_lt_of_ge (Real.exp_pos _).le hneg.1).elim
        have him_half_pi : u.im < Real.pi / 2 := by
          by_contra him_not_lt
          have hcos_nonpos := Real.cos_nonpos_of_pi_div_two_le_of_le
            (le_of_not_gt him_not_lt) (by linarith [Real.pi_pos])
          linarith
        have htan_eq : (u.re + 1) * Real.tan u.im = u.im := by
          rw [Real.tan_eq_sin_div_cos]
          field_simp [hcos_pos.ne']
          calc
            (u.re + 1) * Real.sin u.im =
                (Real.exp u.re * Real.cos u.im) * Real.sin u.im := by rw [hre]
            _ = (Real.exp u.re * Real.sin u.im) * Real.cos u.im := by ring
            _ = u.im * Real.cos u.im := by rw [him]
          ring
        have hlt_tan := Real.lt_tan him_pos him_half_pi
        have htan_pos := Real.tan_pos_of_pos_of_lt_pi_div_two him_pos him_half_pi
        nlinarith
      have hexp_lt : Real.exp u.re < 1 := Real.exp_lt_one_iff.mpr hre_neg
      have hproduct_lt : Real.exp u.re * Real.sin u.im < Real.sin u.im := by
        simpa using mul_lt_mul_of_pos_right hexp_lt hsin_pos
      linarith [Real.sin_lt him_pos]
  have hexp_eq : Real.exp u.re = u.re + 1 := by
    simpa [him_zero] using hre
  have hre_zero : u.re = 0 := by
    by_contra hre_ne
    linarith [Real.add_one_lt_exp hre_ne]
  apply Complex.ext
  · simpa using hre_zero
  · simpa using him_zero

/-- The origin is the only zero of `exp(u)-u-1` in the first horizontal saddle strip. -/
theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff_of_abs_im_lt_two_pi
    {u : ℂ} (hu : |u.im| < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase u = 0 ↔ u = 0 := by
  constructor
  · intro hphase
    by_cases him : 0 ≤ u.im
    · exact deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_of_im_nonneg
        him (lt_of_le_of_lt (le_abs_self _) hu) hphase
    · have hconj_im_nonneg : 0 ≤ (conj u).im := by
        simp only [Complex.conj_im]
        exact (neg_pos.mpr (lt_of_not_ge him)).le
      have hconj_im_lt : (conj u).im < 2 * Real.pi := by
        simp only [Complex.conj_im]
        exact lt_of_le_of_lt (neg_le_abs _) hu
      have hconj_phase :
          deBruijnNewmanPolymathBoydComplexSaddlePhase (conj u) = 0 := by
        rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_conj, hphase]
        simp
      have hconj := deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_of_im_nonneg
        hconj_im_nonneg hconj_im_lt hconj_phase
      have := congrArg conj hconj
      simpa using this
  · rintro rfl
    exact deBruijnNewmanPolymathBoydComplexSaddlePhase_zero

theorem isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain :
    IsOpen deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  exact (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).inter
    (isOpen_lt
      (continuous_norm.comp continuous_deBruijnNewmanPolymathBoydComplexSaddlePhase)
      continuous_const)

/-- The entire Boyd phase is open, by the complex open mapping theorem. -/
theorem isOpenMap_deBruijnNewmanPolymathBoydComplexSaddlePhase :
    IsOpenMap deBruijnNewmanPolymathBoydComplexSaddlePhase := by
  have hanalytic : AnalyticOnNhd ℂ deBruijnNewmanPolymathBoydComplexSaddlePhase univ :=
    fun u _ => deBruijnNewmanPolymathBoydComplexSaddlePhase_analyticAt u
  rcases hanalytic.is_constant_or_isOpenMap with hconstant | hopen
  · rcases hconstant with ⟨w, hw⟩
    have hphase_one_ne : deBruijnNewmanPolymathBoydComplexSaddlePhase 1 ≠ 0 := by
      intro hzero
      have hreal := congrArg Complex.re hzero
      simp [deBruijnNewmanPolymathBoydComplexSaddlePhase, Complex.exp_re] at hreal
      linarith [Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)]
    exact (hphase_one_ne (by simpa using (hw 1).trans (hw 0).symm)).elim
  · exact hopen

/-- The proper first-strip phase map is also open. -/
theorem isOpenMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    IsOpenMap deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  apply (isOpen_ball.isOpenEmbedding_subtypeVal).isOpenMap_iff.mpr
  change IsOpenMap (fun u : deBruijnNewmanPolymathBoydOriginPhaseDomain =>
    deBruijnNewmanPolymathBoydComplexSaddlePhase u)
  exact isOpenMap_deBruijnNewmanPolymathBoydComplexSaddlePhase.restrict
    isOpen_deBruijnNewmanPolymathBoydOriginPhaseDomain

/-- The origin, as a point of the first-strip phase source domain. -/
def deBruijnNewmanPolymathBoydOriginPhaseDomainZero :
    deBruijnNewmanPolymathBoydOriginPhaseDomain :=
  ⟨0, by
    constructor
    · simpa using (show (0 : ℝ) < 2 * Real.pi by positivity)
    · rw [deBruijnNewmanPolymathBoydComplexSaddlePhase_zero, norm_zero]
      positivity⟩

/-- Zero, as a point of the open target phase disk. -/
def deBruijnNewmanPolymathBoydOpenPhaseDiskZero :
    deBruijnNewmanPolymathBoydOpenPhaseDisk :=
  ⟨0, by
    rw [deBruijnNewmanPolymathBoydOpenPhaseDisk, mem_ball, dist_self]
    positivity⟩

theorem deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_zero :
    deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
        {deBruijnNewmanPolymathBoydOpenPhaseDiskZero} =
      {deBruijnNewmanPolymathBoydOriginPhaseDomainZero} := by
  ext u
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hu
    apply Subtype.ext
    apply (deBruijnNewmanPolymathBoydComplexSaddlePhase_eq_zero_iff_of_abs_im_lt_two_pi
      u.property.1).mp
    simpa [deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero] using congrArg Subtype.val hu
  · intro hu
    subst u
    apply Subtype.ext
    simp [deBruijnNewmanPolymathBoydPhaseOnOriginDomain,
      deBruijnNewmanPolymathBoydOpenPhaseDiskZero,
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero]

private theorem isConnected_deBruijnNewmanPolymathBoydOpenPhaseDisk :
    IsConnected deBruijnNewmanPolymathBoydOpenPhaseDisk := by
  rw [deBruijnNewmanPolymathBoydOpenPhaseDisk]
  exact (convex_ball (0 : ℂ) (2 * Real.pi)).isConnected
    ⟨0, mem_ball_self (by positivity)⟩

/-- The first-strip phase domain is exactly one connected origin component. -/
theorem isConnected_deBruijnNewmanPolymathBoydOriginPhaseDomain :
    IsConnected deBruijnNewmanPolymathBoydOriginPhaseDomain := by
  letI : ConnectedSpace deBruijnNewmanPolymathBoydOpenPhaseDisk :=
    Subtype.connectedSpace isConnected_deBruijnNewmanPolymathBoydOpenPhaseDisk
  have hopen := isOpenMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain
  have hclosed := isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain.isClosedMap
  have hfiber :
      (deBruijnNewmanPolymathBoydPhaseOnOriginDomain ⁻¹'
        {deBruijnNewmanPolymathBoydOpenPhaseDiskZero}).Finite := by
    rw [deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_zero]
    exact finite_singleton _
  letI : Finite (ConnectedComponents deBruijnNewmanPolymathBoydOriginPhaseDomain) :=
    hopen.finite_connectedComponents_of_finite_preimage_singleton_of_connectedSpace
      hclosed hfiber
  letI : Fintype (ConnectedComponents deBruijnNewmanPolymathBoydOriginPhaseDomain) :=
    Fintype.ofFinite _
  have hcomponents :
      (Fintype.card (ConnectedComponents deBruijnNewmanPolymathBoydOriginPhaseDomain) : ENat) ≤
        1 := by
    simpa [ENat.card_eq_coe_fintype_card,
      deBruijnNewmanPolymathBoydPhaseOnOriginDomain_preimage_zero] using
      hopen.enatCard_connectedComponents_le_encard_preimage_singleton hclosed
        deBruijnNewmanPolymathBoydOpenPhaseDiskZero
  have hcomponents_nat :
      Fintype.card (ConnectedComponents deBruijnNewmanPolymathBoydOriginPhaseDomain) ≤ 1 := by
    exact_mod_cast hcomponents
  letI : Subsingleton (ConnectedComponents deBruijnNewmanPolymathBoydOriginPhaseDomain) :=
    Fintype.card_le_one_iff_subsingleton.mp hcomponents_nat
  letI : PreconnectedSpace deBruijnNewmanPolymathBoydOriginPhaseDomain :=
    preconnectedSpace_iff_connectedComponent.mpr fun x => by
      apply eq_univ_of_forall
      intro y
      have hxy : connectedComponent x = connectedComponent y :=
        ConnectedComponents.coe_eq_coe.mp
          (Subsingleton.elim
            (x : ConnectedComponents deBruijnNewmanPolymathBoydOriginPhaseDomain) y)
      rw [hxy]
      exact mem_connectedComponent
  exact isConnected_iff_connectedSpace.mpr
    { toPreconnectedSpace := inferInstance
      toNonempty := ⟨deBruijnNewmanPolymathBoydOriginPhaseDomainZero⟩ }

/-- The first-strip proper phase map covers the full open phase disk. -/
theorem surjective_deBruijnNewmanPolymathBoydPhaseOnOriginDomain :
    Function.Surjective deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
  letI : ConnectedSpace deBruijnNewmanPolymathBoydOpenPhaseDisk :=
    Subtype.connectedSpace isConnected_deBruijnNewmanPolymathBoydOpenPhaseDisk
  have hopen := isOpenMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain
  have hclosed := isProperMap_deBruijnNewmanPolymathBoydPhaseOnOriginDomain.isClosedMap
  have hrange_clopen : IsClopen (range deBruijnNewmanPolymathBoydPhaseOnOriginDomain) := by
    constructor
    · rw [← image_univ]
      exact hclosed univ isClosed_univ
    · rw [← image_univ]
      exact hopen univ isOpen_univ
  have hrange_nonempty :
      (range deBruijnNewmanPolymathBoydPhaseOnOriginDomain).Nonempty :=
    ⟨deBruijnNewmanPolymathBoydPhaseOnOriginDomain
        deBruijnNewmanPolymathBoydOriginPhaseDomainZero,
      deBruijnNewmanPolymathBoydOriginPhaseDomainZero, rfl⟩
  have hrange_eq := hrange_clopen.eq_univ hrange_nonempty
  intro z
  have hz : z ∈ range deBruijnNewmanPolymathBoydPhaseOnOriginDomain := by
    rw [hrange_eq]
    exact mem_univ z
  exact hz

end

end LeanLab.Riemann
