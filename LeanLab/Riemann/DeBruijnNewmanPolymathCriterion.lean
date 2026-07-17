import LeanLab.Riemann.DeBruijnNewmanDynamics
import LeanLab.Riemann.DeBruijnNewmanGeneralStrip

set_option linter.style.header false

/-!
# Polymath zero-free-region criterion

This file formalizes the three closed zero-free regions used in Polymath Proposition 3.3 and
develops the boundary and zero-dynamics infrastructure needed by its first-contact proof.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The time-zero compact region in Polymath Proposition 3.3. -/
def deBruijnNewmanPolymathInitialRegionZeroFree (t0 X y0 : ℝ) : Prop :=
  ∀ x y : ℝ,
    0 ≤ x → x ≤ X →
    Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
    deBruijnNewmanH 0 ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- The terminal asymptotic region in Polymath Proposition 3.3. -/
def deBruijnNewmanPolymathFinalRegionZeroFree (t0 X y0 : ℝ) : Prop :=
  ∀ x y : ℝ,
    X + Real.sqrt (1 - y0 ^ 2) ≤ x →
    y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
    deBruijnNewmanH t0 ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- The spacetime barrier region in Polymath Proposition 3.3. -/
def deBruijnNewmanPolymathBarrierRegionZeroFree (t0 X y0 : ℝ) : Prop :=
  ∀ t x y : ℝ,
    0 ≤ t → t ≤ t0 →
    X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
    Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y →
    y ≤ Real.sqrt (1 - 2 * t) →
    deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- The moving lower boundary in the Polymath first-contact argument. -/
def deBruijnNewmanPolymathBoundaryHeight (t0 y0 t : ℝ) : ℝ :=
  Real.sqrt (y0 ^ 2 + 2 * (t0 - t))

/-- Compact spacetime witnesses to failure of the moving zero-free region. -/
def deBruijnNewmanPolymathBadWitnesses (t0 X y0 : ℝ) :
    Set ((ℝ × ℝ) × ℝ) :=
  Icc (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ((t0, X), 1) ∩
    {p | deBruijnNewmanPolymathBoundaryHeight t0 y0 p.1.1 ≤ p.2} ∩
    {p | deBruijnNewmanH p.1.1 ((p.1.2 : ℂ) + (p.2 : ℂ) * I) = 0}

/-- Times at which the compact moving region contains a zero. -/
def deBruijnNewmanPolymathBadTimes (t0 X y0 : ℝ) : Set ℝ :=
  (fun p : (ℝ × ℝ) × ℝ ↦ p.1.1) ''
    deBruijnNewmanPolymathBadWitnesses t0 X y0

theorem isClosed_deBruijnNewmanPolymathBadWitnesses (t0 X y0 : ℝ) :
    IsClosed (deBruijnNewmanPolymathBadWitnesses t0 X y0) := by
  have hheight : Continuous
      (fun p : (ℝ × ℝ) × ℝ ↦ deBruijnNewmanPolymathBoundaryHeight t0 y0 p.1.1) := by
    unfold deBruijnNewmanPolymathBoundaryHeight
    fun_prop
  have hy : Continuous (fun p : (ℝ × ℝ) × ℝ ↦ p.2) := by fun_prop
  have hpoint : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (p.1.1, (p.1.2 : ℂ) + (p.2 : ℂ) * I)) := by
    fun_prop
  have hzero : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      deBruijnNewmanH p.1.1 ((p.1.2 : ℂ) + (p.2 : ℂ) * I)) :=
    continuous_deBruijnNewmanH_joint.comp hpoint
  unfold deBruijnNewmanPolymathBadWitnesses
  exact isClosed_Icc.inter (isClosed_le hheight hy) |>.inter
    (isClosed_eq hzero continuous_const)

theorem isCompact_deBruijnNewmanPolymathBadWitnesses (t0 X y0 : ℝ) :
    IsCompact (deBruijnNewmanPolymathBadWitnesses t0 X y0) := by
  exact isCompact_Icc.of_isClosed_subset
    (isClosed_deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (fun _ hp ↦ hp.1.1)

theorem isCompact_deBruijnNewmanPolymathBadTimes (t0 X y0 : ℝ) :
    IsCompact (deBruijnNewmanPolymathBadTimes t0 X y0) := by
  exact (isCompact_deBruijnNewmanPolymathBadWitnesses t0 X y0).image
    (by fun_prop)

/-- If a bad spacetime witness exists, then there is an earliest bad time. -/
theorem exists_deBruijnNewmanPolymath_firstBadTime
    {t0 X y0 : ℝ}
    (hbad : (deBruijnNewmanPolymathBadWitnesses t0 X y0).Nonempty) :
    ∃ t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0,
      ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t := by
  have htimes : (deBruijnNewmanPolymathBadTimes t0 X y0).Nonempty := by
    rcases hbad with ⟨p, hp⟩
    exact ⟨p.1.1, ⟨p, hp, rfl⟩⟩
  obtain ⟨t1, ht1, hmin⟩ :=
    (isCompact_deBruijnNewmanPolymathBadTimes t0 X y0).exists_isMinOn
      htimes continuous_id.continuousOn
  exact ⟨t1, ht1, hmin⟩

theorem mem_deBruijnNewmanPolymathBadWitnesses_iff
    {t0 X y0 : ℝ} {p : (ℝ × ℝ) × ℝ} :
    p ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0 ↔
      0 ≤ p.1.1 ∧ p.1.1 ≤ t0 ∧
      0 ≤ p.1.2 ∧ p.1.2 ≤ X ∧
      0 ≤ p.2 ∧ p.2 ≤ 1 ∧
      deBruijnNewmanPolymathBoundaryHeight t0 y0 p.1.1 ≤ p.2 ∧
      deBruijnNewmanH p.1.1 ((p.1.2 : ℂ) + (p.2 : ℂ) * I) = 0 := by
  simp only [deBruijnNewmanPolymathBadWitnesses, mem_inter_iff, mem_Icc,
    mem_setOf_eq]
  constructor
  · rintro ⟨⟨⟨hlow, hupp⟩, hheight⟩, hzero⟩
    exact ⟨hlow.1.1, hupp.1.1, hlow.1.2, hupp.1.2, hlow.2, hupp.2,
      hheight, hzero⟩
  · rintro ⟨ht0, htt0, hx0, hxX, hy0, hy1, hheight, hzero⟩
    exact ⟨⟨⟨⟨⟨ht0, hx0⟩, hy0⟩, ⟨⟨htt0, hxX⟩, hy1⟩⟩, hheight⟩, hzero⟩

/-- The initial certificate excludes time zero from the compact bad-time set. -/
theorem deBruijnNewmanPolymathBadTime_pos_of_initial
    {t0 X y0 t : ℝ}
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (ht : t ∈ deBruijnNewmanPolymathBadTimes t0 X y0) :
    0 < t := by
  rcases ht with ⟨p, hp, rfl⟩
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht0, _htt0, hx0, hxX, _hy0, hy1, hheight, hzero⟩
  have htNe : p.1.1 ≠ 0 := by
    intro htZero
    have hheight0 : Real.sqrt (y0 ^ 2 + 2 * t0) ≤ p.2 := by
      simpa [deBruijnNewmanPolymathBoundaryHeight, htZero] using hheight
    exact hinit p.1.2 p.2 hx0 hxX hheight0 hy1 (by simpa only [htZero] using hzero)
  exact lt_of_le_of_ne ht0 (Ne.symm htNe)

/-- A bad witness cannot lie on either vertical side of the Polymath rectangle. -/
theorem deBruijnNewmanPolymathBadWitness_re_mem_Ioo
    {t0 X y0 : ℝ} (hthalf : t0 ≤ (1 : ℝ) / 2)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0) :
    p.1.2 ∈ Ioo 0 X := by
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht0, htt0, hx0, hxX, _hy0, _hy1, hheight, hzero⟩
  have hxNeZero : p.1.2 ≠ 0 := by
    intro hxZero
    have hno := haxis p.1.1 p.2
    apply hno
    simpa only [hxZero, Complex.ofReal_zero, zero_add] using hzero
  have hxNeX : p.1.2 ≠ X := by
    intro hxEq
    have htHalf : p.1.1 ≤ (1 : ℝ) / 2 := htt0.trans hthalf
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 htHalf hzero
    have him : (((p.1.2 : ℂ) + (p.2 : ℂ) * I).im) = p.2 := by simp
    rw [him] at hstrip
    have hrad : 0 ≤ 1 - 2 * p.1.1 := by linarith
    have hyTop : p.2 ≤ Real.sqrt (1 - 2 * p.1.1) := by
      nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 - 2 * p.1.1)]
    have hno := hbarrier p.1.1 p.1.2 p.2 ht0 htt0
      (show X ≤ p.1.2 by rw [hxEq])
      (show p.1.2 ≤ X + Real.sqrt (1 - y0 ^ 2) by
        rw [hxEq]
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _))
      hheight hyTop
    exact hno hzero
  exact ⟨lt_of_le_of_ne hx0 (Ne.symm hxNeZero),
    lt_of_le_of_ne hxX hxNeX⟩

/-- At the earliest bad time, every bad witness lies on the moving lower boundary.
The proof uses compactness and multiplicity-free zero persistence, so it applies before the
simple/repeated split. -/
theorem deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    {t0 X y0 t1 x y : ℝ} (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0) :
    y = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
  have ht1Bad : t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t1, x), y), hp, rfl⟩
  have ht1Pos : 0 < t1 :=
    deBruijnNewmanPolymathBadTime_pos_of_initial hinit ht1Bad
  rcases mem_deBruijnNewmanPolymathBadWitnesses_iff.mp hp with
    ⟨ht10, ht1t0, _hx0, _hxX, hy0, _hy1, hheight, hzero⟩
  have hxInterior : x ∈ Ioo 0 X :=
    deBruijnNewmanPolymathBadWitness_re_mem_Ioo hthalf haxis hbarrier hp
  apply le_antisymm
  · by_contra hyNot
    have hYlt : deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 < y :=
      lt_of_not_ge hyNot
    have ht1Half : t1 ≤ (1 : ℝ) / 2 := ht1t0.trans hthalf
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht10 ht1Half hzero
    have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
    rw [him] at hstrip
    have hyNonneg : 0 ≤ y := hy0
    have hyOne : y < 1 := by
      nlinarith [sq_nonneg (y - 1)]
    let c : ℝ := (deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 + y) / 2
    have hYc : deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 < c := by
      dsimp only [c]
      linarith
    have hcy : c < y := by
      dsimp only [c]
      linarith
    let U : Set ℂ := {z | 0 < z.re ∧ z.re < X ∧ c < z.im ∧ z.im < 1}
    have hUOpen : IsOpen U := by
      simpa only [U, setOf_and] using
        (isOpen_lt continuous_const Complex.continuous_re).inter
          ((isOpen_lt Complex.continuous_re continuous_const).inter
            ((isOpen_lt continuous_const Complex.continuous_im).inter
              (isOpen_lt Complex.continuous_im continuous_const)))
    let z0 : ℂ := (x : ℂ) + (y : ℂ) * I
    have hz0U : z0 ∈ U := by
      simpa [z0, U] using ⟨hxInterior.1, hxInterior.2, hcy, hyOne⟩
    obtain ⟨R, hR, hboundary, hballU⟩ :=
      exists_deBruijnNewmanH_isolating_closedBall_subset
        hzero (hUOpen.mem_nhds hz0U)
    have hpersist := eventually_exists_deBruijnNewmanH_zero_mem_closedBall
      hR hzero hboundary
    have hYcont : ContinuousAt
        (deBruijnNewmanPolymathBoundaryHeight t0 y0) t1 := by
      unfold deBruijnNewmanPolymathBoundaryHeight
      fun_prop
    have hYevent : ∀ᶠ t in 𝓝 t1,
        deBruijnNewmanPolymathBoundaryHeight t0 y0 t < c :=
      hYcont.eventually (Iio_mem_nhds hYc)
    have hevent : ∀ᶠ t in 𝓝 t1,
        0 < t ∧ deBruijnNewmanPolymathBoundaryHeight t0 y0 t < c ∧
          ∃ z ∈ Metric.closedBall z0 R, deBruijnNewmanH t z = 0 := by
      filter_upwards [Ioi_mem_nhds ht1Pos, hYevent, hpersist] with t ht hY hz
      exact ⟨ht, hY, hz⟩
    obtain ⟨t, htt1, ht, hYt, z, hzBall, hzZero⟩ := hevent.exists_lt
    have hzU := hballU hzBall
    have hzPoint : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    have htLe : t ≤ t0 := (le_of_lt htt1).trans ht1t0
    have hcNonneg : 0 ≤ c := by
      dsimp only [c]
      have hYnonneg : 0 ≤ deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
        exact Real.sqrt_nonneg _
      linarith
    have htBadWitness : ((t, z.re), z.im) ∈
        deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
      rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
      exact ⟨ht.le, htLe, hzU.1.le, hzU.2.1.le,
        hcNonneg.trans (le_of_lt hzU.2.2.1), hzU.2.2.2.le,
        (hYt.trans hzU.2.2.1).le, by simpa only [hzPoint] using hzZero⟩
    have htBad : t ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
      ⟨((t, z.re), z.im), htBadWitness, rfl⟩
    exact (not_lt_of_ge (hmin t htBad)) htt1
  · exact hheight

private theorem cos_mul_I_mul_ofReal (y u : ℝ) :
    Complex.cos (((y : ℂ) * I) * (u : ℂ)) = (Real.cosh (y * u) : ℂ) := by
  rw [show ((y : ℂ) * I) * (u : ℂ) = ((y * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh]

private theorem integrableOn_deBruijnNewmanImaginaryAxisIntegrand (t y : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦
        Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh (y * u))
      (Ioi 0) := by
  have hre := (integrableOn_dbnHeatCosIntegrand t ((y : ℂ) * I)).re
  apply hre.congr
  filter_upwards with u
  rw [cos_mul_I_mul_ofReal, ← Complex.ofReal_mul]
  exact RCLike.ofReal_re _

/-- The source heat family is strictly positive on the entire imaginary axis. -/
theorem deBruijnNewmanH_mul_I_re_pos (t y : ℝ) :
    0 < (deBruijnNewmanH t ((y : ℂ) * I)).re := by
  let f : ℝ → ℝ := fun u ↦
    Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh (y * u)
  have hfInt : Integrable f (volume.restrict (Ioi 0)) := by
    change IntegrableOn f (Ioi 0)
    exact integrableOn_deBruijnNewmanImaginaryAxisIntegrand t y
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos
      (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.le))
      (Real.cosh_pos _)).le
  have hsupport : 0 < (volume.restrict (Ioi 0)) (Function.support f) := by
    have hsubset : Ioo (0 : ℝ) 1 ⊆ Function.support f := by
      intro u hu
      exact (mul_pos
        (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.1.le))
        (Real.cosh_pos _)).ne'
    have hmeasure : 0 < (volume.restrict (Ioi 0)) (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      simp only [Ioo_inter_Ioi, max_eq_left (by norm_num : (0 : ℝ) ≤ 0),
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
      norm_num
    exact hmeasure.trans_le (measure_mono hsubset)
  have hfPos : 0 < ∫ u, f u ∂volume.restrict (Ioi 0) :=
    (integral_pos_iff_support_of_nonneg_ae hfNonneg hfInt).2 hsupport
  have hH : deBruijnNewmanH t ((y : ℂ) * I) =
      ((∫ u, f u ∂volume.restrict (Ioi 0) : ℝ) : ℂ) := by
    rw [deBruijnNewmanH, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with u
    rw [cos_mul_I_mul_ofReal]
    simp only [f]
    push_cast
    rfl
  rw [hH]
  simpa using hfPos

/-- There are no source heat-family zeros on the imaginary axis at any heat time. -/
theorem deBruijnNewmanH_mul_I_ne_zero (t y : ℝ) :
    deBruijnNewmanH t ((y : ℂ) * I) ≠ 0 := by
  intro hzero
  have hpos := deBruijnNewmanH_mul_I_re_pos t y
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- The time-zero region certificate remains valid after deleting its redundant upper boundary. -/
theorem deBruijnNewmanPolymathInitialRegionZeroFree.above
    {t0 X y0 : ℝ}
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxX : x ≤ X)
    (hy : Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y) :
    deBruijnNewmanH 0 ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hy1 : y ≤ 1
  · exact hinit x y hx0 hxX hy hy1
  intro hzero
  have hstrip := deBruijnNewmanH_zero_im_mem_Ioo hzero
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hstrip
  exact (not_lt_of_ge (lt_of_not_ge hy1).le) hstrip.2

/-- The terminal region certificate remains valid after deleting its strip-implied upper bound. -/
theorem deBruijnNewmanPolymathFinalRegionZeroFree.above
    {t0 X y0 : ℝ} (ht0 : 0 ≤ t0) (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hfinal : deBruijnNewmanPolymathFinalRegionZeroFree t0 X y0)
    {x y : ℝ} (hx : X + Real.sqrt (1 - y0 ^ 2) ≤ x) (hy : y0 ≤ y)
    (hy0 : 0 ≤ y0) :
    deBruijnNewmanH t0 ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hyTop : y ≤ Real.sqrt (1 - 2 * t0)
  · exact hfinal x y hx hy hyTop
  intro hzero
  have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 hthalf hzero
  have hrad : 0 ≤ 1 - 2 * t0 := by linarith
  have hyPos : 0 ≤ y := hy0.trans hy
  have hsqrtLt : Real.sqrt (1 - 2 * t0) < y := lt_of_not_ge hyTop
  have hySq : 1 - 2 * t0 < y ^ 2 := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 - 2 * t0)]
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hstrip
  exact (not_lt_of_ge hstrip) hySq

/-- The spacetime barrier certificate remains valid after deleting its strip-implied upper bound. -/
theorem deBruijnNewmanPolymathBarrierRegionZeroFree.above
    {t0 X y0 : ℝ}
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    {t x y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ t0) (hthalf : t ≤ (1 : ℝ) / 2)
    (hxX : X ≤ x) (hx : x ≤ X + Real.sqrt (1 - y0 ^ 2))
    (hy : Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y) :
    deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hyTop : y ≤ Real.sqrt (1 - 2 * t)
  · exact hbarrier t x y ht0 ht hxX hx hy hyTop
  intro hzero
  have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 hthalf hzero
  have hrad : 0 ≤ 1 - 2 * t := by linarith
  have hyNonneg : 0 ≤ y := (Real.sqrt_nonneg _).trans hy
  have hsqrtLt : Real.sqrt (1 - 2 * t) < y := lt_of_not_ge hyTop
  have hySq : 1 - 2 * t < y ^ 2 := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 - 2 * t)]
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hstrip
  exact (not_lt_of_ge hstrip) hySq

section

private abbrev PolymathHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ _ RCLike.toInnerProductSpaceReal.toModule _ _ f f' x

theorem hasDerivAt_deBruijnNewmanPolymathBoundaryHeight
    {t0 y0 t : ℝ}
    (hpos : 0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t) :
    PolymathHasDerivAt (deBruijnNewmanPolymathBoundaryHeight t0 y0)
      (-1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t) t := by
  unfold deBruijnNewmanPolymathBoundaryHeight at hpos ⊢
  let q : ℝ → ℝ := fun s ↦ y0 ^ 2 + 2 * (t0 - s)
  have hq : PolymathHasDerivAt q (-2) t := by
    dsimp only [q]
    have hsub : PolymathHasDerivAt (fun s : ℝ ↦ t0 - s) (-1) t := by
      have hraw := (hasDerivAt_const (x := t) (c := t0)).sub (hasDerivAt_id t)
      have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) - 1 = -1)
      apply hraw'.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun s ↦ by simp)
    have hmul : PolymathHasDerivAt (fun s : ℝ ↦ 2 * (t0 - s)) (-2) t := by
      simpa only [mul_neg, mul_one] using hsub.const_mul 2
    have hraw := (hasDerivAt_const (x := t) (c := y0 ^ 2)).add hmul
    have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) + -2 = -2)
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s ↦ by simp)
  have hqPos : 0 < q t := by
    apply Real.sqrt_pos.1
    simpa only [q, deBruijnNewmanPolymathBoundaryHeight] using hpos
  have hsqrt := hq.sqrt hqPos.ne'
  have hsqrtPos : 0 < Real.sqrt (q t) := Real.sqrt_pos.2 hqPos
  have hderiv : -2 / (2 * Real.sqrt (q t)) = -1 / Real.sqrt (q t) := by
    field_simp [hsqrtPos.ne']
  simpa only [q] using hsqrt.congr_deriv hderiv

private theorem eventually_lt_on_left_of_hasDerivAt_lt
    {f g : ℝ → ℝ} {t f' g' : ℝ}
    (hf : PolymathHasDerivAt f f' t) (hg : PolymathHasDerivAt g g' t)
    (hderiv : f' < g') (hvalue : f t = g t) :
    ∀ᶠ s in 𝓝 t, s < t → g s < f s := by
  have hq : PolymathHasDerivAt (f - g) (f' - g') t := hf.sub hg
  have hslopeWithin : ∀ᶠ s in 𝓝[≠] t, slope (f - g) t s < 0 :=
    hq.tendsto_slope.eventually (Iio_mem_nhds (sub_neg.mpr hderiv))
  have hslope : ∀ᶠ s in 𝓝 t, s ≠ t → slope (f - g) t s < 0 :=
    eventually_nhdsWithin_iff.mp hslopeWithin
  filter_upwards [hslope] with s hs
  intro hst
  have hslopeNeg := hs hst.ne
  rw [slope_def_field] at hslopeNeg
  have hnum : 0 < (f - g) s - (f - g) t := by
    have hmul := (div_lt_iff_of_neg (sub_neg.mpr hst)).mp hslopeNeg
    simpa only [zero_mul] using hmul
  simp only [Pi.sub_apply] at hnum
  rw [hvalue] at hnum
  linarith

/-- The simple-contact branch reduces exactly to the strict imaginary force inequality from
Polymath Proposition 3.3. If that inequality holds, minimality of the bad time is contradicted. -/
theorem deBruijnNewmanPolymath_firstBadWitness_not_simple_of_force_lt
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0) (ht1Pos : 0 < t1)
    (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hxInterior : x ∈ Ioo 0 X)
    (hcontact : y = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1)
    (hforce :
      (2 * deBruijnNewmanRegularizedZeroForce t1 ((x : ℂ) + (y : ℂ) * I)).im <
        -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) :
    deriv (deBruijnNewmanH t1) ((x : ℂ) + (y : ℂ) * I) = 0 := by
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht10, ht1t0, _hx0, _hxX, _hyNonneg, hy1, _hheight, hzero⟩
  by_contra hsimple
  let z0 : ℂ := (x : ℂ) + (y : ℂ) * I
  obtain ⟨z, hzAnchor, hzTend, hzDeriv, hzZero, _hzUnique⟩ :=
    exists_deBruijnNewman_localComplexSimpleZeroPath hzero hsimple
  have hYPos : 0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    have hrad : 0 < y0 ^ 2 + 2 * (t0 - t1) := by
      nlinarith [sq_pos_of_pos hy0]
    simpa only [deBruijnNewmanPolymathBoundaryHeight] using Real.sqrt_pos.2 hrad
  have hYDeriv := hasDerivAt_deBruijnNewmanPolymathBoundaryHeight hYPos
  have hzImDeriv : PolymathHasDerivAt (fun t ↦ (z t).im)
      (2 * deBruijnNewmanRegularizedZeroForce t1 z0).im t1 := by
    have hcomp := Complex.imCLM.hasFDerivAt.comp t1 hzDeriv.hasFDerivAt
    simpa [Function.comp_def, Complex.imCLM_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, z0] using hcomp.hasDerivAt
  have hzImAnchor : (z t1).im =
      deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    rw [hzAnchor]
    simp [hcontact]
  have habove : ∀ᶠ t in 𝓝 t1, t < t1 →
      deBruijnNewmanPolymathBoundaryHeight t0 y0 t < (z t).im :=
    eventually_lt_on_left_of_hasDerivAt_lt hzImDeriv hYDeriv hforce hzImAnchor
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < X ∧ w.im < 1}
  have hUOpen : IsOpen U := by
    simpa only [U, setOf_and] using
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt Complex.continuous_im continuous_const))
  have hyOne : y < 1 := by
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht10 (ht1t0.trans hthalf) hzero
    have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
    rw [him] at hstrip
    have hyPos : 0 < y := by rw [hcontact]; exact hYPos
    nlinarith [sq_nonneg (y - 1)]
  have hz0U : z0 ∈ U := by
    simpa [z0, U] using ⟨hxInterior.1, hxInterior.2, hyOne⟩
  have hzEventuallyU : ∀ᶠ t in 𝓝 t1, z t ∈ U :=
    hzTend.eventually (hUOpen.mem_nhds hz0U)
  have hevent : ∀ᶠ t in 𝓝 t1,
      0 < t ∧ z t ∈ U ∧ deBruijnNewmanH t (z t) = 0 ∧
        (t < t1 → deBruijnNewmanPolymathBoundaryHeight t0 y0 t < (z t).im) := by
    filter_upwards [Ioi_mem_nhds ht1Pos, hzEventuallyU,
      hzZero, habove] with t ht hzU hzeroT haboveT
    exact ⟨ht, hzU, hzeroT, haboveT⟩
  obtain ⟨t, htt1, ht, hzU, hzeroT, haboveT⟩ := hevent.exists_lt
  have htLe : t ≤ t0 := (le_of_lt htt1).trans ht1t0
  have hzPoint : ((z t).re : ℂ) + ((z t).im : ℂ) * I = z t := by
    apply Complex.ext <;> simp
  have htWitness : ((t, (z t).re), (z t).im) ∈
      deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
    rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
    have haboveT' := haboveT htt1
    exact ⟨ht.le, htLe, hzU.1.le, hzU.2.1.le,
      (Real.sqrt_nonneg _).trans haboveT'.le, hzU.2.2.le, haboveT'.le,
      by simpa only [hzPoint] using hzeroT⟩
  have htBad : t ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t, (z t).re), (z t).im), htWitness, rfl⟩
  exact (not_lt_of_ge (hmin t htBad)) htt1

/-- The weak consequence of backward Hermite splitting needed at a repeated first contact. The
square-root displacement from the source theorem dominates every fixed linear speed. -/
def deBruijnNewmanHasBackwardUpperLinearEscape (t : ℝ) (z : ℂ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ U ∈ 𝓝 z,
    ∀ᶠ s in 𝓝[<] t,
      ∃ w ∈ U, deBruijnNewmanH s w = 0 ∧ z.im + C * (t - s) < w.im

/-- A first-contact zero cannot have the backward upper-escape property supplied by repeated-zero
Hermite splitting. This closes the full topological consumer of the repeated branch. -/
theorem deBruijnNewmanPolymath_firstBadWitness_not_backwardUpperLinearEscape
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0) (ht1Pos : 0 < t1)
    (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hxInterior : x ∈ Ioo 0 X)
    (hcontact : y = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) :
    ¬deBruijnNewmanHasBackwardUpperLinearEscape t1 ((x : ℂ) + (y : ℂ) * I) := by
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht10, ht1t0, _hx0, _hxX, _hyNonneg, _hy1, _hheight, hzero⟩
  intro hescape
  let z0 : ℂ := (x : ℂ) + (y : ℂ) * I
  have hYPos : 0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    have hrad : 0 < y0 ^ 2 + 2 * (t0 - t1) := by
      nlinarith [sq_pos_of_pos hy0]
    simpa only [deBruijnNewmanPolymathBoundaryHeight] using Real.sqrt_pos.2 hrad
  let C : ℝ := 2 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let line : ℝ → ℝ := fun s ↦ y + C * (t1 - s)
  have hsub : PolymathHasDerivAt (fun s : ℝ ↦ t1 - s) (-1) t1 := by
    have hraw := (hasDerivAt_const (x := t1) (c := t1)).sub (hasDerivAt_id t1)
    have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) - 1 = -1)
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s ↦ by simp)
  have hscaled : PolymathHasDerivAt (fun s : ℝ ↦ C * (t1 - s)) (-C) t1 := by
    simpa only [mul_neg, mul_one] using hsub.const_mul C
  have hline : PolymathHasDerivAt line (-C) t1 := by
    have hraw := (hasDerivAt_const (x := t1) (c := y)).add hscaled
    have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) + -C = -C)
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s ↦ by simp [line])
  have hYDeriv := hasDerivAt_deBruijnNewmanPolymathBoundaryHeight hYPos
  have hderiv : -C <
      -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    dsimp only [C]
    have hInv : 0 < 1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by positivity
    rw [show 2 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 =
      2 * (1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) by ring]
    rw [show -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 =
      -(1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) by ring]
    linarith
  have hlineValue : line t1 = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    simp only [line, sub_self, mul_zero, add_zero, hcontact]
  have hlineAbove : ∀ᶠ s in 𝓝 t1, s < t1 →
      deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s :=
    eventually_lt_on_left_of_hasDerivAt_lt hline hYDeriv hderiv hlineValue
  have hyOne : y < 1 := by
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht10 (ht1t0.trans hthalf) hzero
    have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
    rw [him] at hstrip
    have hyPos : 0 < y := by rw [hcontact]; exact hYPos
    nlinarith [sq_nonneg (y - 1)]
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < X ∧ w.im < 1}
  have hUOpen : IsOpen U := by
    simpa only [U, setOf_and] using
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt Complex.continuous_im continuous_const))
  have hz0U : z0 ∈ U := by
    simpa [z0, U] using ⟨hxInterior.1, hxInterior.2, hyOne⟩
  have hsplit := hescape C hC U (hUOpen.mem_nhds hz0U)
  have hlineRaw : ∀ᶠ s in 𝓝[<] t1, s < t1 →
      deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s :=
    hlineAbove.filter_mono inf_le_left
  have hlineWithin : ∀ᶠ s in 𝓝[<] t1,
      deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s := by
    filter_upwards [hlineRaw, eventually_mem_nhdsWithin] with
      s hs hst
    exact hs hst
  have hposN : ∀ᶠ s in 𝓝 t1, 0 < s := Ioi_mem_nhds ht1Pos
  have hposWithin : ∀ᶠ s in 𝓝[<] t1, 0 < s :=
    hposN.filter_mono inf_le_left
  have hevent : ∀ᶠ s in 𝓝[<] t1,
      s < t1 ∧ 0 < s ∧
        deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s ∧
        ∃ w ∈ U, deBruijnNewmanH s w = 0 ∧ z0.im + C * (t1 - s) < w.im := by
    filter_upwards [eventually_mem_nhdsWithin, hposWithin, hlineWithin, hsplit] with
      s hst hs hlineS hsplitS
    exact ⟨hst, hs, hlineS, hsplitS⟩
  obtain ⟨s, hst1, hsPos, hlineS, w, hwU, hwZero, hwEscape⟩ := hevent.exists
  have hlineEq : line s = z0.im + C * (t1 - s) := by
    simp [line, z0]
  have hYw : deBruijnNewmanPolymathBoundaryHeight t0 y0 s < w.im := by
    rw [hlineEq] at hlineS
    exact hlineS.trans hwEscape
  have hsLe : s ≤ t0 := (le_of_lt hst1).trans ht1t0
  have hwPoint : (w.re : ℂ) + (w.im : ℂ) * I = w := by
    apply Complex.ext <;> simp
  have hsWitness : ((s, w.re), w.im) ∈
      deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
    rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
    exact ⟨hsPos.le, hsLe, hwU.1.le, hwU.2.1.le,
      (Real.sqrt_nonneg _).trans hYw.le, hwU.2.2.le, hYw.le,
      by simpa only [hwPoint] using hwZero⟩
  have hsBad : s ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((s, w.re), w.im), hsWitness, rfl⟩
  exact (not_lt_of_ge (hmin s hsBad)) hst1

/-- The exact obstruction pair remaining at a first contact after the force inequality is supplied:
the contact is repeated, but minimality forbids the backward escape predicted by Hermite
splitting. -/
theorem deBruijnNewmanPolymath_firstBadWitness_repeated_obstruction_of_force_lt
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0) (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hforce :
      (2 * deBruijnNewmanRegularizedZeroForce t1 ((x : ℂ) + (y : ℂ) * I)).im <
        -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) :
    deriv (deBruijnNewmanH t1) ((x : ℂ) + (y : ℂ) * I) = 0 ∧
      ¬deBruijnNewmanHasBackwardUpperLinearEscape t1 ((x : ℂ) + (y : ℂ) * I) := by
  have ht1Bad : t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t1, x), y), hp, rfl⟩
  have ht1Pos := deBruijnNewmanPolymathBadTime_pos_of_initial hinit ht1Bad
  have hxInterior :=
    deBruijnNewmanPolymathBadWitness_re_mem_Ioo hthalf haxis hbarrier hp
  have hcontact := deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    hthalf hinit haxis hbarrier hmin hp
  exact ⟨deBruijnNewmanPolymath_firstBadWitness_not_simple_of_force_lt
      hy0 ht1Pos hthalf hmin hp hxInterior hcontact hforce,
    deBruijnNewmanPolymath_firstBadWitness_not_backwardUpperLinearEscape
      hy0 ht1Pos hthalf hmin hp hxInterior hcontact⟩

end

/-- A strict time-`t` canopy feeds directly into the compiled arbitrary-base strip theorem. -/
theorem deBruijnNewmanAllZerosReal_add_half_sq_of_im_abs_lt
    {t y : ℝ} (hy : 0 < y)
    (hcanopy : ∀ z : ℂ, deBruijnNewmanH t z = 0 → |z.im| < y) :
    deBruijnNewmanAllZerosReal (t + y ^ 2 / 2) := by
  apply deBruijnNewmanAllZerosReal_add_half_sq hy.le
  intro z hz
  rcases abs_lt.mp (hcanopy z hz) with ⟨hlower, hupper⟩
  have hprod : 0 < (y - z.im) * (y + z.im) :=
    mul_pos (sub_pos.mpr hupper) (by linarith)
  nlinarith

/-- Exact arithmetic for the second row of Polymath Table 1. -/
theorem deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_endpoint
    (hall : deBruijnNewmanAllZerosReal
      ((93 : ℝ) / 500 + ((16733 : ℝ) / 100000) ^ 2 / 2)) :
    deBruijnNewmanAllZerosReal ((1 : ℝ) / 5) := by
  apply deBruijnNewmanAllZerosReal_mono (t :=
    (93 : ℝ) / 500 + ((16733 : ℝ) / 100000) ^ 2 / 2) (tau := (1 : ℝ) / 5)
  · norm_num
  · exact hall

end

end LeanLab.Riemann
