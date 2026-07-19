import LeanLab.Riemann.DeBruijnNewmanPolymathBoydAdjacentSaddleCauchy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The adjacent zero-real-phase contours for Boyd's Gamma saddle

This module constructs the upper adjacent contour from the origin to `2*pi*I` as the graph of
the inverse of a real order isomorphism. It then proves strict decrease of the imaginary phase
along that contour. No two-dimensional covering or global complex inverse is assumed.
-/

namespace LeanLab.Riemann

open Complex Filter Set
open scoped ComplexConjugate Topology

noncomputable section

/-- The real carrier obtained by solving the zero-real-phase equation for `cos y`. -/
def deBruijnNewmanPolymathBoydAdjacentContourCarrier (x : ℝ) : ℝ :=
  (x + 1) * Real.exp (-x)

theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourCarrier (x : ℝ) :
    HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourCarrier
      (-x * Real.exp (-x)) x := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourCarrier
  have h := ((hasDerivAt_id x).add_const 1).mul
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg)
  have h' := h.congr_deriv (by
    change 1 * Real.exp (-x) + (x + 1) * (Real.exp (-x) * -1) =
      -x * Real.exp (-x)
    ring)
  exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

theorem deriv_deBruijnNewmanPolymathBoydAdjacentContourCarrier (x : ℝ) :
    deriv deBruijnNewmanPolymathBoydAdjacentContourCarrier x =
      -x * Real.exp (-x) :=
  (hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourCarrier x).deriv

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourCarrier :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourCarrier := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourCarrier
  fun_prop

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn :
    StrictMonoOn deBruijnNewmanPolymathBoydAdjacentContourCarrier (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0)
    continuous_deBruijnNewmanPolymathBoydAdjacentContourCarrier.continuousOn
  intro x hx
  rw [interior_Iic] at hx
  rw [deriv_deBruijnNewmanPolymathBoydAdjacentContourCarrier]
  exact mul_pos (neg_pos.mpr hx) (Real.exp_pos _)

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrier_le_one
    {x : ℝ} (hx : x ≤ 0) :
    deBruijnNewmanPolymathBoydAdjacentContourCarrier x ≤ 1 := by
  calc
    deBruijnNewmanPolymathBoydAdjacentContourCarrier x ≤
        deBruijnNewmanPolymathBoydAdjacentContourCarrier 0 :=
      deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn.monotoneOn
        hx (by simp) hx
    _ = 1 := by simp [deBruijnNewmanPolymathBoydAdjacentContourCarrier]

/-- The carrier restricted to its natural lower half-line and codomain. -/
def deBruijnNewmanPolymathBoydAdjacentContourCarrierMap :
    Iic (0 : ℝ) → Iic (1 : ℝ) := fun x =>
  ⟨deBruijnNewmanPolymathBoydAdjacentContourCarrier x,
    deBruijnNewmanPolymathBoydAdjacentContourCarrier_le_one x.property⟩

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrierMap_strictMono :
    StrictMono deBruijnNewmanPolymathBoydAdjacentContourCarrierMap := by
  intro x y hxy
  exact deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn
    x.property y.property hxy

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrierMap_surjective :
    Function.Surjective deBruijnNewmanPolymathBoydAdjacentContourCarrierMap := by
  intro z
  let a : ℝ := z - 2
  have hz : (z : ℝ) ≤ 1 := z.property
  have ha0 : a ≤ 0 := by dsimp [a]; linarith
  have hcarrierA : deBruijnNewmanPolymathBoydAdjacentContourCarrier a ≤ z := by
    have hexp : 1 ≤ Real.exp (2 - (z : ℝ)) := Real.one_le_exp (by linarith)
    have hmul := mul_le_mul_of_nonpos_left hexp (by linarith : (z : ℝ) - 1 ≤ 0)
    dsimp [a]
    rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier]
    calc
      ((z : ℝ) - 2 + 1) * Real.exp (-((z : ℝ) - 2)) =
          ((z : ℝ) - 1) * Real.exp (2 - (z : ℝ)) := by ring
      _ ≤ ((z : ℝ) - 1) * 1 := hmul
      _ ≤ z := by linarith
  have hzmem : (z : ℝ) ∈ Icc
      (deBruijnNewmanPolymathBoydAdjacentContourCarrier a)
      (deBruijnNewmanPolymathBoydAdjacentContourCarrier 0) := by
    refine ⟨hcarrierA, ?_⟩
    rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier]
    norm_num
    exact hz
  obtain ⟨x, hx, hxz⟩ :=
    intermediate_value_Icc ha0
      continuous_deBruijnNewmanPolymathBoydAdjacentContourCarrier.continuousOn hzmem
  refine ⟨⟨x, hx.2⟩, ?_⟩
  apply Subtype.ext
  exact hxz

/-- The carrier is an order isomorphism `(-infinity,0] -> (-infinity,1]`. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourCarrierOrderIso :
    Iic (0 : ℝ) ≃o Iic (1 : ℝ) :=
  StrictMono.orderIsoOfSurjective
    deBruijnNewmanPolymathBoydAdjacentContourCarrierMap
    deBruijnNewmanPolymathBoydAdjacentContourCarrierMap_strictMono
    deBruijnNewmanPolymathBoydAdjacentContourCarrierMap_surjective

/-- A continuous total representative of the inverse carrier, clamped only above `1`. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse (z : ℝ) : ℝ :=
  (deBruijnNewmanPolymathBoydAdjacentContourCarrierOrderIso.symm
    ⟨min z 1, min_le_right z 1⟩).1

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrier_inverse (z : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourCarrier
        (deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse z) = min z 1 := by
  have h := deBruijnNewmanPolymathBoydAdjacentContourCarrierOrderIso.apply_symm_apply
    (⟨min z 1, min_le_right z 1⟩ : Iic (1 : ℝ))
  exact congrArg Subtype.val h

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse_nonpos (z : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse z ≤ 0 :=
  (deBruijnNewmanPolymathBoydAdjacentContourCarrierOrderIso.symm
    ⟨min z 1, min_le_right z 1⟩).property

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse
  exact continuous_subtype_val.comp
    (deBruijnNewmanPolymathBoydAdjacentContourCarrierOrderIso.symm.continuous.comp
      ((continuous_id.min continuous_const).subtype_mk _))

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse_neg
    {z : ℝ} (hz : z < 1) :
    deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse z < 0 := by
  have hle := deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse_nonpos z
  refine lt_of_le_of_ne hle ?_
  intro hzero
  have hcarrier := deBruijnNewmanPolymathBoydAdjacentContourCarrier_inverse z
  rw [hzero] at hcarrier
  simp [deBruijnNewmanPolymathBoydAdjacentContourCarrier, min_eq_left hz.le] at hcarrier
  exact hz.ne hcarrier.symm

theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse
    {z : ℝ} (hz : z < 1) :
    HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse
      (-deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse z *
        Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse z))⁻¹ z := by
  have hxneg := deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse_neg hz
  apply (hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourCarrier
    (deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse z)).of_local_left_inverse
      continuous_deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse.continuousAt
      (mul_ne_zero (neg_ne_zero.mpr hxneg.ne) (Real.exp_ne_zero _))
  filter_upwards [eventually_lt_nhds hz] with w hw
  rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier_inverse, min_eq_left hw.le]

/-- The unique real part of the upper zero-real-phase contour at height `y`. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourRealPart (y : ℝ) : ℝ :=
  deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse (Real.cos y)

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourRealPart :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourRealPart :=
  continuous_deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse.comp Real.continuous_cos

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos (y : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart y ≤ 0 :=
  deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse_nonpos _

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrier_realPart (y : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourCarrier
        (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) = Real.cos y := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourRealPart,
    deBruijnNewmanPolymathBoydAdjacentContourCarrier_inverse,
    min_eq_left (Real.cos_le_one y)]

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_eq (y : ℝ) :
    Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.cos y =
      deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1 := by
  have h := deBruijnNewmanPolymathBoydAdjacentContourCarrier_realPart y
  rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier] at h
  calc
    Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.cos y =
        Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
          ((deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1) *
            Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y)) := by rw [← h]
    _ = deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1 := by
      calc
        Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
            ((deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1) *
              Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y)) =
            (deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1) *
              (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
                Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y)) := by ring
        _ = deBruijnNewmanPolymathBoydAdjacentContourRealPart y + 1 := by
          rw [← Real.exp_add]
          simp

theorem deBruijnNewmanPolymathBoydAdjacentContourCarrier_neg_two_lt_neg_one :
    deBruijnNewmanPolymathBoydAdjacentContourCarrier (-2) < -1 := by
  norm_num [deBruijnNewmanPolymathBoydAdjacentContourCarrier, Real.one_lt_exp_iff]

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_mem (y : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart y ∈ Icc (-2) 0 := by
  refine ⟨?_, deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos y⟩
  by_contra hnot
  have hlt : deBruijnNewmanPolymathBoydAdjacentContourRealPart y < -2 := lt_of_not_ge hnot
  have hmono := deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn
    (deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos y) (by norm_num) hlt
  rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier_realPart] at hmono
  linarith [Real.neg_one_le_cos y,
    deBruijnNewmanPolymathBoydAdjacentContourCarrier_neg_two_lt_neg_one]

theorem existsUnique_deBruijnNewmanPolymathBoydAdjacentContourRealPart (y : ℝ) :
    ∃! x : ℝ, x ∈ Icc (-2) 0 ∧
      Real.exp x * Real.cos y = x + 1 := by
  refine ⟨deBruijnNewmanPolymathBoydAdjacentContourRealPart y,
    ⟨deBruijnNewmanPolymathBoydAdjacentContourRealPart_mem y,
      deBruijnNewmanPolymathBoydAdjacentContourRealPart_eq y⟩, ?_⟩
  intro x hx
  have hcarrierX : deBruijnNewmanPolymathBoydAdjacentContourCarrier x = Real.cos y := by
    rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier, ← hx.2]
    calc
      Real.exp x * Real.cos y * Real.exp (-x) =
          Real.cos y * (Real.exp x * Real.exp (-x)) := by ring
      _ = Real.cos y := by rw [← Real.exp_add]; simp
  exact deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn.injOn
    hx.1.2 (deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos y)
    (hcarrierX.trans (deBruijnNewmanPolymathBoydAdjacentContourCarrier_realPart y).symm)

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_neg
    {y : ℝ} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart y < 0 := by
  have hcos : Real.cos y < 1 := by
    have hne : Real.cos y ≠ 1 := by
      intro h
      have hyzero := (Real.cos_eq_one_iff_of_lt_of_lt
        (by nlinarith [Real.pi_pos] : -(2 * Real.pi) < y) hy2pi).mp h
      exact hy0.ne' hyzero
    exact lt_of_le_of_ne (Real.cos_le_one y) hne
  exact deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse_neg hcos

theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourRealPart
    {y : ℝ} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourRealPart
      (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
        deBruijnNewmanPolymathBoydAdjacentContourRealPart y) y := by
  have hcos : Real.cos y < 1 := by
    have hne : Real.cos y ≠ 1 := by
      intro h
      exact hy0.ne' ((Real.cos_eq_one_iff_of_lt_of_lt
        (by nlinarith [Real.pi_pos] : -(2 * Real.pi) < y) hy2pi).mp h)
    exact lt_of_le_of_ne (Real.cos_le_one y) hne
  have hcomp := (hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse hcos).comp y
    (Real.hasDerivAt_cos y)
  have hxne : deBruijnNewmanPolymathBoydAdjacentContourRealPart y ≠ 0 :=
    (deBruijnNewmanPolymathBoydAdjacentContourRealPart_neg hy0 hy2pi).ne
  have hcoef :
      (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y *
          Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y))⁻¹ *
          (-Real.sin y) =
        Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
          deBruijnNewmanPolymathBoydAdjacentContourRealPart y := by
    field_simp [hxne, Real.exp_ne_zero]
    symm
    calc
      Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y *
          Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) =
          Real.sin y * (Real.exp (-deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
            Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y)) := by ring
      _ = Real.sin y := by rw [← Real.exp_add]; simp
  change HasDerivAt
    (deBruijnNewmanPolymathBoydAdjacentContourCarrierInverse ∘ Real.cos)
    (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
      deBruijnNewmanPolymathBoydAdjacentContourRealPart y) y
  exact hcomp.congr_deriv hcoef

/-- The upper adjacent zero-real-phase contour. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPlus (y : ℝ) : ℂ :=
  (deBruijnNewmanPolymathBoydAdjacentContourRealPart y : ℂ) + (y : ℂ) * I

/-- The imaginary phase height along the upper adjacent contour. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight (y : ℝ) : ℝ :=
  Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y - y

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourPlus :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourPlus := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourPlus
  exact (Complex.continuous_ofReal.comp
    continuous_deBruijnNewmanPolymathBoydAdjacentContourRealPart).add
      (Complex.continuous_ofReal.mul continuous_const)

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
  exact ((Real.continuous_exp.comp
    continuous_deBruijnNewmanPolymathBoydAdjacentContourRealPart).mul
      Real.continuous_sin).sub continuous_id

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourPlus_re (y : ℝ) :
    (deBruijnNewmanPolymathBoydAdjacentContourPlus y).re =
      deBruijnNewmanPolymathBoydAdjacentContourRealPart y := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPlus]

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourPlus_im (y : ℝ) :
    (deBruijnNewmanPolymathBoydAdjacentContourPlus y).im = y := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPlus]

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPlus (y : ℝ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentContourPlus y) =
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y : ℂ) * I := by
  apply Complex.ext
  · rw [deBruijnNewmanPolymathBoydComplexSaddlePhase]
    simp only [Complex.sub_re, Complex.exp_re,
      deBruijnNewmanPolymathBoydAdjacentContourPlus_re,
      deBruijnNewmanPolymathBoydAdjacentContourPlus_im, one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, sub_zero]
    rw [deBruijnNewmanPolymathBoydAdjacentContourRealPart_eq]
    simp
  · rw [deBruijnNewmanPolymathBoydComplexSaddlePhase,
      deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight]
    simp only [Complex.sub_im, Complex.exp_im,
      deBruijnNewmanPolymathBoydAdjacentContourPlus_re,
      deBruijnNewmanPolymathBoydAdjacentContourPlus_im, one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, zero_mul, add_zero, sub_zero]

theorem hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
    {y : ℝ} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
      (((deBruijnNewmanPolymathBoydAdjacentContourRealPart y) ^ 2 +
        Real.exp (2 * deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y ^ 2) /
        deBruijnNewmanPolymathBoydAdjacentContourRealPart y) y := by
  have hx := hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourRealPart hy0 hy2pi
  have hraw : HasDerivAt deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
      ((Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
          (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
            deBruijnNewmanPolymathBoydAdjacentContourRealPart y)) * Real.sin y +
        Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.cos y - 1) y := by
    unfold deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
    have h := (((Real.hasDerivAt_exp _).comp y hx).mul
      (Real.hasDerivAt_sin y)).sub (hasDerivAt_id y)
    have h' := h.congr_deriv (by
      change
        Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
              (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
                deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y +
            Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.cos y - 1 =
          Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) *
              (Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y /
                deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y +
            Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.cos y - 1
      rfl)
    exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hxne : deBruijnNewmanPolymathBoydAdjacentContourRealPart y ≠ 0 :=
    (deBruijnNewmanPolymathBoydAdjacentContourRealPart_neg hy0 hy2pi).ne
  apply hraw.congr_deriv
  rw [deBruijnNewmanPolymathBoydAdjacentContourRealPart_eq]
  field_simp [hxne]
  have hexp : Real.exp (deBruijnNewmanPolymathBoydAdjacentContourRealPart y) ^ 2 =
      Real.exp (2 * deBruijnNewmanPolymathBoydAdjacentContourRealPart y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1 <;> ring
  rw [hexp]
  ring

theorem deriv_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
    {y : ℝ} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    deriv deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y =
      ((deBruijnNewmanPolymathBoydAdjacentContourRealPart y) ^ 2 +
        Real.exp (2 * deBruijnNewmanPolymathBoydAdjacentContourRealPart y) * Real.sin y ^ 2) /
        deBruijnNewmanPolymathBoydAdjacentContourRealPart y :=
  (hasDerivAt_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight hy0 hy2pi).deriv

theorem deriv_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_neg
    {y : ℝ} (hy0 : 0 < y) (hy2pi : y < 2 * Real.pi) :
    deriv deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y < 0 := by
  rw [deriv_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight hy0 hy2pi]
  have hxneg := deBruijnNewmanPolymathBoydAdjacentContourRealPart_neg hy0 hy2pi
  exact div_neg_of_pos_of_neg (add_pos_of_pos_of_nonneg (sq_pos_of_neg hxneg)
    (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))) hxneg

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_strictAntiOn :
    StrictAntiOn deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
      (Icc 0 (2 * Real.pi)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 (2 * Real.pi))
    continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight.continuousOn
  intro y hy
  rw [interior_Icc] at hy
  exact deriv_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_neg hy.1 hy.2

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_zero :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart 0 = 0 := by
  apply deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn.injOn
    (deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos 0) (by simp)
  rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier_realPart]
  simp [deBruijnNewmanPolymathBoydAdjacentContourCarrier]

theorem deBruijnNewmanPolymathBoydAdjacentContourRealPart_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourRealPart (2 * Real.pi) = 0 := by
  apply deBruijnNewmanPolymathBoydAdjacentContourCarrier_strictMonoOn.injOn
    (deBruijnNewmanPolymathBoydAdjacentContourRealPart_nonpos _) (by simp)
  rw [deBruijnNewmanPolymathBoydAdjacentContourCarrier_realPart]
  simp [deBruijnNewmanPolymathBoydAdjacentContourCarrier]

theorem deBruijnNewmanPolymathBoydAdjacentContourPlus_zero :
    deBruijnNewmanPolymathBoydAdjacentContourPlus 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPlus,
    deBruijnNewmanPolymathBoydAdjacentContourRealPart_zero]

theorem deBruijnNewmanPolymathBoydAdjacentContourPlus_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourPlus (2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint 1 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPlus,
    deBruijnNewmanPolymathBoydAdjacentContourRealPart_two_pi,
    deBruijnNewmanPolymathBoydComplexSaddlePoint]

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_zero :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight,
    deBruijnNewmanPolymathBoydAdjacentContourRealPart_zero]

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight (2 * Real.pi) =
      -2 * Real.pi := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight,
    deBruijnNewmanPolymathBoydAdjacentContourRealPart_two_pi, Real.sin_two_pi]

/-- The positive magnitude of the decreasing imaginary phase along the upper contour. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude (y : ℝ) : ℝ :=
  -deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude :=
  continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight.neg

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_strictMonoOn :
    StrictMonoOn deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude
      (Icc 0 (2 * Real.pi)) :=
  deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_strictAntiOn.neg

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_zero :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude 0 = 0 := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_zero]

@[simp]
theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude (2 * Real.pi) =
      2 * Real.pi := by
  simp [deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_two_pi]

/-- The phase magnitude restricted to the upper adjacent contour interval. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap :
    Icc (0 : ℝ) (2 * Real.pi) → Icc (0 : ℝ) (2 * Real.pi) := fun y =>
  ⟨deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude y, by
    constructor
    · calc
        0 = deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude 0 := by simp
        _ ≤ deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude y :=
          deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_strictMonoOn.monotoneOn
            (by exact ⟨le_rfl, (mul_pos two_pos Real.pi_pos).le⟩) y.property y.property.1
    · calc
        deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude y ≤
            deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude (2 * Real.pi) :=
          deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_strictMonoOn.monotoneOn
            y.property (by exact ⟨(mul_pos two_pos Real.pi_pos).le, le_rfl⟩) y.property.2
        _ = 2 * Real.pi := by simp⟩

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap_strictMono :
    StrictMono deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap := by
  intro x y hxy
  exact deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_strictMonoOn
    x.property y.property hxy

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap_surjective :
    Function.Surjective deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap := by
  intro s
  have hmem : (s : ℝ) ∈ Icc
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude 0)
      (deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude (2 * Real.pi)) := by
    simpa using s.property
  obtain ⟨y, hy, hys⟩ := intermediate_value_Icc
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude.continuousOn hmem
  refine ⟨⟨y, hy⟩, ?_⟩
  apply Subtype.ext
  exact hys

/-- Phase magnitude as an order isomorphism of the adjacent contour interval. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeOrderIso :
    Icc (0 : ℝ) (2 * Real.pi) ≃o Icc (0 : ℝ) (2 * Real.pi) :=
  StrictMono.orderIsoOfSurjective
    deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap
    deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap_strictMono
    deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeMap_surjective

/-- The clamped inverse parameter for imaginary phase values. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter (s : ℝ) : ℝ :=
  (deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeOrderIso.symm
    ⟨min (max (-s) 0) (2 * Real.pi),
      ⟨le_min (le_max_right _ _) (by positivity), min_le_right _ _⟩⟩).1

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem (s : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter s ∈
      Icc 0 (2 * Real.pi) :=
  (deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeOrderIso.symm
    ⟨min (max (-s) 0) (2 * Real.pi),
      ⟨le_min (le_max_right _ _) (by positivity), min_le_right _ _⟩⟩).property

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter
  have hclamp : Continuous (fun s : ℝ => min (max (-s) 0) (2 * Real.pi)) :=
    (continuous_id.neg.max continuous_const).min continuous_const
  exact continuous_subtype_val.comp
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeOrderIso.symm.continuous.comp
      (hclamp.subtype_mk _))

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_liftParameter (s : ℝ) :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter s) =
      min (max (-s) 0) (2 * Real.pi) := by
  have h := deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitudeOrderIso.apply_symm_apply
    (⟨min (max (-s) 0) (2 * Real.pi),
      ⟨le_min (le_max_right _ _) (by positivity), min_le_right _ _⟩⟩ :
        Icc (0 : ℝ) (2 * Real.pi))
  exact congrArg Subtype.val h

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_liftParameter
    {s : ℝ} (hs : s ∈ Icc (-2 * Real.pi) 0) :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter s) = s := by
  have h := deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_liftParameter s
  have hneg0 : 0 ≤ -s := neg_nonneg.mpr hs.2
  have hneg2pi : -s ≤ 2 * Real.pi := by linarith [hs.1]
  rw [max_eq_left hneg0, min_eq_left hneg2pi] at h
  unfold deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude at h
  linarith

theorem existsUnique_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift
    {s : ℝ} (hs : s ∈ Icc (-2 * Real.pi) 0) :
    ∃! y : ℝ, y ∈ Icc 0 (2 * Real.pi) ∧
      deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y = s := by
  refine ⟨deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter s,
    ⟨deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem s,
      deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_liftParameter hs⟩, ?_⟩
  intro y hy
  exact deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_strictAntiOn.injOn
    hy.1 (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem s)
    (hy.2.trans (deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_liftParameter hs).symm)

/-- The upper adjacent contour point with prescribed imaginary phase. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (s : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydAdjacentContourPlus
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter s)

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourPhaseLift :=
  continuous_deBruijnNewmanPolymathBoydAdjacentContourPlus.comp
    continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPhaseLift
    {s : ℝ} (hs : s ∈ Icc (-2 * Real.pi) 0) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift s) = (s : ℂ) * I := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPlus,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight_liftParameter hs]

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_neg_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter (-2 * Real.pi) =
      2 * Real.pi := by
  apply deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_strictMonoOn.injOn
    (deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_mem _) (by
      exact ⟨(mul_pos two_pos Real.pi_pos).le, le_rfl⟩)
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseMagnitude_liftParameter]
  simp [Real.pi_pos.le]

theorem deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint 1 := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourPhaseLift,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLiftParameter_neg_two_pi,
    deBruijnNewmanPolymathBoydAdjacentContourPlus_two_pi]

theorem tendsto_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_at_neg_two_pi :
    Tendsto deBruijnNewmanPolymathBoydAdjacentContourPhaseLift
      (𝓝[Set.Ioi (-2 * Real.pi)] (-2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint 1)) := by
  rw [← deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_two_pi]
  exact continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift.continuousAt.mono_left
    inf_le_left

/-- The lower adjacent contour, obtained by conjugating the upper one. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourMinus (y : ℝ) : ℂ :=
  conj (deBruijnNewmanPolymathBoydAdjacentContourPlus y)

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_conj (u : ℂ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase (conj u) =
      conj (deBruijnNewmanPolymathBoydComplexSaddlePhase u) := by
  simp [deBruijnNewmanPolymathBoydComplexSaddlePhase]

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourMinus (y : ℝ) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentContourMinus y) =
      (-deBruijnNewmanPolymathBoydAdjacentContourPhaseHeight y : ℂ) * I := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourMinus,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_conj,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPlus]
  simp

theorem deBruijnNewmanPolymathBoydAdjacentContourMinus_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourMinus (2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint (-1) := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourMinus,
    deBruijnNewmanPolymathBoydAdjacentContourPlus_two_pi]
  apply Complex.ext <;> simp [deBruijnNewmanPolymathBoydComplexSaddlePoint]

/-- The lower adjacent phase lift, parameterized by positive imaginary phase. -/
noncomputable def deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift (s : ℝ) : ℂ :=
  conj (deBruijnNewmanPolymathBoydAdjacentContourPhaseLift (-s))

theorem continuous_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift :
    Continuous deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift := by
  unfold deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift
  exact continuous_conj.comp
    (continuous_deBruijnNewmanPolymathBoydAdjacentContourPhaseLift.comp continuous_id.neg)

theorem deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourNegativePhaseLift
    {s : ℝ} (hs : s ∈ Icc 0 (2 * Real.pi)) :
    deBruijnNewmanPolymathBoydComplexSaddlePhase
        (deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift s) = (s : ℂ) * I := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_conj,
    deBruijnNewmanPolymathBoydComplexSaddlePhase_adjacentContourPhaseLift]
  · simp
  · exact ⟨by linarith [hs.2], neg_nonpos.mpr hs.1⟩

theorem deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_two_pi :
    deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift (2 * Real.pi) =
      deBruijnNewmanPolymathBoydComplexSaddlePoint (-1) := by
  rw [deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift,
    show -(2 * Real.pi) = -2 * Real.pi by ring,
    deBruijnNewmanPolymathBoydAdjacentContourPhaseLift_neg_two_pi]
  apply Complex.ext <;> simp [deBruijnNewmanPolymathBoydComplexSaddlePoint]

theorem tendsto_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_at_two_pi :
    Tendsto deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift
      (𝓝[Set.Iio (2 * Real.pi)] (2 * Real.pi))
      (𝓝 (deBruijnNewmanPolymathBoydComplexSaddlePoint (-1))) := by
  rw [← deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift_two_pi]
  exact
    continuous_deBruijnNewmanPolymathBoydAdjacentContourNegativePhaseLift.continuousAt.mono_left
      inf_le_left

end

end LeanLab.Riemann
