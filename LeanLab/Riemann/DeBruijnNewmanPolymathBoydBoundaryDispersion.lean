import LeanLab.Riemann.DeBruijnNewmanPolymathBoydR2JacobianRemainder
import LeanLab.Riemann.WeilZeroCutoff

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Boundary dispersion for Boyd's scaled-Gamma remainder

This module rewrites the exponentially weighted rays in Boyd--Nemes equation `(15)` as the
boundary jump between the second scaled-Gamma remainder and the reflected inverse remainder.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory Real Set
open scoped Interval Real Topology

noncomputable section

/-- Nemes's inverse scaled-Gamma remainder at order two. -/
def deBruijnNewmanPolymathScaledGammaInverseR2 (z : ℂ) : ℂ :=
  1 / deBruijnNewmanPolymathScaledGamma z - 1 + 1 / (12 * z)

/-- The scaled-Gamma boundary jump selected by the reflection product. -/
def deBruijnNewmanPolymathScaledGammaBoundaryJump (z : ℂ) : ℂ :=
  deBruijnNewmanPolymathScaledGamma z -
    1 / deBruijnNewmanPolymathScaledGamma (-z)

/-- On the positive imaginary ray, the reflection product is exactly Boyd's exponential weight. -/
theorem deBruijnNewmanPolymathScaledGammaBoundaryJump_I
    {s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathScaledGammaBoundaryJump ((s : ℂ) * Complex.I) =
      Real.exp (-2 * Real.pi * s) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I) := by
  let z : ℂ := (s : ℂ) * Complex.I
  let q : ℝ := Real.exp (-2 * Real.pi * s)
  have hz : 0 < z.im := by simp [z, hs]
  have hq : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hden : (1 : ℂ) - (q : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq.ne'
  have hneg : deBruijnNewmanPolymathScaledGamma (-z) ≠ 0 :=
    deBruijnNewmanPolymathScaledGamma_ne_zero (by simpa [z] using hs.ne')
  have hprod := deBruijnNewmanPolymathScaledGamma_mul_neg hz
  rw [complex_exp_two_pi_I_mul_I s] at hprod
  have hinv : (1 : ℂ) / deBruijnNewmanPolymathScaledGamma (-z) =
      (1 - (q : ℂ)) * deBruijnNewmanPolymathScaledGamma z := by
    apply (div_eq_iff hneg).2
    calc
      (1 : ℂ) =
          (deBruijnNewmanPolymathScaledGamma z *
            deBruijnNewmanPolymathScaledGamma (-z)) * (1 - (q : ℂ)) := by
              rw [hprod]
              exact (div_mul_cancel₀ 1 hden).symm
      _ = ((1 - (q : ℂ)) * deBruijnNewmanPolymathScaledGamma z) *
          deBruijnNewmanPolymathScaledGamma (-z) := by ring
  change deBruijnNewmanPolymathScaledGammaBoundaryJump z =
    (q : ℂ) * deBruijnNewmanPolymathScaledGamma z
  rw [deBruijnNewmanPolymathScaledGammaBoundaryJump, hinv]
  ring

/-- The companion negative ray has the same Boyd exponential weight. -/
theorem deBruijnNewmanPolymathScaledGammaBoundaryJump_neg_I
    {s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathScaledGammaBoundaryJump (-(s : ℂ) * Complex.I) =
      Real.exp (-2 * Real.pi * s) *
        deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I) := by
  let z : ℂ := (s : ℂ) * Complex.I
  let q : ℝ := Real.exp (-2 * Real.pi * s)
  have hz : 0 < z.im := by simp [z, hs]
  have hq : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  have hden : (1 : ℂ) - (q : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hq.ne'
  have hpos : deBruijnNewmanPolymathScaledGamma z ≠ 0 :=
    deBruijnNewmanPolymathScaledGamma_ne_zero (by simpa [z] using hs.ne')
  have hprod := deBruijnNewmanPolymathScaledGamma_mul_neg hz
  rw [complex_exp_two_pi_I_mul_I s] at hprod
  have hinv : (1 : ℂ) / deBruijnNewmanPolymathScaledGamma z =
      (1 - (q : ℂ)) * deBruijnNewmanPolymathScaledGamma (-z) := by
    apply (div_eq_iff hpos).2
    calc
      (1 : ℂ) =
          (deBruijnNewmanPolymathScaledGamma z *
            deBruijnNewmanPolymathScaledGamma (-z)) * (1 - (q : ℂ)) := by
              rw [hprod]
              exact (div_mul_cancel₀ 1 hden).symm
      _ = ((1 - (q : ℂ)) * deBruijnNewmanPolymathScaledGamma (-z)) *
          deBruijnNewmanPolymathScaledGamma z := by ring
  have hpoint : -(s : ℂ) * Complex.I = -z := by simp [z]
  rw [hpoint]
  change deBruijnNewmanPolymathScaledGammaBoundaryJump (-z) =
    (q : ℂ) * deBruijnNewmanPolymathScaledGamma (-z)
  rw [deBruijnNewmanPolymathScaledGammaBoundaryJump, neg_neg, hinv]
  ring

/-- The jump splits into the right remainder and the reflected inverse remainder. -/
theorem deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders
    {z : ℂ} (hz : z ≠ 0) :
    deBruijnNewmanPolymathScaledGammaBoundaryJump z =
      deBruijnNewmanPolymathGammaStirlingR2 z -
        deBruijnNewmanPolymathScaledGammaInverseR2 (-z) := by
  rw [deBruijnNewmanPolymathScaledGammaBoundaryJump,
    deBruijnNewmanPolymathScaledGammaInverseR2,
    deBruijnNewmanPolymathGammaStirlingR2,
    deBruijnNewmanPolymathScaledGamma]
  field_simp [hz]
  all_goals ring

/-- The inverse order-two remainder is analytic in the right half-plane. -/
theorem deBruijnNewmanPolymathScaledGammaInverseR2_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathScaledGammaInverseR2 {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hfrac : DifferentiableWithinAt ℂ (fun w : ℂ => 1 / (12 * w))
      {w : ℂ | 0 < w.re} z :=
    (differentiableWithinAt_const (c := (1 : ℂ))).div
      ((differentiableWithinAt_const (c := (12 : ℂ))).mul differentiableWithinAt_id)
      (mul_ne_zero (by norm_num) hz0)
  have hone : DifferentiableWithinAt ℂ (fun _ : ℂ => (1 : ℂ))
      {w : ℂ | 0 < w.re} z := by fun_prop
  unfold deBruijnNewmanPolymathScaledGammaInverseR2
  exact ((deBruijnNewmanPolymathScaledGamma_inv_differentiableOn_rightHalfPlane z hz).sub
    hone).add hfrac

/-- Reflection transports the inverse remainder to an analytic function on the left half-plane. -/
theorem deBruijnNewmanPolymathScaledGammaInverseR2_neg_differentiableOn_leftHalfPlane :
    DifferentiableOn ℂ (fun z : ℂ => deBruijnNewmanPolymathScaledGammaInverseR2 (-z))
      {z : ℂ | z.re < 0} := by
  intro z hz
  change z.re < 0 at hz
  have hneg : -z ∈ {w : ℂ | 0 < w.re} := by
    change 0 < (-z).re
    simpa using neg_pos.mpr hz
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have houter : DifferentiableAt ℂ deBruijnNewmanPolymathScaledGammaInverseR2 (-z) :=
    (deBruijnNewmanPolymathScaledGammaInverseR2_differentiableOn_rightHalfPlane
      (-z) hneg).differentiableAt (hopen.mem_nhds hneg)
  exact (houter.comp z differentiableAt_id.neg).differentiableWithinAt

/-- The positive-ray Boyd kernel written with the scaled-Gamma boundary jump. -/
def deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand (z : ℂ) (s : ℝ) : ℂ :=
  ((s : ℂ) * deBruijnNewmanPolymathScaledGammaBoundaryJump
      ((s : ℂ) * Complex.I)) /
    (1 - (s : ℂ) * Complex.I / z)

/-- The negative-ray Boyd kernel written with the scaled-Gamma boundary jump. -/
def deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand (z : ℂ) (s : ℝ) : ℂ :=
  ((s : ℂ) * deBruijnNewmanPolymathScaledGammaBoundaryJump
      (-(s : ℂ) * Complex.I)) /
    (1 + (s : ℂ) * Complex.I / z)

theorem deBruijnNewmanPolymathBoydR2PlusIntegrand_eq_boundaryJump
    (z : ℂ) {s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathBoydR2PlusIntegrand z s =
      deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s := by
  rw [deBruijnNewmanPolymathBoydR2PlusIntegrand,
    deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand,
    deBruijnNewmanPolymathScaledGammaBoundaryJump_I hs]
  push_cast
  ring

theorem deBruijnNewmanPolymathBoydR2MinusIntegrand_eq_boundaryJump
    (z : ℂ) {s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathBoydR2MinusIntegrand z s =
      deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s := by
  rw [deBruijnNewmanPolymathBoydR2MinusIntegrand,
    deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand,
    deBruijnNewmanPolymathScaledGammaBoundaryJump_neg_I hs]
  push_cast
  ring

/-- The exact two-ray boundary projection underlying Boyd--Nemes equation `(15)` at `N = 2`. -/
def deBruijnNewmanPolymathBoydBoundaryJumpProjection (z : ℂ) : ℂ :=
  ((∫ s : ℝ in Ioi 0,
      deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s) -
    (∫ s : ℝ in Ioi 0,
      deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s)) /
      (2 * Real.pi * Complex.I * z ^ 2)

/-- Both boundary-jump rays inherit the source Boyd integrability certificate. -/
theorem deBruijnNewmanPolymathBoydBoundaryJump_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z) (Ioi 0) ∧
      IntegrableOn (deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z) (Ioi 0) := by
  constructor
  · refine (deBruijnNewmanPolymathBoydR2_integrableOn hz).1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact deBruijnNewmanPolymathBoydR2PlusIntegrand_eq_boundaryJump z hs
  · refine (deBruijnNewmanPolymathBoydR2_integrableOn hz).2.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact deBruijnNewmanPolymathBoydR2MinusIntegrand_eq_boundaryJump z hs

/-- Boyd's source integral is exactly the two-ray projection of the reflection boundary jump. -/
theorem deBruijnNewmanPolymathBoydR2Integral_eq_boundaryJumpProjection (z : ℂ) :
    deBruijnNewmanPolymathBoydR2Integral z =
      deBruijnNewmanPolymathBoydBoundaryJumpProjection z := by
  have hminus :
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2MinusIntegrand z s) =
        ∫ s : ℝ in Ioi 0,
          deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact deBruijnNewmanPolymathBoydR2MinusIntegrand_eq_boundaryJump z hs
  have hplus :
      (∫ s : ℝ in Ioi 0, deBruijnNewmanPolymathBoydR2PlusIntegrand z s) =
        ∫ s : ℝ in Ioi 0,
          deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact deBruijnNewmanPolymathBoydR2PlusIntegrand_eq_boundaryJump z hs
  rw [deBruijnNewmanPolymathBoydR2Integral_eq,
    deBruijnNewmanPolymathBoydBoundaryJumpProjection, hminus, hplus]

/-- Local-open-set version of the finite rectangular Cauchy formula. -/
theorem rectangleBoundaryIntegral_weighted_cauchyKernel_of_differentiableOn
    {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {rho : ℂ} {l r b t : ℝ}
    (hrect : [[l, r]] ×ℂ [[b, t]] ⊆ U)
    (hl : l < rho.re) (hr : rho.re < r)
    (hb : b < rho.im) (ht : rho.im < t) :
    rectangleBoundaryIntegral (fun z => F z / (z - rho)) l r b t =
      2 * (Real.pi : ℂ) * Complex.I * F rho := by
  let K : ℂ → ℂ := fun z => F rho * (z - rho)⁻¹
  let G : ℂ → ℂ := weightedCauchyRemovable F rho
  have hlne : l ≠ rho.re := ne_of_lt hl
  have hrne : r ≠ rho.re := ne_of_gt hr
  have hbne : b ≠ rho.im := ne_of_lt hb
  have htne : t ≠ rho.im := ne_of_gt ht
  have hrhoRect : rho ∈ [[l, r]] ×ℂ [[b, t]] := by
    rw [Complex.mem_reProdIm]
    constructor
    · rw [uIcc_of_le (hl.le.trans hr.le)]
      exact ⟨hl.le, hr.le⟩
    · rw [uIcc_of_le (hb.le.trans ht.le)]
      exact ⟨hb.le, ht.le⟩
  have hrhoU : rho ∈ U := hrect hrhoRect
  have hGdiff : DifferentiableOn ℂ G U := by
    dsimp only [G, weightedCauchyRemovable]
    exact (Complex.differentiableOn_dslope (hU.mem_nhds hrhoU)).2 hF
  have hKb : IntervalIntegrable (fun x : ℝ => K (x + b * Complex.I)) volume l r :=
    (intervalIntegrable_inv_sub_const_horizontal hbne).const_mul _
  have hKt : IntervalIntegrable (fun x : ℝ => K (x + t * Complex.I)) volume l r :=
    (intervalIntegrable_inv_sub_const_horizontal htne).const_mul _
  have hKr : IntervalIntegrable (fun y : ℝ => K (r + y * Complex.I)) volume b t :=
    (intervalIntegrable_inv_sub_const_vertical hrne).const_mul _
  have hKl : IntervalIntegrable (fun y : ℝ => K (l + y * Complex.I)) volume b t :=
    (intervalIntegrable_inv_sub_const_vertical hlne).const_mul _
  have hGb : IntervalIntegrable (fun x : ℝ => G (x + b * Complex.I)) volume l r := by
    apply intervalIntegrable_comp_of_differentiableOn hU hGdiff (by fun_prop)
    intro x hx
    apply hrect
    rw [Complex.mem_reProdIm]
    simpa using And.intro hx (left_mem_uIcc : b ∈ [[b, t]])
  have hGt : IntervalIntegrable (fun x : ℝ => G (x + t * Complex.I)) volume l r := by
    apply intervalIntegrable_comp_of_differentiableOn hU hGdiff (by fun_prop)
    intro x hx
    apply hrect
    rw [Complex.mem_reProdIm]
    simpa using And.intro hx (right_mem_uIcc : t ∈ [[b, t]])
  have hGr : IntervalIntegrable (fun y : ℝ => G (r + y * Complex.I)) volume b t := by
    apply intervalIntegrable_comp_of_differentiableOn hU hGdiff (by fun_prop)
    intro y hy
    apply hrect
    rw [Complex.mem_reProdIm]
    simpa using And.intro (right_mem_uIcc : r ∈ [[l, r]]) hy
  have hGl : IntervalIntegrable (fun y : ℝ => G (l + y * Complex.I)) volume b t := by
    apply intervalIntegrable_comp_of_differentiableOn hU hGdiff (by fun_prop)
    intro y hy
    apply hrect
    rw [Complex.mem_reProdIm]
    simpa using And.intro (left_mem_uIcc : l ∈ [[l, r]]) hy
  have hbottom :
      (∫ x : ℝ in l..r, F (x + b * Complex.I) / (x + b * Complex.I - rho)) =
        ∫ x : ℝ in l..r, K (x + b * Complex.I) + G (x + b * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] at him
      apply hbne
      linarith)
  have htop :
      (∫ x : ℝ in l..r, F (x + t * Complex.I) / (x + t * Complex.I - rho)) =
        ∫ x : ℝ in l..r, K (x + t * Complex.I) + G (x + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add] at him
      apply htne
      linarith)
  have hright :
      (∫ y : ℝ in b..t, F (r + y * Complex.I) / (r + y * Complex.I - rho)) =
        ∫ y : ℝ in b..t, K (r + y * Complex.I) + G (r + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one] at hre
      apply hrne
      linarith)
  have hleft :
      (∫ y : ℝ in b..t, F (l + y * Complex.I) / (l + y * Complex.I - rho)) =
        ∫ y : ℝ in b..t, K (l + y * Complex.I) + G (l + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one] at hre
      apply hlne
      linarith)
  have hdecomp :
      rectangleBoundaryIntegral (fun z => F z / (z - rho)) l r b t =
        rectangleBoundaryIntegral (fun z => K z + G z) l r b t := by
    unfold rectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  have hadd := rectangleBoundaryIntegral_add hKb hGb hKt hGt hKr hGr hKl hGl
  have hGzero : rectangleBoundaryIntegral G l r b t = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn (hGdiff.mono hrect)
  have hK : rectangleBoundaryIntegral K l r b t =
      F rho * rectangleBoundaryIntegral (fun z : ℂ => (z - rho)⁻¹) l r b t :=
    rectangleBoundaryIntegral_const_mul (F rho) (fun z : ℂ => (z - rho)⁻¹) l r b t
  rw [hdecomp, hadd, hK, hGzero, add_zero,
    rectangleBoundaryIntegral_inv_sub_eq_two_pi_mul_I hl hr hb ht]
  ring

/-- The Cauchy weight for the actual second scaled-Gamma remainder. -/
def deBruijnNewmanPolymathBoydR2CauchyWeight (z : ℂ) : ℂ :=
  z * deBruijnNewmanPolymathGammaStirlingR2 z

/-- The reflected inverse-remainder Cauchy weight. -/
def deBruijnNewmanPolymathBoydInverseR2CauchyWeight (z : ℂ) : ℂ :=
  z * deBruijnNewmanPolymathScaledGammaInverseR2 (-z)

theorem deBruijnNewmanPolymathBoydR2CauchyWeight_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathBoydR2CauchyWeight
      {z : ℂ | 0 < z.re} := by
  exact differentiableOn_id.mul
    deBruijnNewmanPolymathGammaStirlingR2_differentiableOn_rightHalfPlane

theorem deBruijnNewmanPolymathBoydInverseR2CauchyWeight_differentiableOn_leftHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathBoydInverseR2CauchyWeight
      {z : ℂ | z.re < 0} := by
  exact differentiableOn_id.mul
    deBruijnNewmanPolymathScaledGammaInverseR2_neg_differentiableOn_leftHalfPlane

/-- The positive boundary ray separates into right and reflected-left remainder kernels. -/
theorem deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand_eq_remainders
    (z : ℂ) {s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s =
      ((s : ℂ) * deBruijnNewmanPolymathGammaStirlingR2
          ((s : ℂ) * Complex.I)) /
          (1 - (s : ℂ) * Complex.I / z) -
        ((s : ℂ) * deBruijnNewmanPolymathScaledGammaInverseR2
          (-(s : ℂ) * Complex.I)) /
          (1 - (s : ℂ) * Complex.I / z) := by
  rw [deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand,
    deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') Complex.I_ne_zero)]
  ring_nf

/-- The negative boundary ray has the companion right/reflected-left separation. -/
theorem deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand_eq_remainders
    (z : ℂ) {s : ℝ} (hs : 0 < s) :
    deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s =
      ((s : ℂ) * deBruijnNewmanPolymathGammaStirlingR2
          (-(s : ℂ) * Complex.I)) /
          (1 + (s : ℂ) * Complex.I / z) -
        ((s : ℂ) * deBruijnNewmanPolymathScaledGammaInverseR2
          ((s : ℂ) * Complex.I)) /
          (1 + (s : ℂ) * Complex.I / z) := by
  have hpoint : -(s : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs.ne')) Complex.I_ne_zero
  have hnegpoint : -(-(s : ℂ) * Complex.I) = (s : ℂ) * Complex.I := by ring
  rw [deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand,
    deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders hpoint, hnegpoint]
  ring_nf

/-- The three non-imaginary edges of the finite right-half-plane Cauchy rectangle. -/
def deBruijnNewmanPolymathBoydR2RightEdgeResidual
    (z : ℂ) (epsilon R T : ℝ) : ℂ :=
  (∫ x : ℝ in epsilon..R,
      deBruijnNewmanPolymathBoydR2CauchyWeight
          (x + (-T) * Complex.I) /
        (x + (-T) * Complex.I - z)) -
    (∫ x : ℝ in epsilon..R,
      deBruijnNewmanPolymathBoydR2CauchyWeight
          (x + T * Complex.I) /
        (x + T * Complex.I - z)) +
    Complex.I * (∫ y : ℝ in -T..T,
      deBruijnNewmanPolymathBoydR2CauchyWeight
          (R + y * Complex.I) /
        (R + y * Complex.I - z))

/-- Finite right-half-plane Cauchy projection with every residual edge explicit. -/
theorem deBruijnNewmanPolymathBoydR2_finite_rightHalfPlane_projection
    {z : ℂ} {epsilon R T : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonz : epsilon < z.re) (hzR : z.re < R)
    (hbottom : -T < z.im) (htop : z.im < T) :
    Complex.I * (∫ y : ℝ in -T..T,
      deBruijnNewmanPolymathBoydR2CauchyWeight
          (epsilon + y * Complex.I) /
        (epsilon + y * Complex.I - z)) =
      -(2 * (Real.pi : ℂ) * Complex.I *
          deBruijnNewmanPolymathBoydR2CauchyWeight z) +
        deBruijnNewmanPolymathBoydR2RightEdgeResidual z epsilon R T := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hepsilonR : epsilon ≤ R := (hepsilonz.trans hzR).le
  have hrect : [[epsilon, R]] ×ℂ [[-T, T]] ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    change 0 < w.re
    rw [uIcc_of_le hepsilonR] at hw
    exact hepsilon.trans_le hw.1.1
  have hboundary :=
    rectangleBoundaryIntegral_weighted_cauchyKernel_of_differentiableOn
      hU deBruijnNewmanPolymathBoydR2CauchyWeight_differentiableOn_rightHalfPlane
      hrect hepsilonz hzR hbottom htop
  simp only [rectangleBoundaryIntegral] at hboundary
  rw [deBruijnNewmanPolymathBoydR2RightEdgeResidual]
  simp only [Complex.ofReal_neg] at hboundary ⊢
  linear_combination -hboundary

/-- The three outer edges of the finite left-half-plane reflected-inverse rectangle. -/
def deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual
    (z : ℂ) (epsilon R T : ℝ) : ℂ :=
  -(∫ x : ℝ in -R..-epsilon,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight
          (x + (-T) * Complex.I) /
        (x + (-T) * Complex.I - z)) +
    (∫ x : ℝ in -R..-epsilon,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight
          (x + T * Complex.I) /
        (x + T * Complex.I - z)) +
    Complex.I * (∫ y : ℝ in -T..T,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight
          (-R + y * Complex.I) /
        (-R + y * Complex.I - z))

/-- Finite left-half-plane Cauchy cancellation with every residual edge explicit. -/
theorem deBruijnNewmanPolymathBoydInverseR2_finite_leftHalfPlane_projection
    {z : ℂ} {epsilon R T : ℝ}
    (hz : 0 < z.re) (hepsilon : 0 < epsilon) (hepsilonR : epsilon < R) :
    Complex.I * (∫ y : ℝ in -T..T,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight
          (-epsilon + y * Complex.I) /
        (-epsilon + y * Complex.I - z)) =
      deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z epsilon R T := by
  let U : Set ℂ := {w : ℂ | w.re < 0}
  have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hleftRight : -R ≤ -epsilon := neg_le_neg hepsilonR.le
  have hrect : [[-R, -epsilon]] ×ℂ [[-T, T]] ⊆ U := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    change w.re < 0
    rw [uIcc_of_le hleftRight] at hw
    exact hw.1.2.trans_lt (neg_neg_of_pos hepsilon)
  have hkernel : DifferentiableOn ℂ
      (fun w => deBruijnNewmanPolymathBoydInverseR2CauchyWeight w / (w - z))
      ([[-R, -epsilon]] ×ℂ [[-T, T]]) := by
    intro w hw
    have hwU : w ∈ U := hrect hw
    have hwz : w - z ≠ 0 := by
      rw [sub_ne_zero]
      intro hwz
      have hre := congrArg Complex.re hwz
      change w.re < 0 at hwU
      linarith
    have hden : DifferentiableWithinAt ℂ (fun q : ℂ => q - z)
        ([[-R, -epsilon]] ×ℂ [[-T, T]]) w := by fun_prop
    have hweight : DifferentiableWithinAt ℂ
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
        ([[-R, -epsilon]] ×ℂ [[-T, T]]) w :=
      (deBruijnNewmanPolymathBoydInverseR2CauchyWeight_differentiableOn_leftHalfPlane
        w hwU).mono hrect
    exact hweight.div hden hwz
  have hboundary := rectangleBoundaryIntegral_eq_zero_of_differentiableOn hkernel
  simp only [rectangleBoundaryIntegral] at hboundary
  rw [deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual]
  simp only [Complex.ofReal_neg] at hboundary ⊢
  linear_combination hboundary

/-- Inner positive real boundary of the canonical rectangle family. -/
def deBruijnNewmanPolymathBoydBoundaryEpsilon (z : ℂ) (n : ℕ) : ℝ :=
  z.re / ((n : ℝ) + 2)

/-- Outer real boundary of the canonical rectangle family. -/
def deBruijnNewmanPolymathBoydBoundaryRadius (z : ℂ) (n : ℕ) : ℝ :=
  z.re + (n : ℝ) + 1

/-- Symmetric height of the canonical rectangle family. -/
def deBruijnNewmanPolymathBoydBoundaryHeight (z : ℂ) (n : ℕ) : ℝ :=
  |z.im| + (n : ℝ) + 1

/-- The normalized difference of the two finite inner vertical Cauchy integrals. -/
def deBruijnNewmanPolymathBoydFiniteBoundaryProjection
    (z : ℂ) (epsilon T : ℝ) : ℂ :=
  -(1 / (2 * Real.pi * Complex.I * z)) *
    (Complex.I * (∫ y : ℝ in -T..T,
      deBruijnNewmanPolymathBoydR2CauchyWeight
          (epsilon + y * Complex.I) /
        (epsilon + y * Complex.I - z)) -
      Complex.I * (∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
            (-epsilon + y * Complex.I) /
          (-epsilon + y * Complex.I - z)))

/-- Every canonical rectangle contains `z` in its right half and keeps its left half pole-free. -/
theorem deBruijnNewmanPolymathBoydBoundaryCanonical_geometry
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    0 < deBruijnNewmanPolymathBoydBoundaryEpsilon z n ∧
      deBruijnNewmanPolymathBoydBoundaryEpsilon z n < z.re ∧
      z.re < deBruijnNewmanPolymathBoydBoundaryRadius z n ∧
      -deBruijnNewmanPolymathBoydBoundaryHeight z n < z.im ∧
      z.im < deBruijnNewmanPolymathBoydBoundaryHeight z n ∧
      deBruijnNewmanPolymathBoydBoundaryEpsilon z n <
        deBruijnNewmanPolymathBoydBoundaryRadius z n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 1 < (n : ℝ) + 2 := by linarith
  have hepsilon : 0 < deBruijnNewmanPolymathBoydBoundaryEpsilon z n := by
    rw [deBruijnNewmanPolymathBoydBoundaryEpsilon]
    positivity
  have hepsilonz : deBruijnNewmanPolymathBoydBoundaryEpsilon z n < z.re := by
    rw [deBruijnNewmanPolymathBoydBoundaryEpsilon]
    exact div_lt_self hz hden
  have hzR : z.re < deBruijnNewmanPolymathBoydBoundaryRadius z n := by
    rw [deBruijnNewmanPolymathBoydBoundaryRadius]
    linarith
  have hbottom : -deBruijnNewmanPolymathBoydBoundaryHeight z n < z.im := by
    rw [deBruijnNewmanPolymathBoydBoundaryHeight]
    nlinarith [neg_abs_le z.im]
  have htop : z.im < deBruijnNewmanPolymathBoydBoundaryHeight z n := by
    rw [deBruijnNewmanPolymathBoydBoundaryHeight]
    nlinarith [le_abs_self z.im]
  exact ⟨hepsilon, hepsilonz, hzR, hbottom, htop, hepsilonz.trans hzR⟩

/-- Exact finite canonical projection: only the two explicit outer-edge residuals remain. -/
theorem deBruijnNewmanPolymathBoydFiniteBoundaryProjection_eq_R2_sub_residual
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n) =
      deBruijnNewmanPolymathGammaStirlingR2 z -
        (deBruijnNewmanPolymathBoydR2RightEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
          deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n)) /
          (2 * Real.pi * Complex.I * z) := by
  obtain ⟨hepsilon, hepsilonz, hzR, hbottom, htop, hepsilonR⟩ :=
    deBruijnNewmanPolymathBoydBoundaryCanonical_geometry hz n
  have hright := deBruijnNewmanPolymathBoydR2_finite_rightHalfPlane_projection
    hepsilon hepsilonz hzR hbottom htop
  have hleft := deBruijnNewmanPolymathBoydInverseR2_finite_leftHalfPlane_projection
    (T := deBruijnNewmanPolymathBoydBoundaryHeight z n) hz hepsilon hepsilonR
  rw [deBruijnNewmanPolymathBoydFiniteBoundaryProjection, hright, hleft,
    deBruijnNewmanPolymathBoydR2CauchyWeight]
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  field_simp [hz0, Real.pi_ne_zero, Complex.I_ne_zero]
  ring

/-- Vanishing of the two explicit outer-edge residuals forces the finite projections to `R_2`. -/
theorem deBruijnNewmanPolymathBoydFiniteBoundaryProjection_tendsto_R2_of_edgeResiduals
    {z : ℂ} (hz : 0 < z.re)
    (hright : Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydR2RightEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0))
    (hleft : Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 (deBruijnNewmanPolymathGammaStirlingR2 z)) := by
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hz
  have hden : (2 : ℂ) * Real.pi * Complex.I * z ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hz0
  have hquot : Filter.Tendsto
      (fun n : ℕ =>
        (deBruijnNewmanPolymathBoydR2RightEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
          deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n)) /
          (2 * Real.pi * Complex.I * z))
      Filter.atTop (𝓝 0) := by
    have hconst : Filter.Tendsto
        (fun _ : ℕ => (2 : ℂ) * Real.pi * Complex.I * z)
        Filter.atTop (𝓝 ((2 : ℂ) * Real.pi * Complex.I * z)) := tendsto_const_nhds
    have hraw := (hright.sub hleft).div hconst hden
    have hraw0 : Filter.Tendsto
        ((fun n : ℕ =>
          deBruijnNewmanPolymathBoydR2RightEdgeResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
              (deBruijnNewmanPolymathBoydBoundaryRadius z n)
              (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
            deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
              (deBruijnNewmanPolymathBoydBoundaryRadius z n)
              (deBruijnNewmanPolymathBoydBoundaryHeight z n)) /
          (fun _ : ℕ => (2 : ℂ) * Real.pi * Complex.I * z))
        Filter.atTop (𝓝 0) := by simpa using hraw
    apply Filter.Tendsto.congr' ?_ hraw0
    filter_upwards with n
    exact Pi.div_apply _ _ n
  have hexpr : Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathGammaStirlingR2 z -
        (deBruijnNewmanPolymathBoydR2RightEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
          deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n)) /
          (2 * Real.pi * Complex.I * z))
      Filter.atTop (𝓝 (deBruijnNewmanPolymathGammaStirlingR2 z)) := by
    simpa using (tendsto_const_nhds.sub hquot)
  apply Filter.Tendsto.congr' ?_ hexpr
  filter_upwards with n
  exact (deBruijnNewmanPolymathBoydFiniteBoundaryProjection_eq_R2_sub_residual hz n).symm

/-- The exact remaining analytic limit package after the finite Cauchy identities. -/
def deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate : Prop :=
  ∀ z : ℂ, 0 < z.re →
    Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydR2RightEdgeResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryRadius z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryRadius z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z))

/-- The registered edge-decay and boundary-trace limits close Boyd--Nemes equation `(15)`. -/
theorem deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_of_boundaryDispersionLimits
    (hlimits : deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate)
    {z : ℂ} (hz : 0 < z.re) :
    deBruijnNewmanPolymathGammaStirlingR2 z =
      deBruijnNewmanPolymathBoydR2Integral z := by
  obtain ⟨hright, hleft, htrace⟩ := hlimits z hz
  have hR2 :=
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection_tendsto_R2_of_edgeResiduals
      hz hright hleft
  have heq : deBruijnNewmanPolymathGammaStirlingR2 z =
      deBruijnNewmanPolymathBoydBoundaryJumpProjection z :=
    tendsto_nhds_unique hR2 htrace
  rw [deBruijnNewmanPolymathBoydR2Integral_eq_boundaryJumpProjection]
  exact heq

/-- The complete unconditional boundary-dispersion certificate retained by Loop 27. -/
def deBruijnNewmanPolymathBoydBoundaryDispersionCertificateStatement : Prop :=
  (∀ s : ℝ, 0 < s →
    deBruijnNewmanPolymathScaledGammaBoundaryJump ((s : ℂ) * Complex.I) =
      Real.exp (-2 * Real.pi * s) *
        deBruijnNewmanPolymathScaledGamma ((s : ℂ) * Complex.I)) ∧
  (∀ s : ℝ, 0 < s →
    deBruijnNewmanPolymathScaledGammaBoundaryJump (-(s : ℂ) * Complex.I) =
      Real.exp (-2 * Real.pi * s) *
        deBruijnNewmanPolymathScaledGamma (-(s : ℂ) * Complex.I)) ∧
  (∀ z : ℂ, z ≠ 0 →
    deBruijnNewmanPolymathScaledGammaBoundaryJump z =
      deBruijnNewmanPolymathGammaStirlingR2 z -
        deBruijnNewmanPolymathScaledGammaInverseR2 (-z)) ∧
  DifferentiableOn ℂ deBruijnNewmanPolymathScaledGammaInverseR2
    {z : ℂ | 0 < z.re} ∧
  DifferentiableOn ℂ (fun z : ℂ => deBruijnNewmanPolymathScaledGammaInverseR2 (-z))
    {z : ℂ | z.re < 0} ∧
  (∀ z : ℂ,
    deBruijnNewmanPolymathBoydR2Integral z =
      deBruijnNewmanPolymathBoydBoundaryJumpProjection z) ∧
  (∀ z : ℂ, 0 < z.re → ∀ n : ℕ,
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n) =
      deBruijnNewmanPolymathGammaStirlingR2 z -
        (deBruijnNewmanPolymathBoydR2RightEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
          deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
            (deBruijnNewmanPolymathBoydBoundaryRadius z n)
            (deBruijnNewmanPolymathBoydBoundaryHeight z n)) /
          (2 * Real.pi * Complex.I * z)) ∧
  (deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate →
    ∀ z : ℂ, 0 < z.re →
      deBruijnNewmanPolymathGammaStirlingR2 z =
        deBruijnNewmanPolymathBoydR2Integral z)

theorem deBruijnNewmanPolymathBoydBoundaryDispersionCertificate :
    deBruijnNewmanPolymathBoydBoundaryDispersionCertificateStatement := by
  refine ⟨fun _ hs => deBruijnNewmanPolymathScaledGammaBoundaryJump_I hs,
    fun _ hs => deBruijnNewmanPolymathScaledGammaBoundaryJump_neg_I hs,
    fun _ hz => deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders hz,
    deBruijnNewmanPolymathScaledGammaInverseR2_differentiableOn_rightHalfPlane,
    deBruijnNewmanPolymathScaledGammaInverseR2_neg_differentiableOn_leftHalfPlane,
    deBruijnNewmanPolymathBoydR2Integral_eq_boundaryJumpProjection, ?_, ?_⟩
  · intro z hz n
    exact deBruijnNewmanPolymathBoydFiniteBoundaryProjection_eq_R2_sub_residual hz n
  · intro hlimits z hz
    exact deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_of_boundaryDispersionLimits hlimits hz

end

end LeanLab.Riemann
