import LeanLab.Riemann.HardyAbelMomentAmplification
import LeanLab.Riemann.DeBruijnNewmanHeat
import Mathlib.Analysis.MellinInversion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy's theta inversion

This module reconstructs the interior Cahen--Mellin identity in Hardy's 1914 proof.
The boundary Abel limit is deliberately not used here.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped Topology

namespace LeanLab.Riemann

noncomputable section

/-- Hardy's theta series, indexed once over the positive squares. -/
def hardyThetaSeries (y : ℂ) : ℂ :=
  1 + 2 * ∑' n : ℕ,
    Complex.exp (-(((n + 1 : ℕ) : ℂ) ^ 2) * y)

/-- The connected alpha strip on which `Re (pi * exp (I * alpha))` is positive. -/
def hardyAlphaStrip : Set ℂ :=
  {alpha : ℂ | |alpha.re| < Real.pi / 2}

/-- The complexified interior integral in Hardy's equation (2). -/
def hardyXiInteriorIntegral (alpha : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    (Complex.exp (alpha * (t : ℂ)) +
        Complex.exp (-alpha * (t : ℂ))) *
      (hardyXi (2 * t) : ℂ) / (1 / 4 + 4 * t ^ 2)

private theorem integrableOn_norm_deBruijnNewmanPhi :
    IntegrableOn (fun u : ℝ => ‖deBruijnNewmanPhi u‖) (Ioi 0) := by
  have hweighted :=
    integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi 0
      (le_refl 0) 0
  apply Integrable.mono' hweighted
  · exact
      (aestronglyMeasurable_deBruijnNewmanPhi
        (volume.restrict (Ioi 0))).norm
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simp only [zero_mul, add_zero, Real.exp_zero]
    exact le_mul_of_one_le_left (norm_nonneg _) (by nlinarith [sq_nonneg u])

private theorem integrableOn_deBruijnNewmanH_zero_real_integrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        (deBruijnNewmanPhi u : ℂ) *
          Complex.cos ((4 * t : ℂ) * (u : ℂ)))
      (Ioi 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using
    integrableOn_dbnHeatCosIntegrand 0 (4 * t : ℂ)

/-- The actual Hardy xi coordinate is uniformly bounded on the real line by the
`L1` mass of the source theta kernel. -/
theorem norm_hardyXi_two_mul_le_phiMass (t : ℝ) :
    ‖hardyXi (2 * t)‖ ≤
      8 * ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖ := by
  rw [Real.norm_eq_abs, hardyXi_two_mul_eq_deBruijnNewmanH_zero_four_mul]
  have hH :
      ‖deBruijnNewmanH 0 (4 * t)‖ ≤
        ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖ := by
    rw [deBruijnNewmanH]
    simp only [zero_mul, Real.exp_zero, one_mul]
    calc
      ‖∫ u : ℝ in Ioi 0,
          (deBruijnNewmanPhi u : ℂ) *
            Complex.cos ((4 * t : ℂ) * (u : ℂ))‖
          ≤ ∫ u : ℝ in Ioi 0,
              ‖(deBruijnNewmanPhi u : ℂ) *
                Complex.cos ((4 * t : ℂ) * (u : ℂ))‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖ := by
        apply integral_mono_ae
          (integrableOn_deBruijnNewmanH_zero_real_integrand t).norm
          integrableOn_norm_deBruijnNewmanPhi
        filter_upwards with u
        rw [norm_mul, norm_real]
        have harg :
            ((4 * t : ℂ) * (u : ℂ)) = ((4 * t * u : ℝ) : ℂ) := by
          push_cast
          ring
        rw [harg, ← Complex.ofReal_cos, norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (Real.abs_cos_le_one (4 * t * u))
  calc
    |8 * (deBruijnNewmanH 0 (4 * t)).re|
        ≤ 8 * ‖deBruijnNewmanH 0 (4 * t)‖ := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
          exact mul_le_mul_of_nonneg_left
            (Complex.abs_re_le_norm _) (by norm_num)
    _ ≤ 8 * ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖ := by
      gcongr

private theorem hardyCompletedMellin_eq_xi (t : ℝ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
        ((1 / 4 : ℂ) + t * I) =
      2 * (1 - 2 * (hardyXi (2 * t) : ℂ)) /
        (1 / 4 + 4 * t ^ 2) := by
  have hs :
      2 * ((1 / 4 : ℂ) + t * I) =
        hardyCriticalLinePoint (2 * t) := by
    apply Complex.ext
    · norm_num [hardyCriticalLinePoint]
    · simp [hardyCriticalLinePoint]
  have hcompleted :
      mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
          ((1 / 4 : ℂ) + t * I) =
        2 * completedRiemannZeta₀ (hardyCriticalLinePoint (2 * t)) := by
    change
      (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀
          ((1 / 4 : ℂ) + t * I) =
        2 * completedRiemannZeta₀ (hardyCriticalLinePoint (2 * t))
    rw [← hs]
    unfold completedRiemannZeta₀
      HurwitzZeta.completedHurwitzZetaEven₀
    ring
  rw [hcompleted]
  rw [← hardyCriticalXi_eq_ofReal]
  unfold hardyCriticalXi riemannXi
  have hprod :
      hardyCriticalLinePoint (2 * t) *
          (hardyCriticalLinePoint (2 * t) - 1) =
        -(((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
    unfold hardyCriticalLinePoint
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hdenCast :
      (1 / 4 : ℂ) + 4 * (t : ℂ) ^ 2 =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hden : (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 := by positivity
  have hdenC :
      ((((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  rw [hdenCast, hprod, eq_div_iff hdenC]
  ring

private theorem integrable_hardyMellinMajorant :
    Integrable
      (fun t : ℝ =>
        (2 * (1 + 16 *
          (∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖))) /
          (1 / 4 + 4 * t ^ 2)) := by
  have hbase :
      Integrable (fun t : ℝ => (1 / 4 + 4 * t ^ 2)⁻¹) := by
    convert
      (integrable_inv_one_add_sq.comp_mul_left'
        (show (4 : ℝ) ≠ 0 by norm_num)).const_mul 4 using 1
    funext t
    field_simp
  simpa only [div_eq_mul_inv, mul_assoc] using
    hbase.const_mul
      (2 * (1 + 16 *
        (∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖)))

/-- The actual completed critical-line Mellin transform in Hardy's formula is absolutely
integrable on `Re(q)=1/4`. -/
theorem verticalIntegrable_hardyCompletedMellin :
    Complex.VerticalIntegrable
      (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif)
      (1 / 4) := by
  rw [Complex.VerticalIntegrable]
  apply Integrable.mono' integrable_hardyMellinMajorant
  · exact
      ((HurwitzZeta.hurwitzEvenFEPair 0).differentiable_Λ₀.continuous
        |>.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    have hline := hardyCompletedMellin_eq_xi t
    norm_num at hline ⊢
    rw [hline, norm_div, norm_mul]
    have hdenArg :
        (1 / 4 : ℂ) + 4 * (t : ℂ) ^ 2 =
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    have hden :
        ‖((1 / 4 : ℂ) + 4 * (t : ℂ) ^ 2)‖ =
          (1 / 4 + 4 * t ^ 2 : ℝ) := by
      rw [hdenArg, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hden]
    have hnum :
        ‖1 - 2 * (hardyXi (2 * t) : ℂ)‖ ≤
          1 + 16 * ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖ := by
      calc
        ‖1 - 2 * (hardyXi (2 * t) : ℂ)‖
            ≤ ‖(1 : ℂ)‖ + ‖2 * (hardyXi (2 * t) : ℂ)‖ :=
          norm_sub_le _ _
        _ = 1 + 2 * ‖hardyXi (2 * t)‖ := by
          simp
        _ ≤ 1 + 16 * ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖ := by
          have hxi := norm_hardyXi_two_mul_le_phiMass t
          nlinarith
    have hdenPos : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
    calc
      ‖(2 : ℂ)‖ * ‖1 - 2 * (hardyXi (2 * t) : ℂ)‖ /
            (1 / 4 + 4 * t ^ 2)
          ≤ 2 * (1 + 16 *
              (∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖)) /
            (1 / 4 + 4 * t ^ 2) := by
        norm_num
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnum (by norm_num)) hdenPos.le

/-- Positive-real Mellin inversion away from the library representative's artificial
point value at `x = 1`. -/
theorem hardyMellinInv_eq_f_modif {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    mellinInv (1 / 4)
        (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif) x =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  apply mellinInv_mellin_eq (1 / 4) _ hx
  · have hM :
        HasMellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
          (((1 / 4 : ℝ) : ℂ))
          ((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀
            (((1 / 4 : ℝ) : ℂ))) := by
      unfold WeakFEPair.Λ₀
      exact
        (HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin
          (((1 / 4 : ℝ) : ℂ))
    exact hM.1
  · exact verticalIntegrable_hardyCompletedMellin
  · rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · have hnhds : Ioo 0 1 ∈ 𝓝 x := Ioo_mem_nhds hx hlt
      have hfcont :
          ContinuousAt (HurwitzZeta.hurwitzEvenFEPair 0).f x := by
        simpa only [HurwitzZeta.hurwitzEvenFEPair] using
          ((Complex.continuous_ofReal.comp_continuousOn
            (HurwitzZeta.continuousOn_evenKernel 0)) x hx
              |>.continuousAt (Ioi_mem_nhds hx))
      have hpow :
          ContinuousAt
            (fun y : ℝ =>
              y ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k)) x :=
        Real.continuousAt_rpow_const x
          (-(HurwitzZeta.hurwitzEvenFEPair 0).k) (.inl hx.ne')
      have hpowC :
          ContinuousAt
            (fun y : ℝ =>
              ((y ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k) : ℝ) : ℂ)) x :=
        Complex.continuous_ofReal.continuousAt.comp hpow
      have hcont : ContinuousAt (fun y : ℝ =>
          (HurwitzZeta.hurwitzEvenFEPair 0).f y -
            (((HurwitzZeta.hurwitzEvenFEPair 0).ε *
                (y ^ (-(HurwitzZeta.hurwitzEvenFEPair 0).k) : ℝ)) : ℂ) *
              (HurwitzZeta.hurwitzEvenFEPair 0).g₀) x :=
        hfcont.sub ((continuousAt_const.mul hpowC).mul continuousAt_const)
      refine hcont.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with y hy
      simp [WeakFEPair.f_modif, hy.1, hy.2,
        not_lt_of_ge hy.2.le]
    · have hnhds : Ioi 1 ∈ 𝓝 x := Ioi_mem_nhds hgt
      have hfcont :
          ContinuousAt (HurwitzZeta.hurwitzEvenFEPair 0).f x := by
        simpa only [HurwitzZeta.hurwitzEvenFEPair] using
          ((Complex.continuous_ofReal.comp_continuousOn
            (HurwitzZeta.continuousOn_evenKernel 0)) x hx
              |>.continuousAt (Ioi_mem_nhds hx))
      have hcont : ContinuousAt (fun y : ℝ =>
          (HurwitzZeta.hurwitzEvenFEPair 0).f y -
            (HurwitzZeta.hurwitzEvenFEPair 0).f₀) x :=
        hfcont.sub continuousAt_const
      refine hcont.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with y hy
      have hy1 : 1 < y := hy
      have hy0 : 0 < y := one_pos.trans hy1
      simp [WeakFEPair.f_modif, hy1, hy0,
        not_lt_of_ge hy1.le]

/-- The lower cutoff whose Mellin transform is `1 / s`. -/
private def hardyLowerPoleCutoff (x : ℝ) : ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) x

/-- A pointwise representative of the two elementary pole terms. Away from `x = 1`
it is `1` below one and `x⁻¹ᐟ²` above one. -/
def hardyPoleKernel (x : ℝ) : ℂ :=
  hardyLowerPoleCutoff x +
    (x : ℂ) ^ (-(1 / 2 : ℂ)) * hardyLowerPoleCutoff x⁻¹

private theorem hasMellin_hardyUpperPole {s : ℂ} (hs : s.re < 1 / 2) :
    HasMellin
      (fun x : ℝ =>
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * hardyLowerPoleCutoff x⁻¹)
      s (1 / (1 / 2 - s)) := by
  have hbase :
      HasMellin hardyLowerPoleCutoff (-(s + (-(1 / 2 : ℂ))))
        (1 / (-(s + (-(1 / 2 : ℂ))))) := by
    apply hasMellin_one_Ioc
    norm_num
    linarith
  have hinv :
      MellinConvergent (fun x : ℝ => hardyLowerPoleCutoff x⁻¹)
        (s + (-(1 / 2 : ℂ))) := by
    have hraw :
        MellinConvergent
          (fun x : ℝ => hardyLowerPoleCutoff (x ^ (-1 : ℝ)))
          (s + (-(1 / 2 : ℂ))) := by
      apply
        (MellinConvergent.comp_rpow
          (f := hardyLowerPoleCutoff)
          (s := s + (-(1 / 2 : ℂ)))
          (a := -1) (by norm_num)).2
      convert hbase.1 using 1
      norm_num
      ring
    simpa only [Real.rpow_neg_one] using hraw
  constructor
  · exact
      (MellinConvergent.cpow_smul
        (f := fun x : ℝ => hardyLowerPoleCutoff x⁻¹)
        (s := s) (a := -(1 / 2 : ℂ))).2 hinv
  · change
      mellin
          (fun x : ℝ =>
            (x : ℂ) ^ (-(1 / 2 : ℂ)) •
              hardyLowerPoleCutoff x⁻¹) s =
        1 / (1 / 2 - s)
    rw [mellin_cpow_smul, mellin_comp_inv, hbase.2]
    ring

private theorem hasMellin_hardyPoleKernel {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    HasMellin hardyPoleKernel s
      (1 / s + 1 / (1 / 2 - s)) := by
  have hlower :
      HasMellin hardyLowerPoleCutoff s (1 / s) :=
    hasMellin_one_Ioc hs0
  have hupper := hasMellin_hardyUpperPole hs1
  unfold hardyPoleKernel
  constructor
  · exact (hasMellin_add hlower.1 hupper.1).1
  · rw [(hasMellin_add hlower.1 hupper.1).2, hlower.2, hupper.2]

private theorem mellin_hardyPoleKernel_quarter_eq (t : ℝ) :
    mellin hardyPoleKernel
        ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) =
      2 / (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
  have hm :=
    hasMellin_hardyPoleKernel
      (s := (((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I)
      (by norm_num) (by norm_num)
  rw [hm.2]
  have hden : (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 := by positivity
  have hdenC :
      ((((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hden
  have hq :
      ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) ≠ 0 := by
    intro h
    have hre := congr_arg Complex.re h
    norm_num at hre
  have hkq :
      (1 / 2 - ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I)) ≠ 0 := by
    intro h
    have hre := congr_arg Complex.re h
    norm_num at hre
  have hprod :
      ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) *
          (1 / 2 - ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I)) =
        ((((1 / 16 : ℝ) + t ^ 2 : ℝ) : ℂ)) := by
    ring_nf
    rw [Complex.I_sq]
    norm_num
    ring
  have hsmall : (1 / 16 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have hsmallC :
      ((((1 / 16 : ℝ) + t ^ 2 : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsmall
  have hscale :
      ((((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)) =
        4 * ((((1 / 16 : ℝ) + t ^ 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [one_div_add_one_div hq hkq, hprod, hscale]
  field_simp [hsmallC]
  ring

private theorem integrable_hardyPoleMellinLine :
    Integrable
      (fun t : ℝ =>
        2 / (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)) := by
  have hbase :
      Integrable (fun t : ℝ => (1 / 4 + 4 * t ^ 2)⁻¹) := by
    convert
      (integrable_inv_one_add_sq.comp_mul_left'
        (show (4 : ℝ) ≠ 0 by norm_num)).const_mul 4 using 1
    funext t
    field_simp
  have hreal :
      Integrable (fun t : ℝ => 2 / (1 / 4 + 4 * t ^ 2)) := by
    simpa only [div_eq_mul_inv] using hbase.const_mul 2
  have hcomplex :
      Integrable
        (fun t : ℝ =>
          ((2 / (1 / 4 + 4 * t ^ 2) : ℝ) : ℂ)) :=
    hreal.ofReal
  convert hcomplex using 1
  funext t
  push_cast
  rfl

private theorem verticalIntegrable_hardyPoleKernel :
    Complex.VerticalIntegrable (mellin hardyPoleKernel) (1 / 4) := by
  rw [Complex.VerticalIntegrable]
  refine integrable_hardyPoleMellinLine.congr
    (ae_of_all volume fun t => ?_)
  symm
  exact mellin_hardyPoleKernel_quarter_eq t

private theorem hardyPoleKernel_eq_one {x : ℝ}
    (hx : 0 < x) (hx1 : x < 1) :
    hardyPoleKernel x = 1 := by
  have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx).2 hx1
  simp [hardyPoleKernel, hardyLowerPoleCutoff, hx,
    hx1.le, not_le_of_gt hinv]

private theorem hardyPoleKernel_eq_cpow {x : ℝ}
    (hx : 1 < x) :
    hardyPoleKernel x = (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hx0 : 0 < x := one_pos.trans hx
  have hinv0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hinv1 : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx.le
  simp [hardyPoleKernel, hardyLowerPoleCutoff, hx0,
    hinv0, hinv1, not_le_of_gt hx]

/-- Mellin inversion evaluates the elementary rational pole kernel, away from the
chosen representative's doubled value at `x = 1`. -/
theorem hardyPoleMellinInv_eq_kernel {x : ℝ}
    (hx : 0 < x) (hx1 : x ≠ 1) :
    mellinInv (1 / 4) (mellin hardyPoleKernel) x =
      hardyPoleKernel x := by
  apply mellinInv_mellin_eq (1 / 4) _ hx
  · exact
      (hasMellin_hardyPoleKernel
        (s := (((1 / 4 : ℝ) : ℂ)))
        (by norm_num) (by norm_num)).1
  · exact verticalIntegrable_hardyPoleKernel
  · rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · have hnhds : Ioo 0 1 ∈ 𝓝 x := Ioo_mem_nhds hx hlt
      have hcont :
          ContinuousAt (fun _ : ℝ => (1 : ℂ)) x :=
        continuousAt_const
      refine hcont.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with y hy
      rw [hardyPoleKernel_eq_one hy.1 hy.2]
    · have hnhds : Ioi 1 ∈ 𝓝 x := Ioi_mem_nhds hgt
      have hcont :
          ContinuousAt
            (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 : ℂ))) x :=
        Complex.continuousAt_ofReal_cpow_const x (-(1 / 2 : ℂ))
          (.inr (one_pos.trans hgt).ne')
      refine hcont.congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with y hy
      rw [hardyPoleKernel_eq_cpow hy]

private theorem integrable_mellinPhase_mul_of_vertical
    {F : ℂ → ℂ} (hF : Complex.VerticalIntegrable F (1 / 4))
    {x : ℝ} (hx : 0 < x) :
    Integrable
      (fun t : ℝ =>
        (x : ℂ) ^
            (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) *
          F ((((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I))) := by
  rw [Complex.VerticalIntegrable] at hF
  have hphase :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (x : ℂ) ^
            (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I))) volume := by
    apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.2
    intro t
    exact
      (continuousAt_const_cpow
        (Complex.ofReal_ne_zero.mpr hx.ne')).comp (by fun_prop)
  apply hF.bdd_mul
    (c := x ^ (-(1 / 4 : ℝ))) hphase
  filter_upwards with t
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  norm_num

/-- The full-line integral obtained by inserting the critical-line xi identity into
Mellin inversion. This is Hardy's positive-real formula before the elementary rational
kernel is evaluated. -/
def hardyPositiveRealMellinIntegral (x : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ t : ℝ,
      (x : ℂ) ^
          (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) *
        (2 * (1 - 2 * (hardyXi (2 * t) : ℂ)) /
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ))

/-- The literal xi integral in Hardy's equation (1). -/
def hardyXiPositiveRealIntegral (x : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ t : ℝ,
      (x : ℂ) ^
          (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) *
        (4 * (hardyXi (2 * t) : ℂ) /
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ))

/-- Exact positive-real Hardy--Mellin identity, with the library's point representative
at `x = 1` excluded. -/
theorem hardyPositiveRealMellinIntegral_eq_f_modif
    {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    hardyPositiveRealMellinIntegral x =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  rw [← hardyMellinInv_eq_f_modif hx hx1]
  unfold hardyPositiveRealMellinIntegral mellinInv
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have hline :
      mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
          ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) =
        2 * (1 - 2 * (hardyXi (2 * t) : ℂ)) /
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
    convert hardyCompletedMellin_eq_xi t using 1 <;>
      push_cast <;>
      ring
  rw [hline]

/-- The source xi integral is exactly the difference between the elementary pole
kernel and the pole-subtracted theta representative. -/
theorem hardyXiPositiveRealIntegral_eq_pole_sub_f_modif
    {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    hardyXiPositiveRealIntegral x =
      hardyPoleKernel x -
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  have hpole :
      Integrable
        (fun t : ℝ =>
          (x : ℂ) ^
              (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) *
            mellin hardyPoleKernel
              ((((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I))) :=
    integrable_mellinPhase_mul_of_vertical
      verticalIntegrable_hardyPoleKernel hx
  have htheta :
      Integrable
        (fun t : ℝ =>
          (x : ℂ) ^
              (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) *
            mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
              ((((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I))) :=
    integrable_mellinPhase_mul_of_vertical
      verticalIntegrable_hardyCompletedMellin hx
  rw [← hardyPoleMellinInv_eq_kernel hx hx1,
    ← hardyMellinInv_eq_f_modif hx hx1]
  unfold hardyXiPositiveRealIntegral mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  rw [← mul_sub, ← integral_sub hpole htheta]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  have hpoleLine := mellin_hardyPoleKernel_quarter_eq t
  have hthetaLine :
      mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
          ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) =
        2 * (1 - 2 * (hardyXi (2 * t) : ℂ)) /
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
    convert hardyCompletedMellin_eq_xi t using 1 <;>
      push_cast <;>
      ring
  rw [hpoleLine, hthetaLine]
  ring

private theorem integrable_hardyXiMellinLine :
    Integrable
      (fun t : ℝ =>
        4 * (hardyXi (2 * t) : ℂ) /
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)) := by
  have hpole := verticalIntegrable_hardyPoleKernel
  have htheta := verticalIntegrable_hardyCompletedMellin
  rw [Complex.VerticalIntegrable] at hpole htheta
  have hdiff := hpole.sub htheta
  refine hdiff.congr (ae_of_all volume fun t => ?_)
  have hpoleLine := mellin_hardyPoleKernel_quarter_eq t
  have hthetaLine :
      mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
          ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) =
        2 * (1 - 2 * (hardyXi (2 * t) : ℂ)) /
          (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) := by
    convert hardyCompletedMellin_eq_xi t using 1 <;>
      push_cast <;>
      ring
  change
    mellin hardyPoleKernel
        ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) -
      mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
        ((((1 / 4 : ℝ) : ℂ)) + (t : ℂ) * I) =
      4 * (hardyXi (2 * t) : ℂ) /
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)
  rw [hpoleLine, hthetaLine]
  ring

private theorem continuousAt_hardyXiPositiveRealIntegral_one :
    ContinuousAt hardyXiPositiveRealIntegral 1 := by
  let G : ℝ → ℂ := fun t =>
    4 * (hardyXi (2 * t) : ℂ) /
      (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)
  let F : ℝ → ℝ → ℂ := fun x t =>
    (x : ℂ) ^
        (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)) * G t
  let bound : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) ^ (-(1 / 4 : ℝ)) * ‖G t‖
  have hG : Integrable G := by
    simpa only [G] using integrable_hardyXiMellinLine
  have hbound : Integrable bound := by
    exact hG.norm.const_mul ((1 / 2 : ℝ) ^ (-(1 / 4 : ℝ)))
  have hcore :
      Tendsto (fun x : ℝ => ∫ t : ℝ, F x t) (𝓝 1)
        (𝓝 (∫ t : ℝ, F 1 t)) := by
    apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
          (by norm_num : (1 : ℝ) < 3 / 2)] with x hxI
      have hx0 : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans hxI.1
      have hphase :
          Continuous (fun t : ℝ =>
            (x : ℂ) ^
              (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I))) := by
        apply continuous_iff_continuousAt.2
        intro t
        exact
          (continuousAt_const_cpow
            (Complex.ofReal_ne_zero.mpr hx0.ne')).comp (by fun_prop)
      exact hphase.aestronglyMeasurable.mul hG.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
          (by norm_num : (1 : ℝ) < 3 / 2)] with x hxI
      exact ae_of_all volume fun t => by
        have hx0 : 0 < x :=
          (by norm_num : (0 : ℝ) < 1 / 2).trans hxI.1
        dsimp only [F, bound]
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
        norm_num
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos
            (by norm_num : (0 : ℝ) < 1 / 2) hxI.1.le (by norm_num))
          (norm_nonneg _)
    · exact hbound
    · filter_upwards with t
      dsimp only [F]
      exact
        (Complex.continuousAt_ofReal_cpow_const 1
          (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * I))
          (.inr one_ne_zero)).mul continuousAt_const
  have hscaled :
      Tendsto
        (fun x : ℝ =>
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            ∫ t : ℝ, F x t)
        (𝓝 1)
        (𝓝 ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          ∫ t : ℝ, F 1 t)) :=
    continuousAt_const.mul hcore
  change
    Tendsto (fun x : ℝ => hardyXiPositiveRealIntegral x) (𝓝 1)
      (𝓝 (hardyXiPositiveRealIntegral 1))
  unfold hardyXiPositiveRealIntegral
  simpa only [F, G] using hscaled

/-- Hardy's source equation (1) away from the point representative used by the
Mellin inversion library. -/
private theorem hardyCahenMellinInversion_ne_one
    {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    1 + (x : ℂ) ^ (-(1 / 2 : ℂ)) -
        hardyXiPositiveRealIntegral x =
      (HurwitzZeta.evenKernel 0 x : ℂ) := by
  rw [hardyXiPositiveRealIntegral_eq_pole_sub_f_modif hx hx1]
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · rw [hardyPoleKernel_eq_one hx hlt]
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      hx, hlt, not_lt_of_ge hlt.le]
    have hcpow :
        (x : ℂ) ^ (-(2 : ℂ)⁻¹) =
          ((x ^ (-(2 : ℝ)⁻¹) : ℝ) : ℂ) := by
      convert
        (Complex.ofReal_cpow hx.le (-(2 : ℝ)⁻¹)).symm using 1
      norm_num
    rw [hcpow]
    ring
  · rw [hardyPoleKernel_eq_cpow hgt]
    have hx0 : 0 < x := one_pos.trans hgt
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      hx0, hgt, not_lt_of_ge hgt.le]
    ring

/-- Hardy's source equation (1) at the point where the auxiliary library
representatives are discontinuous but their source combination is continuous. -/
private theorem hardyCahenMellinInversion_one :
    1 + ((1 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) -
        hardyXiPositiveRealIntegral 1 =
      (HurwitzZeta.evenKernel 0 1 : ℂ) := by
  let lhs : ℝ → ℂ := fun x =>
    1 + (x : ℂ) ^ (-(1 / 2 : ℂ)) -
      hardyXiPositiveRealIntegral x
  let rhs : ℝ → ℂ := fun x =>
    (HurwitzZeta.evenKernel 0 x : ℂ)
  have hlhs : ContinuousAt lhs 1 := by
    exact
      (continuousAt_const.add
        (Complex.continuousAt_ofReal_cpow_const 1
          (-(1 / 2 : ℂ)) (.inr one_ne_zero))).sub
        continuousAt_hardyXiPositiveRealIntegral_one
  have hrhs : ContinuousAt rhs 1 := by
    change
      ContinuousAt
        (Complex.ofReal ∘ HurwitzZeta.evenKernel 0) 1
    exact
      ((Complex.continuous_ofReal.comp_continuousOn
          (HurwitzZeta.continuousOn_evenKernel 0)) 1
        (by norm_num : (1 : ℝ) ∈ Ioi 0)).continuousAt
          (Ioi_mem_nhds one_pos)
  have hlhsRight :
      Tendsto lhs (nhdsWithin 1 (Ioi 1)) (𝓝 (lhs 1)) :=
    hlhs.mono_left inf_le_left
  have hrhsRight :
      Tendsto rhs (nhdsWithin 1 (Ioi 1)) (𝓝 (rhs 1)) :=
    hrhs.mono_left inf_le_left
  have heq : lhs =ᶠ[nhdsWithin 1 (Ioi 1)] rhs := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hardyCahenMellinInversion_ne_one
      (one_pos.trans hx) (ne_of_gt hx)
  have hvalue : lhs 1 = rhs 1 :=
    tendsto_nhds_unique (hlhsRight.congr' heq) hrhsRight
  simpa only [lhs, rhs] using hvalue

/-- Hardy's exact Cahen--Mellin equation (1) for every positive real `x`. -/
theorem hardyCahenMellinInversion
    {x : ℝ} (hx : 0 < x) :
    1 + (x : ℂ) ^ (-(1 / 2 : ℂ)) -
        hardyXiPositiveRealIntegral x =
      (HurwitzZeta.evenKernel 0 x : ℂ) := by
  by_cases hx1 : x = 1
  · subst x
    exact hardyCahenMellinInversion_one
  · exact hardyCahenMellinInversion_ne_one hx hx1

/-- On the upper positive-real branch, the exact integral is theta with its
constant term removed. -/
theorem hardyPositiveRealMellinIntegral_eq_theta_sub_one
    {x : ℝ} (hx : 1 < x) :
    hardyPositiveRealMellinIntegral x =
      (HurwitzZeta.evenKernel 0 x : ℂ) - 1 := by
  rw [hardyPositiveRealMellinIntegral_eq_f_modif
    (one_pos.trans hx) (ne_of_gt hx)]
  simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
    hx, one_pos.trans hx, not_lt_of_ge hx.le]

/-- On the lower positive-real branch, the exact integral is theta with its
modular pole term removed. -/
theorem hardyPositiveRealMellinIntegral_eq_theta_sub_rpow
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    hardyPositiveRealMellinIntegral x =
      (HurwitzZeta.evenKernel 0 x : ℂ) -
        ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  rw [hardyPositiveRealMellinIntegral_eq_f_modif hx (ne_of_lt hx1)]
  simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
    hx, hx1, not_lt_of_ge hx1.le]

/-- Aggregate certificate for Hardy's positive-real theta inversion. -/
structure HardyThetaInversionCertificate : Prop where
  xiBound :
    ∀ t : ℝ,
      ‖hardyXi (2 * t)‖ ≤
        8 * ∫ u : ℝ in Ioi 0, ‖deBruijnNewmanPhi u‖
  completedVertical :
    Complex.VerticalIntegrable
      (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif)
      (1 / 4)
  inversion :
    ∀ {x : ℝ}, 0 < x → x ≠ 1 →
      mellinInv (1 / 4)
          (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif) x =
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x
  cahen :
    ∀ {x : ℝ}, 0 < x →
      1 + (x : ℂ) ^ (-(1 / 2 : ℂ)) -
          hardyXiPositiveRealIntegral x =
        (HurwitzZeta.evenKernel 0 x : ℂ)

theorem hardyThetaInversion_endpoint :
    HardyThetaInversionCertificate where
  xiBound := norm_hardyXi_two_mul_le_phiMass
  completedVertical := verticalIntegrable_hardyCompletedMellin
  inversion := hardyMellinInv_eq_f_modif
  cahen := hardyCahenMellinInversion

end

end LeanLab.Riemann
