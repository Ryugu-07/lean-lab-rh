import LeanLab.Riemann.ThetaInfinityMollifier
import LeanLab.Riemann.ZetaConvexity
import Mathlib.Analysis.Complex.RemovableSingularity

set_option linter.style.header false

/-!
# Bettin--Gonek auxiliary regularization

This module regularizes the auxiliary quotient in Bettin--Gonek equations (2.2)--(2.3).
It uses the divided difference of the pole-removed zeta function to patch both the zeta
pole and the selected-zero denominator, and it verifies the exact nonzero coefficient of
the selected simple pole in the contour kernel.

Mellin inversion, vertical decay, contour shifting, and the moment-to-power bridge are not
proved here.
-/

namespace LeanLab.Riemann

open Complex Filter Set
open scoped Topology

noncomputable section

/-- The zeta argument `w - 1/2 + i t` in the Bettin--Gonek auxiliary transform. -/
def bettinGonekShiftedArgument (t : ℝ) (w : ℂ) : ℂ :=
  w - 1 / 2 + t * Complex.I

/-- The `w`-plane pole corresponding to a selected zeta zero `rho`. -/
def bettinGonekSelectedPole (rho : ℂ) (t : ℝ) : ℂ :=
  rho + 1 / 2 - t * Complex.I

theorem bettinGonekShiftedArgument_selectedPole (rho : ℂ) (t : ℝ) :
    bettinGonekShiftedArgument t (bettinGonekSelectedPole rho t) = rho := by
  rw [bettinGonekShiftedArgument, bettinGonekSelectedPole]
  ring

theorem differentiable_bettinGonekShiftedArgument (t : ℝ) :
    Differentiable ℂ (bettinGonekShiftedArgument t) := by
  change Differentiable ℂ (fun w : ℂ => w - 1 / 2 + t * Complex.I)
  fun_prop

/-- The canonical holomorphic extension of `(s-1) zeta(s) / (s-rho)`. -/
def bettinGonekCancelledZeta (rho s : ℂ) : ℂ :=
  dslope zetaPoleRemoved rho s

theorem zetaPoleRemoved_eq_zero_of_nontrivialZero {rho : ℂ}
    (hrho : IsNontrivialZero rho) :
    zetaPoleRemoved rho = 0 := by
  rw [zetaPoleRemoved_eq hrho.2.2]
  apply mul_eq_zero.mpr
  exact Or.inr hrho.1

theorem bettinGonekCancelledZeta_eq_source {rho s : ℂ}
    (hrho : IsNontrivialZero rho) (hsrho : s ≠ rho) (hsone : s ≠ 1) :
    bettinGonekCancelledZeta rho s =
      (s - 1) * riemannZeta s / (s - rho) := by
  rw [bettinGonekCancelledZeta, dslope_of_ne _ hsrho, slope_fun_def_field]
  change (zetaPoleRemoved s - zetaPoleRemoved rho) / (s - rho) = _
  rw [zetaPoleRemoved_eq hsone, zetaPoleRemoved_eq_zero_of_nontrivialZero hrho]
  simp only [sub_zero, div_eq_mul_inv]

theorem differentiable_bettinGonekCancelledZeta (rho : ℂ) :
    Differentiable ℂ (bettinGonekCancelledZeta rho) := by
  change Differentiable ℂ (dslope zetaPoleRemoved rho)
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact differentiable_zetaPoleRemoved.differentiableOn

/-- The source auxiliary factor with its removable singularities patched. -/
def bettinGonekAuxiliaryG (rho : ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  (w - 1) ^ 2 *
      bettinGonekCancelledZeta rho (bettinGonekShiftedArgument t w) /
    ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)

/-- The raw displayed Bettin--Gonek auxiliary quotient, away from its patched points. -/
def bettinGonekAuxiliaryGRaw (rho : ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  (w - 1) ^ 2 *
      ((bettinGonekShiftedArgument t w - 1) *
        riemannZeta (bettinGonekShiftedArgument t w) /
        (bettinGonekShiftedArgument t w - rho)) /
    ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)

theorem bettinGonekAuxiliaryG_eq_raw {rho : ℂ} (hrho : IsNontrivialZero rho)
    (t : ℝ) {w : ℂ}
    (hrhoArg : bettinGonekShiftedArgument t w ≠ rho)
    (honeArg : bettinGonekShiftedArgument t w ≠ 1) :
    bettinGonekAuxiliaryG rho t w = bettinGonekAuxiliaryGRaw rho t w := by
  rw [bettinGonekAuxiliaryG, bettinGonekAuxiliaryGRaw,
    bettinGonekCancelledZeta_eq_source hrho hrhoArg honeArg]

/-- An open neighborhood of the source half-plane on which the rational denominators do not
vanish. -/
def bettinGonekAuxiliaryDomain : Set ℂ :=
  {w | -1 < w.re}

private theorem bettinGonek_add_one_ne_zero {w : ℂ}
    (hw : w ∈ bettinGonekAuxiliaryDomain) :
    w + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
  change -1 < w.re at hw
  linarith

private theorem bettinGonek_add_it_one_ne_zero {w : ℂ}
    (hw : w ∈ bettinGonekAuxiliaryDomain) (t : ℝ) :
    w + t * Complex.I + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    Complex.one_re, Complex.zero_re] at hre
  change -1 < w.re at hw
  linarith

theorem differentiableOn_bettinGonekAuxiliaryG {rho : ℂ}
    (_hrho : IsNontrivialZero rho) (t : ℝ) :
    DifferentiableOn ℂ (bettinGonekAuxiliaryG rho t) bettinGonekAuxiliaryDomain := by
  intro w hw
  have hcancel : DifferentiableAt ℂ
      (fun z : ℂ => bettinGonekCancelledZeta rho (bettinGonekShiftedArgument t z)) w :=
    (differentiable_bettinGonekCancelledZeta rho).differentiableAt.comp w
      (differentiable_bettinGonekShiftedArgument t).differentiableAt
  have hpoly : DifferentiableAt ℂ (fun z : ℂ => (z - 1) ^ 2) w := by
    fun_prop
  have hnum : DifferentiableAt ℂ
      (fun z : ℂ => (z - 1) ^ 2 *
        bettinGonekCancelledZeta rho (bettinGonekShiftedArgument t z)) w :=
    hpoly.mul hcancel
  have hden : DifferentiableAt ℂ
      (fun z : ℂ => (z + 1) ^ 2 * (z + t * Complex.I + 1) ^ 4) w := by
    fun_prop
  have hden_ne : (w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (bettinGonek_add_one_ne_zero hw))
      (pow_ne_zero 4 (bettinGonek_add_it_one_ne_zero hw t))
  exact (hnum.div hden hden_ne).differentiableWithinAt

/-- The rational contour kernel after multiplication by the source Mellin transform. -/
def bettinGonekJKernel (rho : ℂ) (t x : ℝ) (w : ℂ) : ℂ :=
  (w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w /
    ((w - bettinGonekSelectedPole rho t) *
      ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4))

/-- The selected-pole factor removed from the contour kernel. -/
def bettinGonekJKernelPoleRemoved (t x : ℝ) (w : ℂ) : ℂ :=
  (w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w /
    ((w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)

theorem bettinGonekJKernel_mul_poleFactor {rho w : ℂ} (t x : ℝ)
    (hw : w ≠ bettinGonekSelectedPole rho t) :
    (w - bettinGonekSelectedPole rho t) * bettinGonekJKernel rho t x w =
      bettinGonekJKernelPoleRemoved t x w := by
  let p := w - bettinGonekSelectedPole rho t
  let n := (w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w
  let D := (w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4
  change p * (n / (p * D)) = n / D
  rw [div_mul_eq_div_div, ← mul_div_assoc, mul_div_cancel₀ n (sub_ne_zero.mpr hw)]

theorem bettinGonekSelectedPole_sub_three_halves (rho : ℂ) (t : ℝ) :
    bettinGonekSelectedPole rho t - 3 / 2 + t * Complex.I = rho - 1 := by
  rw [bettinGonekSelectedPole]
  ring

theorem bettinGonekSelectedPole_add_one (rho : ℂ) (t : ℝ) :
    bettinGonekSelectedPole rho t + 1 = rho + 3 / 2 - t * Complex.I := by
  rw [bettinGonekSelectedPole]
  ring

theorem bettinGonekSelectedPole_add_it_one (rho : ℂ) (t : ℝ) :
    bettinGonekSelectedPole rho t + t * Complex.I + 1 = rho + 3 / 2 := by
  rw [bettinGonekSelectedPole]
  ring

/-- The exact coefficient displayed after the contour crosses the selected zero. -/
def bettinGonekResidueCoefficient (rho : ℂ) (t x : ℝ) : ℂ :=
  (x : ℂ) ^ (bettinGonekSelectedPole rho t) * (rho - 1) /
    ((rho + 3 / 2 - t * Complex.I) ^ 2 * (rho + 3 / 2) ^ 4)

theorem bettinGonekJKernelPoleRemoved_selectedPole (rho : ℂ) (t x : ℝ) :
    bettinGonekJKernelPoleRemoved t x (bettinGonekSelectedPole rho t) =
      bettinGonekResidueCoefficient rho t x := by
  rw [bettinGonekJKernelPoleRemoved, bettinGonekResidueCoefficient,
    bettinGonekSelectedPole_sub_three_halves,
    bettinGonekSelectedPole_add_one,
    bettinGonekSelectedPole_add_it_one]
  ring

private theorem bettinGonek_rho_add_three_halves_ne_zero {rho : ℂ}
    (hrho : IsNontrivialZero rho) :
    rho + 3 / 2 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  linarith [nontrivial_zero_re_pos hrho]

private theorem bettinGonek_rho_add_three_halves_sub_it_ne_zero {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t : ℝ) :
    rho + 3 / 2 - t * Complex.I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  linarith [nontrivial_zero_re_pos hrho]

theorem continuousAt_bettinGonekJKernelPoleRemoved_selectedPole
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (bettinGonekJKernelPoleRemoved t x)
      (bettinGonekSelectedPole rho t) := by
  have hpow : ContinuousAt (fun w : ℂ => (x : ℂ) ^ w)
      (bettinGonekSelectedPole rho t) :=
    continuousAt_const_cpow (Complex.ofReal_ne_zero.mpr hx.ne')
  have hlinear : ContinuousAt
      (fun w : ℂ => w - 3 / 2 + t * Complex.I)
      (bettinGonekSelectedPole rho t) := by
    fun_prop
  have hnum : ContinuousAt
      (fun w : ℂ => (w - 3 / 2 + t * Complex.I) * (x : ℂ) ^ w)
      (bettinGonekSelectedPole rho t) := hlinear.mul hpow
  have hden : ContinuousAt
      (fun w : ℂ => (w + 1) ^ 2 * (w + t * Complex.I + 1) ^ 4)
      (bettinGonekSelectedPole rho t) := by fun_prop
  have hden_ne :
      (bettinGonekSelectedPole rho t + 1) ^ 2 *
          (bettinGonekSelectedPole rho t + t * Complex.I + 1) ^ 4 ≠ 0 := by
    rw [bettinGonekSelectedPole_add_one, bettinGonekSelectedPole_add_it_one]
    exact mul_ne_zero
      (pow_ne_zero 2 (bettinGonek_rho_add_three_halves_sub_it_ne_zero hrho t))
      (pow_ne_zero 4 (bettinGonek_rho_add_three_halves_ne_zero hrho))
  exact hnum.div hden hden_ne

theorem tendsto_bettinGonekJKernel_selectedPole
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun w : ℂ => (w - bettinGonekSelectedPole rho t) *
        bettinGonekJKernel rho t x w)
      (𝓝[≠] bettinGonekSelectedPole rho t)
      (𝓝 (bettinGonekResidueCoefficient rho t x)) := by
  have htendsto : Tendsto (bettinGonekJKernelPoleRemoved t x)
      (𝓝[≠] bettinGonekSelectedPole rho t)
      (𝓝 (bettinGonekJKernelPoleRemoved t x (bettinGonekSelectedPole rho t))) :=
    (continuousAt_bettinGonekJKernelPoleRemoved_selectedPole hrho t hx).tendsto.mono_left
      nhdsWithin_le_nhds
  rw [bettinGonekJKernelPoleRemoved_selectedPole] at htendsto
  apply htendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (bettinGonekJKernel_mul_poleFactor t x hw).symm

theorem bettinGonekResidueCoefficient_ne_zero
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    bettinGonekResidueCoefficient rho t x ≠ 0 := by
  rw [bettinGonekResidueCoefficient]
  apply div_ne_zero
  · exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne')))
      (sub_ne_zero.mpr hrho.2.2)
  · exact mul_ne_zero
      (pow_ne_zero 2 (bettinGonek_rho_add_three_halves_sub_it_ne_zero hrho t))
      (pow_ne_zero 4 (bettinGonek_rho_add_three_halves_ne_zero hrho))

/-- The fixed auxiliary endpoint: source-half-plane holomorphy and an actual nonzero selected
simple-pole coefficient. -/
theorem bettinGonekAuxiliaryAudit_endpoint
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (bettinGonekAuxiliaryG rho t) bettinGonekAuxiliaryDomain ∧
      Tendsto
        (fun w : ℂ => (w - bettinGonekSelectedPole rho t) *
          bettinGonekJKernel rho t x w)
        (𝓝[≠] bettinGonekSelectedPole rho t)
        (𝓝 (bettinGonekResidueCoefficient rho t x)) ∧
      bettinGonekResidueCoefficient rho t x ≠ 0 :=
  ⟨differentiableOn_bettinGonekAuxiliaryG hrho t,
    tendsto_bettinGonekJKernel_selectedPole hrho t hx,
    bettinGonekResidueCoefficient_ne_zero hrho t hx⟩

end

end LeanLab.Riemann
