import LeanLab.Riemann.LevinsonMontgomeryHeightTenCompleteBoundary
import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelHeatExpansion
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Riemann--Siegel low-zero bridge for the height-ten boundary

This module connects the exact Titchmarsh--Riemann--Siegel contour identity developed for the
de Bruijn--Newman route to the low critical-line nonvanishing input in the height-ten
Levinson--Montgomery certificate. It exposes the exact one-residue remainder margin and proves
all downstream consumers. The uniform margin itself remains open.
-/

open Complex Finset MeasureTheory Real
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

def heightTenRiemannSiegelFiniteRight (N : ℕ) (s : ℂ) : ℂ :=
  (∑ k ∈ Finset.range N,
      deBruijnNewmanRiemannSiegelR0Term (k + 1) s) +
    deBruijnNewmanRiemannSiegelR0N N s

theorem heightTenRiemannSiegelFiniteRight_one (s : ℂ) :
    heightTenRiemannSiegelFiniteRight 1 s =
      deBruijnNewmanRiemannSiegelPrefactor s +
        deBruijnNewmanRiemannSiegelR0N 1 s := by
  simp [heightTenRiemannSiegelFiniteRight,
    deBruijnNewmanRiemannSiegelR0Term]

theorem riemannSiegel_criticalLine_eq_add_conj
    {N : ℕ} {s : ℂ} (hsRe : s.re = 1 / 2)
    (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      heightTenRiemannSiegelFiniteRight N s +
        conj (heightTenRiemannSiegelFiniteRight N s) := by
  have h := deBruijnNewmanRiemannSiegel_xio_finite N hs
  have hconj : conj (1 - s) = s := by
    apply Complex.ext <;> norm_num [hsRe]
  simpa only [heightTenRiemannSiegelFiniteRight,
    deBruijnNewmanRiemannSiegelReflect, hconj, map_add, map_sum] using h

theorem riemannSiegel_criticalLine_one_eq_two_re
    {s : ℂ} (hsRe : s.re = 1 / 2)
    (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      2 * ((heightTenRiemannSiegelFiniteRight 1 s).re : ℂ) := by
  rw [riemannSiegel_criticalLine_eq_add_conj hsRe hs]
  calc
    heightTenRiemannSiegelFiniteRight 1 s +
          conj (heightTenRiemannSiegelFiniteRight 1 s) =
        2 * ((heightTenRiemannSiegelFiniteRight 1 s +
          conj (heightTenRiemannSiegelFiniteRight 1 s)) / 2) := by ring
    _ = 2 * ((heightTenRiemannSiegelFiniteRight 1 s).re : ℂ) := by
      rw [← Complex.re_eq_add_conj]

theorem riemannSiegel_criticalLine_one_eq_prefactor_remainder_re
    {s : ℂ} (hsRe : s.re = 1 / 2)
    (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      2 * ((deBruijnNewmanRiemannSiegelPrefactor s +
        deBruijnNewmanRiemannSiegelR0N 1 s).re : ℂ) := by
  rw [riemannSiegel_criticalLine_one_eq_two_re hsRe hs,
    heightTenRiemannSiegelFiniteRight_one]

theorem riemannXi_ne_zero_of_riemannSiegel_one_re_ne_zero
    {s : ℂ} (hsRe : s.re = 1 / 2)
    (hs : deBruijnNewmanRiemannSiegelIsNoninteger s)
    (hRe : (deBruijnNewmanRiemannSiegelPrefactor s +
      deBruijnNewmanRiemannSiegelR0N 1 s).re ≠ 0) :
    riemannXi s ≠ 0 := by
  intro hxi
  have h := riemannSiegel_criticalLine_one_eq_prefactor_remainder_re hsRe hs
  rw [hxi] at h
  norm_num at h
  apply hRe
  rw [Complex.add_re]
  exact_mod_cast h

theorem riemannXi_ne_zero_of_riemannSiegel_one_remainder_margin
    {s : ℂ} (hsRe : s.re = 1 / 2)
    (hs : deBruijnNewmanRiemannSiegelIsNoninteger s)
    (hmargin :
      |(deBruijnNewmanRiemannSiegelR0N 1 s).re| <
        |(deBruijnNewmanRiemannSiegelPrefactor s).re|) :
    riemannXi s ≠ 0 := by
  apply riemannXi_ne_zero_of_riemannSiegel_one_re_ne_zero hsRe hs
  intro hzero
  have hzero' :
      (deBruijnNewmanRiemannSiegelPrefactor s).re +
        (deBruijnNewmanRiemannSiegelR0N 1 s).re = 0 := by
    simpa only [Complex.add_re] using hzero
  have hre :
      (deBruijnNewmanRiemannSiegelR0N 1 s).re =
        -(deBruijnNewmanRiemannSiegelPrefactor s).re := by
    linarith
  rw [hre, abs_neg] at hmargin
  exact (lt_irrefl _) hmargin

theorem riemannZeta_ne_zero_of_riemannXi_ne_zero_on_criticalLine
    {s : ℂ} (hsRe : s.re = 1 / 2) (hxi : riemannXi s ≠ 0) :
    riemannZeta s ≠ 0 := by
  have hsPos : 0 < s.re := by rw [hsRe]; norm_num
  have hsOne : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [hsRe] at hre
  intro hzeta
  apply hxi
  rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos
    hsPos hsOne, hzeta, mul_zero]

def HeightTenRiemannSiegelOneRemainderMargin : Prop :=
  ∀ y : ℝ, 13 / 2 ≤ y → y ≤ 10 →
    |(deBruijnNewmanRiemannSiegelR0N 1
      ((1 / 2 : ℂ) + (y : ℂ) * I)).re| <
      |(deBruijnNewmanRiemannSiegelPrefactor
        ((1 / 2 : ℂ) + (y : ℂ) * I)).re|

theorem riemannZeta_criticalLine_ne_zero_thirteenHalves_ten_of_riemannSiegel
    (hmargin : HeightTenRiemannSiegelOneRemainderMargin)
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
  let s : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  have hsRe : s.re = 1 / 2 := by norm_num [s]
  have hyPos : 0 < y := by linarith
  have hsNoninteger : deBruijnNewmanRiemannSiegelIsNoninteger s :=
    by
      simpa using
        (deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero
          (s := s) (by simpa [s] using hyPos.ne') 0)
  have hxi :=
    riemannXi_ne_zero_of_riemannSiegel_one_remainder_margin
      hsRe hsNoninteger (by simpa [s] using hmargin y hy0 hy1)
  exact riemannZeta_ne_zero_of_riemannXi_ne_zero_on_criticalLine
    hsRe hxi

theorem speiserZetaDerivRatio_rightVertical_re_neg_thirteenHalves_ten_of_riemannSiegel
    (hmargin : HeightTenRiemannSiegelOneRemainderMargin)
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    (speiserZetaDerivRatio
      ((1 / 2 : ℂ) + (y : ℂ) * I)).re < 0 := by
  exact speiserZetaDerivRatio_rightVertical_re_neg_of_thirteenHalves_le
    hy0
    (riemannZeta_criticalLine_ne_zero_thirteenHalves_ten_of_riemannSiegel
      hmargin hy0 hy1)

theorem norm_deBruijnNewmanRiemannSiegelRawIntegral_le_globalMajorant
    (N : ℕ) (s : ℂ) :
    ‖deBruijnNewmanRiemannSiegelRawIntegral N s‖ ≤
      (1 / 2) *
        Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant N s) *
          Real.sqrt 2 := by
  have hbound := MeasureTheory.norm_integral_le_of_norm_le
    (integrable_deBruijnNewmanRiemannSiegelMajorant N s)
    (ae_of_all _ fun v =>
      norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_majorant N s v)
  unfold deBruijnNewmanRiemannSiegelRawIntegral
  apply hbound.trans_eq
  unfold deBruijnNewmanRiemannSiegelMajorant
  rw [integral_const_mul, integral_gaussian]
  congr 2
  field_simp [Real.pi_ne_zero]

theorem one_lt_riemannSiegel_globalMajorant_rhs_on_heightTenHigh
    {y : ℝ} (hy : 13 / 2 ≤ y) :
    1 <
      (1 / 2) * Real.exp
        (deBruijnNewmanRiemannSiegelMajorantConstant 1
          ((1 / 2 : ℂ) + (y : ℂ) * I)) * Real.sqrt 2 := by
  let s : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  have hyPos : 0 < y := by linarith
  have hsIm : s.im = y := by simp [s]
  have himTerm : 1 < |s.im| * Real.pi := by
    rw [hsIm, abs_of_pos hyPos]
    nlinarith [Real.pi_gt_three]
  have hrest :
      0 ≤ |s.re| * ((1 : ℝ) + 1 / 2 + 4) +
        deBruijnNewmanRiemannSiegelLinearRate 1 s ^ 2 /
          (2 * Real.pi) := by positivity
  have hconstant :
      1 < deBruijnNewmanRiemannSiegelMajorantConstant 1 s := by
    unfold deBruijnNewmanRiemannSiegelMajorantConstant
    nlinarith
  have hexp :
      2 < Real.exp
        (deBruijnNewmanRiemannSiegelMajorantConstant 1 s) :=
    exp_one_gt_two.trans (Real.exp_lt_exp.mpr hconstant)
  have hsqrt : 1 ≤ Real.sqrt 2 := by simp
  change 1 < (1 / 2) *
    Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant 1 s) *
      Real.sqrt 2
  calc
    1 = (1 / 2 : ℝ) * 2 * 1 := by norm_num
    _ ≤ (1 / 2 : ℝ) * 2 * Real.sqrt 2 := by gcongr
    _ < (1 / 2 : ℝ) *
        Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant 1 s) *
          Real.sqrt 2 := by gcongr

end

end LeanLab.Riemann
