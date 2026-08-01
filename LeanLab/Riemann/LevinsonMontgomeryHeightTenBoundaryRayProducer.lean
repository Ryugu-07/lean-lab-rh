import LeanLab.Riemann.LevinsonMontgomeryHeightTenRotatedSlitWinding

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Height-ten boundary ray producer

The first corrected Euler--Maclaurin formula at cutoff one proves that both `zeta` and its
derivative are strictly negative on the real segment from zero to one half. Consequently the
Speiser quotient is positive there, so rotation by `I` places the complete bottom edge in the
principal slit plane. The full rotated-slit boundary certificate is then reduced to the two
vertical edges and the existing strict top-edge sign target.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

private theorem eulerMaclaurinOneZetaApprox_real_one (sigma : ℝ) :
    eulerMaclaurinOneZetaApprox (sigma : ℂ) 1 =
      1 / 2 - 1 / (1 - (sigma : ℂ)) := by
  unfold eulerMaclaurinOneZetaApprox abelZetaApprox
  simp [zetaPartialSum]
  ring

private theorem eulerMaclaurinOneZetaDerivApprox_real_one
    (sigma : ℝ) (hsigma : sigma ≠ 1) :
    eulerMaclaurinOneZetaDerivApprox (sigma : ℂ) 1 =
      -1 / (1 - (sigma : ℂ)) ^ 2 := by
  rw [eulerMaclaurinOneZetaDerivApprox_eq_finiteFormula (sigma : ℂ)
    (by exact_mod_cast hsigma) (by norm_num)]
  simp [eulerMaclaurinOneZetaDerivFiniteFormula]
  ring

private theorem eulerMaclaurinOneZetaError_real_one
    (sigma : ℝ) (hsigma0 : 0 ≤ sigma) :
    eulerMaclaurinOneZetaError (sigma : ℂ) 1 = sigma / 8 := by
  unfold eulerMaclaurinOneZetaError
  rw [show ‖((sigma : ℂ) * ((sigma : ℂ) + 1))‖ = sigma * (sigma + 1) by
    rw [norm_mul, show (sigma : ℂ) + 1 = ((sigma + 1 : ℝ) : ℂ) by norm_num,
      norm_real, norm_real]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hsigma0, abs_of_nonneg (by linarith)]]
  norm_num
  have hsigmaOne : sigma + 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp [hsigmaOne]

private theorem eulerMaclaurinOneZetaDerivError_real_one
    (sigma : ℝ) (hsigma0 : 0 ≤ sigma) :
    eulerMaclaurinOneZetaDerivError (sigma : ℂ) 1 =
      (3 * sigma + 1) / (8 * (sigma + 1)) := by
  unfold eulerMaclaurinOneZetaDerivError
  have hnormOne : ‖(2 : ℂ) * (sigma : ℂ) + 1‖ = 2 * sigma + 1 := by
    rw [show (2 : ℂ) * (sigma : ℂ) + 1 = ((2 * sigma + 1 : ℝ) : ℂ) by
      norm_num]
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hnormTwo :
      ‖(sigma : ℂ) * ((sigma : ℂ) + 1)‖ = sigma * (sigma + 1) := by
    rw [norm_mul, show (sigma : ℂ) + 1 = ((sigma + 1 : ℝ) : ℂ) by norm_num,
      norm_real, norm_real]
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hsigma0, abs_of_nonneg (by linarith)]
  rw [hnormOne, hnormTwo]
  norm_num
  field_simp
  ring

private theorem riemannZeta_realSegment_re_neg_of_pos
    (sigma : ℝ) (hsigma0 : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2) :
    (riemannZeta (sigma : ℂ)).re < 0 := by
  have hsigmaOne : sigma ≠ 1 := by linarith
  have hsigmaComplexOne : (sigma : ℂ) ≠ 1 := by exact_mod_cast hsigmaOne
  have hbound := norm_riemannZeta_sub_eulerMaclaurinOneZetaApprox_le_of_re_pos
    hsigmaComplexOne (by simpa using hsigma0) (N := 1) (by norm_num)
  rw [eulerMaclaurinOneZetaApprox_real_one sigma,
    eulerMaclaurinOneZetaError_real_one sigma hsigma0.le] at hbound
  have hreAbs := (Complex.abs_re_le_norm
    (riemannZeta (sigma : ℂ) - (1 / 2 - 1 / (1 - (sigma : ℂ))))).trans hbound
  have hcenter : ((1 / 2 - 1 / (1 - (sigma : ℂ)) : ℂ)).re =
      1 / 2 - 1 / (1 - sigma) := by
    norm_num [Complex.div_re, Complex.normSq]
  rw [Complex.sub_re, hcenter] at hreAbs
  have hreDiff : (riemannZeta (sigma : ℂ)).re -
      (1 / 2 - 1 / (1 - sigma)) ≤ sigma / 8 :=
    (le_abs_self _).trans hreAbs
  have hden : 0 < 1 - sigma := by linarith
  have hrecip : 1 / 2 + sigma / 8 < 1 / (1 - sigma) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  linarith

private theorem deriv_riemannZeta_realSegment_re_neg_of_pos
    (sigma : ℝ) (hsigma0 : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2) :
    (deriv riemannZeta (sigma : ℂ)).re < 0 := by
  have hsigmaOne : sigma ≠ 1 := by linarith
  have hsigmaComplexOne : (sigma : ℂ) ≠ 1 := by exact_mod_cast hsigmaOne
  have hbound :=
    norm_deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox_le_of_re_pos
      hsigmaComplexOne (by simpa using hsigma0) (N := 1) (by norm_num)
  rw [eulerMaclaurinOneZetaDerivApprox_real_one sigma hsigmaOne,
    eulerMaclaurinOneZetaDerivError_real_one sigma hsigma0.le] at hbound
  have hreAbs := (Complex.abs_re_le_norm
    (deriv riemannZeta (sigma : ℂ) -
      (-1 / (1 - (sigma : ℂ)) ^ 2))).trans hbound
  have hden : 0 < 1 - sigma := by linarith
  have hcenter : ((-1 / (1 - (sigma : ℂ)) ^ 2 : ℂ)).re =
      -1 / (1 - sigma) ^ 2 := by
    norm_num [Complex.div_re, Complex.normSq, pow_two]
    field_simp [ne_of_gt hden]
  rw [Complex.sub_re, hcenter] at hreAbs
  have hreDiff : (deriv riemannZeta (sigma : ℂ)).re -
      (-1 / (1 - sigma) ^ 2) ≤ (3 * sigma + 1) / (8 * (sigma + 1)) :=
    (le_abs_self _).trans hreAbs
  have herror : (3 * sigma + 1) / (8 * (sigma + 1)) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hrecip : 1 ≤ 1 / (1 - sigma) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hden)]
    nlinarith
  have hmargin : -1 / (1 - sigma) ^ 2 +
      (3 * sigma + 1) / (8 * (sigma + 1)) < 0 := by
    rw [neg_div]
    linarith
  linarith

theorem riemannZeta_realSegment_re_neg
    (sigma : ℝ) (hsigma : sigma ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (riemannZeta (sigma : ℂ)).re < 0 := by
  rcases eq_or_lt_of_le hsigma.1 with hzero | hpos
  · subst sigma
    change (riemannZeta (0 : ℂ)).re < 0
    rw [riemannZeta_zero]
    norm_num
  · exact riemannZeta_realSegment_re_neg_of_pos sigma hpos hsigma.2

theorem deriv_riemannZeta_realSegment_re_neg
    (sigma : ℝ) (hsigma : sigma ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    (deriv riemannZeta (sigma : ℂ)).re < 0 := by
  rcases eq_or_lt_of_le hsigma.1 with hzero | hpos
  · subst sigma
    change (deriv riemannZeta (0 : ℂ)).re < 0
    rw [deriv_riemannZeta_zero]
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_log (show 0 ≤ 2 * Real.pi by positivity)]
    norm_num
    have htwoPi : (1 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    linarith [Real.log_pos htwoPi]
  · exact deriv_riemannZeta_realSegment_re_neg_of_pos sigma hpos hsigma.2

private theorem riemannZeta_ofReal_im_eq_zero (sigma : ℝ) :
    (riemannZeta (sigma : ℂ)).im = 0 := by
  have hconj := riemannZeta_conj (sigma : ℂ)
  have him := congrArg Complex.im hconj
  norm_num at him
  linarith

private theorem deriv_riemannZeta_ofReal_im_eq_zero (sigma : ℝ) :
    (deriv riemannZeta (sigma : ℂ)).im = 0 := by
  have hconj := deriv_riemannZeta_conj (sigma : ℂ)
  have him := congrArg Complex.im hconj
  norm_num at him
  linarith

theorem speiserZetaDerivRatio_realSegment_re_pos
    (sigma : ℝ) (hsigma : sigma ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 < (speiserZetaDerivRatio (sigma : ℂ)).re := by
  have hzeta := riemannZeta_realSegment_re_neg sigma hsigma
  have hderiv := deriv_riemannZeta_realSegment_re_neg sigma hsigma
  have hzetaIm := riemannZeta_ofReal_im_eq_zero sigma
  have hderivIm := deriv_riemannZeta_ofReal_im_eq_zero sigma
  have hzetaNe : riemannZeta (sigma : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num at hre
    linarith
  rw [speiserZetaDerivRatio, Complex.div_re, hzetaIm, hderivIm]
  norm_num
  exact div_pos (mul_pos_of_neg_of_neg hderiv hzeta)
    (Complex.normSq_pos.mpr hzetaNe)

theorem speiserBottom_mem_rotatedSlit
    (sigma : ℝ) (hsigma : sigma ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    I * speiserZetaDerivRatio (sigma : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num
  exact ne_of_gt (speiserZetaDerivRatio_realSegment_re_pos sigma hsigma)

def SpeiserPositiveImaginaryRayVerticalBoundary (t : ℝ) : Prop :=
  (∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane) ∧
  (∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) t →
    I * speiserZetaDerivRatio ((1 / 2 : ℂ) + y * I) ∈ Complex.slitPlane)

theorem SpeiserStrictNegativeHorizontal.toRotatedSlitBoundary_of_vertical
    {t : ℝ} (hsign : SpeiserStrictNegativeHorizontal t)
    (hvertical : SpeiserPositiveImaginaryRayVerticalBoundary t) :
    SpeiserRotatedSlitBoundary I t := by
  refine ⟨hsign.1, I_ne_zero, speiserBottom_mem_rotatedSlit, ?_,
    hvertical.1, hvertical.2⟩
  intro sigma hsigma
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num
  exact ne_of_lt (hsign.2 sigma hsigma).2.2

theorem levinsonMontgomeryHeightTenCertificate_of_verticalRayAvoidance
    (hsign : SpeiserStrictNegativeHorizontal 10)
    (hvertical : SpeiserPositiveImaginaryRayVerticalBoundary 10) :
    LevinsonMontgomeryHeightTenCertificate := by
  exact levinsonMontgomeryHeightTenCertificate_of_positiveImaginaryRayAvoidance hsign
    (hsign.toRotatedSlitBoundary_of_vertical hvertical)

end

end LeanLab.Riemann
