import LeanLab.Riemann.LevinsonMontgomeryHeightTenCompleteBoundary

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Height-ten left high boundary

This module proves the positive imaginary-axis zeta nonvanishing structurally and closes the
Levinson--Montgomery left vertical sign for `y >= 7`. The remaining preregistered high interval
`13/2 <= y <= 7` still requires the actual paired-zero contribution or direct zeta evaluation.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

theorem riemannZeta_ne_zero_on_positive_imaginaryAxis
    {y : ℝ} (hy : 0 < y) :
    riemannZeta ((y : ℂ) * I) ≠ 0 := by
  let s : ℂ := (y : ℂ) * I
  have hsRe : s.re = 0 := by simp [s]
  have hsIm : 0 < s.im := by simpa [s] using hy
  have hsZero : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [s] at him
    linarith
  have hsOne : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s] at him
    linarith
  have hnotpole : ∀ m : ℕ, s ≠ -(2 * m) := by
    intro m h
    have him : s.im = 0 := by simpa using congrArg Complex.im h
    linarith
  have hgamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_neg_even hnotpole
  have hxi : riemannXi s ≠ 0 := by
    intro hzero
    have hsNontrivial : IsNontrivialZero s :=
      (isNontrivialZero_iff_riemannXi_eq_zero s).2 hzero
    have hsRePos := speiser_nontrivial_zero_re_pos hsNontrivial
    linarith
  have hxiValue :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
      hsZero hsOne hgamma
  intro hzeta
  apply hxi
  rw [hxiValue, hzeta]
  ring

theorem levinsonMontgomeryArchimedean_imaginaryAxis_neg_of_seven_le
    {y : ℝ} (hy : 7 ≤ y) :
    levinsonMontgomeryLogDerivArchimedeanTerm ((y : ℂ) * I) < 0 := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := s / 2 + 1
  let W : ℂ := w + 1
  have hwRe : w.re = 1 := by
    norm_num [w, s, div_re]
  have hWRe : W.re = 2 := by
    norm_num [W, w, s, div_re]
  have hwRePos : 0 < w.re := by rw [hwRe]; norm_num
  have hWRePos : 0 < W.re := by rw [hWRe]; norm_num
  have hwNormSqComplex : 53 / 4 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]
    norm_num [w, s, div_re, div_im]
    nlinarith
  have hWNormSqComplex : 65 / 4 ≤ Complex.normSq W := by
    rw [Complex.normSq_apply]
    norm_num [W, w, s, div_re, div_im]
    nlinarith
  have hWNormSq : 65 / 4 ≤ ‖W‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hWNormSqComplex
  have hWNorm : 79 / 20 ≤ ‖W‖ := by
    have hnormNonneg : 0 ≤ ‖W‖ := norm_nonneg W
    nlinarith
  have hlogW : (1373 / 1000 : ℝ) < Real.log ‖W‖ := by
    exact
      log_seventyNine_div_twenty_gt_oneThousandThreeHundredSeventyThree_div_oneThousand.trans_le
        (Real.log_le_log (by norm_num) hWNorm)
  have hlogPi : Real.log Real.pi < (229 / 200 : ℝ) :=
    log_pi_lt_twoHundredTwentyNine_div_twoHundred
  have hPoleDen : 50 ≤ Complex.normSq (s - 1) := by
    rw [Complex.normSq_apply]
    norm_num [s]
    nlinarith
  have hPoleDenPos : 0 < Complex.normSq (s - 1) :=
    lt_of_lt_of_le (by norm_num) hPoleDen
  have hPole : -(1 / (s - 1)).re ≤ 1 / 50 := by
    have hEq :
        -(1 / (s - 1)).re =
          (1 - s.re) / Complex.normSq (s - 1) := by
      rw [one_div, Complex.inv_re]
      simp only [sub_re, one_re]
      ring
    rw [hEq, div_le_iff₀ hPoleDenPos]
    norm_num [s]
    nlinarith
  have hWNormSqPos : 0 < Complex.normSq W :=
    lt_of_lt_of_le (by norm_num) hWNormSqComplex
  have hInvCorrection : (1 / (2 * W)).re / 2 ≤ 2 / 65 := by
    have hEq :
        (1 / (2 * W)).re / 2 = W.re / (4 * Complex.normSq W) := by
      rw [one_div, Complex.inv_re]
      norm_num [Complex.normSq_mul]
      ring
    rw [hEq, hWRe, div_le_iff₀ (mul_pos (by norm_num) hWNormSqPos)]
    nlinarith
  have hwNormSqPos : 0 < Complex.normSq w :=
    lt_of_lt_of_le (by norm_num) hwNormSqComplex
  have hwInv : (1 / w).re / 2 ≤ 2 / 53 := by
    have hEq : (1 / w).re / 2 = w.re / (2 * Complex.normSq w) := by
      rw [one_div, Complex.inv_re]
      ring
    rw [hEq, hwRe, div_le_iff₀ (mul_pos (by norm_num) hwNormSqPos)]
    nlinarith
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder W
  have hRnorm : ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) :=
    levinsonMontgomery_digamma_stirling_remainder_norm_le hWRePos
  have hRsmall : ‖R‖ ≤ 27 / 1040 := by
    calc
      ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) := hRnorm
      _ ≤ 27 / 1040 := by
        have hden : 0 < 64 * ‖W‖ ^ 2 := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
  have hRreal : -R.re / 2 ≤ 27 / 2080 := by
    have hre : -R.re ≤ ‖R‖ :=
      (neg_le_abs R.re).trans (Complex.abs_re_le_norm R)
    linarith
  have hnotpole : ∀ m : ℕ, w ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num [hwRe] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hshift := Complex.digamma_apply_add_one w hnotpole
  have hstirling := levinsonMontgomery_digamma_stirling hWRePos
  change Complex.digamma W = Complex.log W - 1 / (2 * W) + R at hstirling
  have hdigamma :
      Complex.digamma w =
        Complex.log W - 1 / (2 * W) + R - 1 / w := by
    calc
      Complex.digamma w = Complex.digamma (w + 1) - 1 / w := by
        rw [hshift]
        ring
      _ = Complex.log W - 1 / (2 * W) + R - 1 / w := by
        rw [show w + 1 = W by rfl, hstirling]
  have hterm :
      levinsonMontgomeryLogDerivArchimedeanTerm s =
        -(1 / (s - 1)).re + Real.log Real.pi / 2 -
          Real.log ‖W‖ / 2 + (1 / (2 * W)).re / 2 +
          (1 / w).re / 2 - R.re / 2 := by
    rw [levinsonMontgomeryLogDerivArchimedeanTerm,
      show s / 2 + 1 = w by rfl, hdigamma]
    simp only [Complex.add_re, Complex.sub_re, Complex.log_re]
    ring
  change levinsonMontgomeryLogDerivArchimedeanTerm s < 0
  rw [hterm]
  nlinarith

theorem speiserZetaDerivRatio_leftVertical_re_neg_of_seven_le
    {y : ℝ} (hy : 7 ≤ y) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).re < 0 := by
  have hyPos : 0 < y := by linarith
  have hzeta := riemannZeta_ne_zero_on_positive_imaginaryAxis hyPos
  have hupper :=
    logDeriv_riemannZeta_re_le_archimedean_on_imaginaryAxis hyPos hzeta
  have hneg :=
    levinsonMontgomeryArchimedean_imaginaryAxis_neg_of_seven_le hy
  simpa only [speiserZetaDerivRatio, logDeriv_apply] using
    (show (logDeriv riemannZeta ((y : ℂ) * I)).re < 0 by linarith)

theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_seven_le
    {y : ℝ} (hy : 7 ≤ y) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane := by
  have hneg := speiserZetaDerivRatio_leftVertical_re_neg_of_seven_le hy
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num
  exact ne_of_lt hneg

end

end LeanLab.Riemann
