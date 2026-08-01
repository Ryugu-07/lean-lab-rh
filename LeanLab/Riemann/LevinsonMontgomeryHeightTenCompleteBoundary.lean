import LeanLab.Riemann.LevinsonMontgomeryHeightTenBoundaryRayProducer

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Height-ten complete-boundary structural reductions

This module exposes the exact critical-line and positive-height logarithmic-derivative identities
used by the complete height-ten boundary attack. It also proves a nonoptimized negative
archimedean sign above height `13/2` on the critical line. The actual low-height nonvanishing and
the remaining vertical and horizontal signs are intentionally not asserted here.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

theorem logDeriv_riemannZeta_re_eq_archimedean_on_criticalLine
    {s : ℂ} (hsRe : s.re = 1 / 2) (hzeta : riemannZeta s ≠ 0) :
    (logDeriv riemannZeta s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s := by
  have hsPos : 0 < s.re := by rw [hsRe]; norm_num
  have hsOne : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [hsRe] at hre
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hsPos
  have hfactor : s * (s - 1) / 2 ≠ 0 := by
    have hsZero : s ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [hsRe] at hre
    exact div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne)) (by norm_num)
  have hxi : riemannXi s ≠ 0 := by
    rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos hsPos hsOne]
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) hzeta
  have hformula :=
    logDeriv_riemannZeta_eq_logDeriv_riemannXi_add_archimedean
      hsPos hsOne hzeta
  have hxiRe :=
    levinsonMontgomery_logDeriv_riemannXi_re_eq_zero_on_criticalLine hsRe hxi
  rw [hformula, Complex.add_re,
    levinsonMontgomeryLogDerivArchimedeanComplex_re, hxiRe, zero_add]

theorem levinsonMontgomery_equation_two_one_of_im_pos
    {s : ℂ} (hsIm : 0 < s.im) (hzeta : riemannZeta s ≠ 0) :
    (logDeriv riemannZeta s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryRealPairedZeroSum s := by
  have hsZero : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [zero_im] at him
    linarith
  have hsOne : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [one_im] at him
    linarith
  have hnotpole : ∀ m : ℕ, s ≠ -(2 * m) := by
    intro m h
    have him : s.im = 0 := by simpa using congrArg Complex.im h
    linarith
  have hgamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_neg_even hnotpole
  have hxiValue :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
      hsZero hsOne hgamma
  have hfactor : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne)) (by norm_num)
  have hxi : riemannXi s ≠ 0 := by
    rw [hxiValue]
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) hzeta
  have hxiLog :=
    logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta_of_nonpole
      hsZero hsOne hnotpole hzeta
  have hgammaLog :=
    logDeriv_GammaR_eq_digamma_of_not_neg_even hnotpole
  have hnotpoleHalf : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    apply hnotpole m
    calc
      s = (s / 2) * 2 := by ring
      _ = (-m : ℂ) * 2 := by rw [hm]
      _ = -(2 * (m : ℂ)) := by ring
  have hpsi := Complex.digamma_apply_add_one (s / 2) hnotpoleHalf
  have hhalfInv : (s / 2)⁻¹ = 2 / s := by
    field_simp [hsZero]
  have hsourceComplex :
      logDeriv riemannZeta s =
        logDeriv riemannXi s - 1 / (s - 1) +
          (Real.log Real.pi : ℂ) / 2 -
          Complex.digamma (s / 2 + 1) / 2 := by
    rw [hgammaLog] at hxiLog
    rw [hpsi, hhalfInv]
    rw [hxiLog]
    simp only [div_eq_mul_inv]
    ring
  have hsourceReal := congrArg Complex.re hsourceComplex
  rw [levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re hxi]
  calc
    (logDeriv riemannZeta s).re =
        (logDeriv riemannXi s - 1 / (s - 1) +
          (Real.log Real.pi : ℂ) / 2 -
          Complex.digamma (s / 2 + 1) / 2).re := hsourceReal
    _ = levinsonMontgomeryLogDerivArchimedeanTerm s +
        (logDeriv riemannXi s).re := by
      rw [levinsonMontgomeryLogDerivArchimedeanTerm]
      norm_num
      ring

theorem logDeriv_riemannZeta_re_le_archimedean_on_imaginaryAxis
    {y : ℝ} (hy : 0 < y) (hzeta : riemannZeta ((y : ℂ) * I) ≠ 0) :
    (logDeriv riemannZeta ((y : ℂ) * I)).re ≤
      levinsonMontgomeryLogDerivArchimedeanTerm ((y : ℂ) * I) := by
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
  have hfactor : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne)) (by norm_num)
  have hxi : riemannXi s ≠ 0 := by
    rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
      hsZero hsOne hgamma]
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) (by simpa [s] using hzeta)
  have hpair :=
    levinsonMontgomeryRealPairedZeroSum_nonpos_of_re_eq_zero hsRe hxi
  have heq := levinsonMontgomery_equation_two_one_of_im_pos
    hsIm (by simpa [s] using hzeta)
  simpa only [s] using (show
    (logDeriv riemannZeta s).re ≤
      levinsonMontgomeryLogDerivArchimedeanTerm s by linarith)

theorem log_seventyNine_div_twenty_gt_oneThousandThreeHundredSeventyThree_div_oneThousand :
    (1373 / 1000 : ℝ) < Real.log (79 / 20) := by
  have hlog := abs_log_sub_binaryLogCenter_le
    (u := (79 / 20 : ℝ)) (by norm_num) 2 10
  have hlower := (abs_le.mp hlog).1
  have hcenter :
      (1373 / 1000 : ℝ) <
        binaryLogCenter 2 10 (79 / 20) - binaryLogError 2 10 (79 / 20) := by
    norm_num [binaryLogCenter, binaryLogError, logAtanhPartial,
      Finset.sum_range_succ]
  linarith

theorem levinsonMontgomeryArchimedean_criticalLine_neg_of_thirteenHalves_le
    {y : ℝ} (hy : 13 / 2 ≤ y) :
    levinsonMontgomeryLogDerivArchimedeanTerm
        ((1 / 2 : ℂ) + (y : ℂ) * I) < 0 := by
  let s : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  let w : ℂ := s / 2 + 1
  let W : ℂ := w + 1
  have hyPos : 0 < y := by linarith
  have hwRe : w.re = 5 / 4 := by
    norm_num [w, s, div_re]
  have hWRe : W.re = 9 / 4 := by
    norm_num [W, w, s, div_re]
  have hwRePos : 0 < w.re := by rw [hwRe]; norm_num
  have hWRePos : 0 < W.re := by rw [hWRe]; norm_num
  have hwNormSqComplex : 97 / 8 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]
    norm_num [w, s, div_re, div_im]
    nlinarith [sq_nonneg y]
  have hWNormSqComplex : 125 / 8 ≤ Complex.normSq W := by
    rw [Complex.normSq_apply]
    norm_num [W, w, s, div_re, div_im]
    nlinarith [sq_nonneg y]
  have hWNormSq : 125 / 8 ≤ ‖W‖ ^ 2 := by
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
  have hPoleDen : 85 / 2 ≤ Complex.normSq (s - 1) := by
    rw [Complex.normSq_apply]
    norm_num [s]
    nlinarith [sq_nonneg y]
  have hPoleDenPos : 0 < Complex.normSq (s - 1) :=
    lt_of_lt_of_le (by norm_num) hPoleDen
  have hPole : -(1 / (s - 1)).re ≤ 1 / 85 := by
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
  have hInvCorrection : (1 / (2 * W)).re / 2 ≤ 9 / 250 := by
    have hEq :
        (1 / (2 * W)).re / 2 = W.re / (4 * Complex.normSq W) := by
      rw [one_div, Complex.inv_re]
      norm_num [Complex.normSq_mul]
      ring
    rw [hEq, hWRe, div_le_iff₀ (mul_pos (by norm_num) hWNormSqPos)]
    nlinarith
  have hwNormSqPos : 0 < Complex.normSq w :=
    lt_of_lt_of_le (by norm_num) hwNormSqComplex
  have hwInv : (1 / w).re / 2 ≤ 5 / 97 := by
    have hEq : (1 / w).re / 2 = w.re / (2 * Complex.normSq w) := by
      rw [one_div, Complex.inv_re]
      ring
    rw [hEq, hwRe, div_le_iff₀ (mul_pos (by norm_num) hwNormSqPos)]
    nlinarith
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder W
  have hRnorm : ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) :=
    levinsonMontgomery_digamma_stirling_remainder_norm_le hWRePos
  have hRsmall : ‖R‖ ≤ 27 / 1000 := by
    calc
      ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) := hRnorm
      _ ≤ 27 / 1000 := by
        have hden : 0 < 64 * ‖W‖ ^ 2 := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
  have hRreal : -R.re / 2 ≤ 27 / 2000 := by
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

theorem speiserZetaDerivRatio_rightVertical_re_neg_of_thirteenHalves_le
    {y : ℝ} (hy : 13 / 2 ≤ y)
    (hzeta : riemannZeta ((1 / 2 : ℂ) + (y : ℂ) * I) ≠ 0) :
    (speiserZetaDerivRatio ((1 / 2 : ℂ) + (y : ℂ) * I)).re < 0 := by
  let s : ℂ := (1 / 2 : ℂ) + (y : ℂ) * I
  have hsRe : s.re = 1 / 2 := by norm_num [s]
  have heq :=
    logDeriv_riemannZeta_re_eq_archimedean_on_criticalLine
      hsRe (by simpa [s] using hzeta)
  have hneg :=
    levinsonMontgomeryArchimedean_criticalLine_neg_of_thirteenHalves_le hy
  simpa only [speiserZetaDerivRatio, logDeriv_apply, s] using
    (show (logDeriv riemannZeta s).re < 0 by linarith)

end

end LeanLab.Riemann
