import LeanLab.Riemann.LevinsonMontgomeryEulerMaclaurinSecond
import LeanLab.Riemann.LevinsonMontgomeryHeightTenLeftHigh

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Height-ten residual left boundary

This module combines a twice-shifted digamma enclosure with the second Euler--Maclaurin
value/derivative balls at the reflected point.  It targets the residual imaginary-axis interval
`13/2 <= y <= 7` left open by the structural `y >= 7` argument.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- Center for the pole/Gamma correction after shifting the digamma argument twice. -/
def levinsonMontgomeryArchimedeanShiftTwoApprox (s : ℂ) : ℝ :=
  -(1 / (s - 1)).re + Real.log Real.pi / 2 -
    (Complex.log ((s / 2 + 1) + 2) - 1 / (2 * ((s / 2 + 1) + 2)) -
      1 / (s / 2 + 1) - 1 / ((s / 2 + 1) + 1)).re / 2

/-- Error radius for the twice-shifted pole/Gamma center. -/
def levinsonMontgomeryArchimedeanShiftTwoError (s : ℂ) : ℝ :=
  27 / (128 * ‖(s / 2 + 1) + 2‖ ^ 2)

/-- The twice-shifted digamma center encloses the actual pole/Gamma correction. -/
theorem abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_shiftTwoApprox_le
    {s : ℂ} (hs : -2 < s.re) :
    |levinsonMontgomeryLogDerivArchimedeanTerm s -
        levinsonMontgomeryArchimedeanShiftTwoApprox s| ≤
      levinsonMontgomeryArchimedeanShiftTwoError s := by
  let w : ℂ := s / 2 + 1
  let W : ℂ := w + 2
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder W
  have hwRe : 0 < w.re := by
    dsimp only [w]
    norm_num [div_re]
    linarith
  have hwOneRe : 0 < (w + 1).re := by
    norm_num
    linarith
  have hWRe : 0 < W.re := by
    dsimp only [W]
    norm_num
    linarith
  have hnotpoleW : ∀ m : ℕ, w ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hnotpoleWOne : ∀ m : ℕ, w + 1 ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, one_re, Complex.natCast_re, Complex.neg_re] at hre
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hshift0 := Complex.digamma_apply_add_one w hnotpoleW
  have hshift1 := Complex.digamma_apply_add_one (w + 1) hnotpoleWOne
  have hstirling := levinsonMontgomery_digamma_stirling hWRe
  change Complex.digamma W = Complex.log W - 1 / (2 * W) + R at hstirling
  have hdigamma : Complex.digamma w =
      Complex.log W - 1 / (2 * W) + R - 1 / w - 1 / (w + 1) := by
    calc
      Complex.digamma w = Complex.digamma (w + 1) - 1 / w := by
        rw [hshift0]
        ring
      _ = Complex.digamma ((w + 1) + 1) - 1 / (w + 1) - 1 / w := by
        rw [hshift1]
        ring
      _ = Complex.log W - 1 / (2 * W) + R - 1 / w - 1 / (w + 1) := by
        rw [show (w + 1) + 1 = W by dsimp only [W]; ring, hstirling]
        ring
  have hdiff :
      levinsonMontgomeryLogDerivArchimedeanTerm s -
          levinsonMontgomeryArchimedeanShiftTwoApprox s = -R.re / 2 := by
    unfold levinsonMontgomeryLogDerivArchimedeanTerm
      levinsonMontgomeryArchimedeanShiftTwoApprox
    change
      (-(1 / (s - 1)).re + Real.log Real.pi / 2 -
          (Complex.digamma w).re / 2) -
        (-(1 / (s - 1)).re + Real.log Real.pi / 2 -
          (Complex.log W - 1 / (2 * W) - 1 / w - 1 / (w + 1)).re / 2) = _
    rw [hdigamma]
    norm_num
    ring
  have hR := levinsonMontgomery_digamma_stirling_remainder_norm_le hWRe
  rw [hdiff, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold levinsonMontgomeryArchimedeanShiftTwoError
  change |R.re| / 2 ≤ 27 / (128 * ‖W‖ ^ 2)
  calc
    |R.re| / 2 ≤ ‖R‖ / 2 := by
      gcongr
      exact Complex.abs_re_le_norm R
    _ ≤ (27 / (64 * ‖W‖ ^ 2)) / 2 := by gcongr
    _ = 27 / (128 * ‖W‖ ^ 2) := by ring

/-- Upper center for the sum of the twice-shifted reflected pole/Gamma corrections. -/
def levinsonMontgomeryReflectedArchimedeanShiftTwoUpper (s : ℂ) : ℝ :=
  levinsonMontgomeryArchimedeanShiftTwoApprox s +
    levinsonMontgomeryArchimedeanShiftTwoError s +
    levinsonMontgomeryArchimedeanShiftTwoApprox (1 - s) +
    levinsonMontgomeryArchimedeanShiftTwoError (1 - s)

/-- The actual reflected pole/Gamma sum is bounded by the twice-shifted upper center. -/
theorem levinsonMontgomery_reflectedArchimedean_le_shiftTwoUpper
    {s : ℂ} (hs : -2 < s.re) (hw : -2 < (1 - s).re) :
    levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryLogDerivArchimedeanTerm (1 - s) ≤
      levinsonMontgomeryReflectedArchimedeanShiftTwoUpper s := by
  have hsAbs :=
    abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_shiftTwoApprox_le hs
  have hwAbs :=
    abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_shiftTwoApprox_le hw
  have hsUpper := (abs_le.mp hsAbs).2
  have hwUpper := (abs_le.mp hwAbs).2
  unfold levinsonMontgomeryReflectedArchimedeanShiftTwoUpper
  linarith

/-- Exact reflected logarithmic-derivative identity on the positive imaginary axis. -/
theorem logDeriv_riemannZeta_re_reflection_on_imaginaryAxis
    {y : ℝ} (hy : 0 < y)
    (hzeta : riemannZeta ((y : ℂ) * I) ≠ 0)
    (hreflected : riemannZeta (1 - (y : ℂ) * I) ≠ 0) :
    (logDeriv riemannZeta ((y : ℂ) * I)).re =
      -(logDeriv riemannZeta (1 - (y : ℂ) * I)).re +
        levinsonMontgomeryLogDerivArchimedeanTerm ((y : ℂ) * I) +
        levinsonMontgomeryLogDerivArchimedeanTerm (1 - (y : ℂ) * I) := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := 1 - s
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
  have hgamma : Gammaℝ s ≠ 0 := GammaR_ne_zero_of_not_neg_even hnotpole
  have hfactor : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne)) (by norm_num)
  have hxi : riemannXi s ≠ 0 := by
    rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
      hsZero hsOne hgamma]
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) (by simpa [s] using hzeta)
  have hpair := levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re hxi
  have hsFormula := levinsonMontgomery_equation_two_one_of_im_pos
    hsIm (by simpa [s] using hzeta)
  have hwRe : 0 < w.re := by simp [w, hsRe]
  have hwOne : w ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [w, s] at him
    linarith
  have hwFormula :=
    logDeriv_riemannZeta_eq_logDeriv_riemannXi_add_archimedean
      hwRe hwOne (by simpa [w, s] using hreflected)
  have hxiReflection : logDeriv riemannXi w = -logDeriv riemannXi s := by
    simpa [w] using logDeriv_riemannXi_one_sub s
  have hwReal := congrArg Complex.re hwFormula
  simp only [Complex.add_re] at hwReal
  rw [levinsonMontgomeryLogDerivArchimedeanComplex_re, hxiReflection,
    Complex.neg_re] at hwReal
  rw [hpair] at hsFormula
  change (logDeriv riemannZeta s).re =
    -(logDeriv riemannZeta w).re +
      levinsonMontgomeryLogDerivArchimedeanTerm s +
      levinsonMontgomeryLogDerivArchimedeanTerm w
  linarith

/-- Second-corrected reflected finite centers certify strict negativity on the imaginary axis. -/
theorem speiserStrictNegativePoint_on_imaginaryAxis_of_reflected_eulerMaclaurinTwo_margins
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    (hupper :
      levinsonMontgomeryReflectedArchimedeanShiftTwoUpper ((y : ℂ) * I) < 0)
    (hcross :
      levinsonMontgomeryReflectedArchimedeanShiftTwoUpper ((y : ℂ) * I) *
          (‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖ -
            eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N) ^ 2 <
        (eulerMaclaurinTwoZetaDerivApprox (1 - (y : ℂ) * I) N *
            conj (eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N)).re -
          (eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) N *
              (‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖ +
                eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N) +
            ‖eulerMaclaurinTwoZetaDerivApprox (1 - (y : ℂ) * I) N‖ *
              eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N)) :
    riemannZeta ((y : ℂ) * I) ≠ 0 ∧
      deriv riemannZeta ((y : ℂ) * I) ≠ 0 ∧
      (speiserZetaDerivRatio ((y : ℂ) * I)).re < 0 := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := 1 - s
  have hwRe : 0 < w.re := by simp [w, s]
  have hwOne : w ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [w, s] at him
    linarith
  have hzBound :=
    norm_riemannZeta_sub_eulerMaclaurinTwoZetaApprox_le_of_re_pos
      hwOne hwRe hN
  have hdBound :=
    norm_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_le_of_re_pos
      hwOne hwRe hN
  have hratio := ratio_re_gt_of_approx hzBound hdBound
    (by simpa [w, s] using hzMargin) (by simpa [s] using hupper)
    (by simpa [w, s] using hcross)
  have hreflected : riemannZeta w ≠ 0 := hratio.1
  have hzeta : riemannZeta s ≠ 0 := by
    simpa [s] using riemannZeta_ne_zero_on_positive_imaginaryAxis hy
  have hreflection := logDeriv_riemannZeta_re_reflection_on_imaginaryAxis
    hy (by simpa [s] using hzeta) (by simpa [w, s] using hreflected)
  have harch := levinsonMontgomery_reflectedArchimedean_le_shiftTwoUpper
    (s := s) (by norm_num [s]) (by norm_num [s])
  have hratioLog :
      levinsonMontgomeryReflectedArchimedeanShiftTwoUpper s <
        (logDeriv riemannZeta w).re := by
    simpa only [logDeriv_apply] using hratio.2
  have hlogNegative : (logDeriv riemannZeta s).re < 0 := by
    change (logDeriv riemannZeta ((y : ℂ) * I)).re < 0
    rw [hreflection]
    simpa only [w] using (show
      -(logDeriv riemannZeta w).re +
          levinsonMontgomeryLogDerivArchimedeanTerm s +
          levinsonMontgomeryLogDerivArchimedeanTerm (1 - s) < 0 by
        linarith)
  have hderiv : deriv riemannZeta s ≠ 0 := by
    intro hzero
    rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hlogNegative
    exact (lt_irrefl 0) hlogNegative
  refine ⟨by simpa [s] using hzeta, by simpa [s] using hderiv, ?_⟩
  simpa only [speiserZetaDerivRatio, logDeriv_apply, s] using hlogNegative

/-- The reflected second-correction margins place the rotated quotient in the slit plane. -/
theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_reflected_eulerMaclaurinTwo
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    (hupper :
      levinsonMontgomeryReflectedArchimedeanShiftTwoUpper ((y : ℂ) * I) < 0)
    (hcross :
      levinsonMontgomeryReflectedArchimedeanShiftTwoUpper ((y : ℂ) * I) *
          (‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖ -
            eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N) ^ 2 <
        (eulerMaclaurinTwoZetaDerivApprox (1 - (y : ℂ) * I) N *
            conj (eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N)).re -
          (eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) N *
              (‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖ +
                eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N) +
            ‖eulerMaclaurinTwoZetaDerivApprox (1 - (y : ℂ) * I) N‖ *
              eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N)) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane := by
  have hneg :=
    speiserStrictNegativePoint_on_imaginaryAxis_of_reflected_eulerMaclaurinTwo_margins
      y hy hN hzMargin hupper hcross
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num
  exact ne_of_lt hneg.2.2

end

end LeanLab.Riemann
