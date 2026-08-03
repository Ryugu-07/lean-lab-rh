import LeanLab.Riemann.LevinsonMontgomeryHeightTenLeftLowZeroMass

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Phase-preserving evaluator for the low and middle left boundary

The previous reflected evaluator retained only a real upper bound. This module keeps the full
complex logarithmic-derivative reflection and turns value and derivative error balls at the
reflected right-half point into a complex ball for the actual quotient on the imaginary axis.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- Full complex logarithmic-derivative reflection on the positive imaginary axis. -/
theorem logDeriv_riemannZeta_reflection_on_imaginaryAxis
    {y : ℝ} (hy : 0 < y)
    (hzeta : riemannZeta ((y : ℂ) * I) ≠ 0)
    (hreflected : riemannZeta (1 - (y : ℂ) * I) ≠ 0) :
    logDeriv riemannZeta ((y : ℂ) * I) =
      -logDeriv riemannZeta (1 - (y : ℂ) * I) +
        levinsonMontgomeryLogDerivArchimedeanComplex ((y : ℂ) * I) +
        levinsonMontgomeryLogDerivArchimedeanComplex (1 - (y : ℂ) * I) := by
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
  have hxiLog :=
    logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta_of_nonpole
      hsZero hsOne hnotpole (by simpa [s] using hzeta)
  have hgammaLog := logDeriv_GammaR_eq_digamma_of_not_neg_even hnotpole
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
  have hsFormula :
      logDeriv riemannZeta s = logDeriv riemannXi s +
        levinsonMontgomeryLogDerivArchimedeanComplex s := by
    rw [hgammaLog] at hxiLog
    unfold levinsonMontgomeryLogDerivArchimedeanComplex
    rw [hpsi, hhalfInv]
    rw [hxiLog]
    simp only [div_eq_mul_inv]
    ring
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
  change logDeriv riemannZeta s =
    -logDeriv riemannZeta w +
      levinsonMontgomeryLogDerivArchimedeanComplex s +
      levinsonMontgomeryLogDerivArchimedeanComplex w
  rw [hsFormula, hwFormula, hxiReflection]
  ring

/-- A value ball separated from zero gives a lower norm bound for its exact value. -/
theorem approx_norm_sub_error_le_norm
    {z Z : ℂ} {e : ℝ} (hz : ‖z - Z‖ ≤ e) :
    ‖Z‖ - e ≤ ‖z‖ := by
  have htriangle : ‖Z‖ ≤ ‖Z - z‖ + ‖z‖ := by
    calc
      ‖Z‖ = ‖(Z - z) + z‖ := by ring_nf
      _ ≤ ‖Z - z‖ + ‖z‖ := norm_add_le _ _
  have hsymm : ‖Z - z‖ = ‖z - Z‖ := by
    rw [← norm_neg (Z - z)]
    congr 1
    ring
  rw [hsymm] at htriangle
  linarith

/-- Value and derivative balls give a complex-norm ball for their quotient. -/
theorem norm_ratio_sub_approx_ratio_le
    {z d Z D : ℂ} {ez ed : ℝ}
    (hz : ‖z - Z‖ ≤ ez) (hd : ‖d - D‖ ≤ ed)
    (hzMargin : ez < ‖Z‖) :
    ‖d / z - D / Z‖ ≤
      ed / (‖Z‖ - ez) +
        ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) := by
  have hez : 0 ≤ ez := (norm_nonneg (z - Z)).trans hz
  have hed : 0 ≤ ed := (norm_nonneg (d - D)).trans hd
  have hgap : 0 < ‖Z‖ - ez := sub_pos.mpr hzMargin
  have hZpos : 0 < ‖Z‖ := lt_of_le_of_lt hez hzMargin
  have hzLower : ‖Z‖ - ez ≤ ‖z‖ := approx_norm_sub_error_le_norm hz
  have hzPos : 0 < ‖z‖ := hgap.trans_le hzLower
  have hzNe : z ≠ 0 := norm_pos_iff.mp hzPos
  have hZNe : Z ≠ 0 := norm_pos_iff.mp hZpos
  have hidentity :
      d / z - D / Z = (d - D) / z + D * (Z - z) / (z * Z) := by
    field_simp [hzNe, hZNe]
    ring
  rw [hidentity]
  calc
    ‖(d - D) / z + D * (Z - z) / (z * Z)‖ ≤
        ‖(d - D) / z‖ + ‖D * (Z - z) / (z * Z)‖ := norm_add_le _ _
    _ = ‖d - D‖ / ‖z‖ +
        (‖D‖ * ‖Z - z‖) / (‖z‖ * ‖Z‖) := by
      simp only [norm_div, norm_mul]
    _ ≤ ed / (‖Z‖ - ez) +
        ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) := by
      have hsymm : ‖Z - z‖ = ‖z - Z‖ := by
        rw [← norm_neg (Z - z)]
        congr 1
        ring
      rw [hsymm]
      exact add_le_add
        (div_le_div₀ hed hd hgap hzLower)
        (div_le_div₀ (mul_nonneg (norm_nonneg D) hez)
          (mul_le_mul_of_nonneg_left hz (norm_nonneg D))
          (mul_pos hgap hZpos)
          (mul_le_mul_of_nonneg_right hzLower hZpos.le))

/-- Complex center for the twice-shifted pole/Gamma correction. -/
def levinsonMontgomeryArchimedeanComplexShiftTwoApprox (s : ℂ) : ℂ :=
  -1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 -
    (Complex.log ((s / 2 + 1) + 2) - 1 / (2 * ((s / 2 + 1) + 2)) -
      1 / (s / 2 + 1) - 1 / ((s / 2 + 1) + 1)) / 2

/-- The complex twice-shifted center encloses the actual pole/Gamma correction. -/
theorem norm_levinsonMontgomeryLogDerivArchimedeanComplex_sub_shiftTwoApprox_le
    {s : ℂ} (hs : -2 < s.re) :
    ‖levinsonMontgomeryLogDerivArchimedeanComplex s -
        levinsonMontgomeryArchimedeanComplexShiftTwoApprox s‖ ≤
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
      levinsonMontgomeryLogDerivArchimedeanComplex s -
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox s = -R / 2 := by
    unfold levinsonMontgomeryLogDerivArchimedeanComplex
      levinsonMontgomeryArchimedeanComplexShiftTwoApprox
    change
      (-1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 - Complex.digamma w / 2) -
        (-1 / (s - 1) + (Real.log Real.pi : ℂ) / 2 -
          (Complex.log W - 1 / (2 * W) - 1 / w - 1 / (w + 1)) / 2) = _
    rw [hdigamma]
    ring
  have hR := levinsonMontgomery_digamma_stirling_remainder_norm_le hWRe
  rw [hdiff, norm_div, norm_neg]
  unfold levinsonMontgomeryArchimedeanShiftTwoError
  norm_num
  calc
    ‖R‖ / 2 ≤ (27 / (64 * ‖W‖ ^ 2)) / 2 := by gcongr
    _ = 27 / (128 * ‖W‖ ^ 2) := by ring

/-- Reflected finite center for the actual quotient on the imaginary axis. -/
def leftLowMiddlePhaseCenter (y : ℝ) (N : ℕ) : ℂ :=
  -(eulerMaclaurinTwoZetaDerivApprox (1 - (y : ℂ) * I) N /
      eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N) +
    levinsonMontgomeryArchimedeanComplexShiftTwoApprox ((y : ℂ) * I) +
    levinsonMontgomeryArchimedeanComplexShiftTwoApprox (1 - (y : ℂ) * I)

/-- Total complex radius of the reflected finite quotient center. -/
def leftLowMiddlePhaseError (y : ℝ) (N : ℕ) : ℝ :=
  eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) N /
      (‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖ -
        eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N) +
    ‖eulerMaclaurinTwoZetaDerivApprox (1 - (y : ℂ) * I) N‖ *
        eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N /
      ((‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖ -
          eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N) *
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖) +
    levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) +
    levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I)

/-- The actual imaginary-axis quotient lies in the phase-preserving reflected finite ball. -/
theorem norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_le
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖) :
    ‖speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter y N‖ ≤
      leftLowMiddlePhaseError y N := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := 1 - s
  let Z : ℂ := eulerMaclaurinTwoZetaApprox w N
  let D : ℂ := eulerMaclaurinTwoZetaDerivApprox w N
  let ez : ℝ := eulerMaclaurinTwoZetaError w N
  let ed : ℝ := eulerMaclaurinTwoZetaDerivError w N
  have hwRe : 0 < w.re := by norm_num [w, s]
  have hwOne : w ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [w, s] at him
    linarith
  have hzBound : ‖riemannZeta w - Z‖ ≤ ez := by
    simpa only [Z, ez] using
      norm_riemannZeta_sub_eulerMaclaurinTwoZetaApprox_le_of_re_pos
        hwOne hwRe hN
  have hdBound : ‖deriv riemannZeta w - D‖ ≤ ed := by
    simpa only [D, ed] using
      norm_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_le_of_re_pos
        hwOne hwRe hN
  have hzMargin' : ez < ‖Z‖ := by simpa only [w, s, Z, ez] using hzMargin
  have hratio := norm_ratio_sub_approx_ratio_le hzBound hdBound hzMargin'
  have hreflected : riemannZeta w ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, norm_neg] at hzBound
    linarith
  have hzeta : riemannZeta s ≠ 0 := by
    simpa [s] using riemannZeta_ne_zero_on_positive_imaginaryAxis hy
  have hreflection := logDeriv_riemannZeta_reflection_on_imaginaryAxis hy
    (by simpa [s] using hzeta) (by simpa [w, s] using hreflected)
  have harchS :=
    norm_levinsonMontgomeryLogDerivArchimedeanComplex_sub_shiftTwoApprox_le
      (s := s) (by norm_num [s])
  have harchW :=
    norm_levinsonMontgomeryLogDerivArchimedeanComplex_sub_shiftTwoApprox_le
      (s := w) (by norm_num [w, s])
  have hdecomp :
      (-deriv riemannZeta w / riemannZeta w +
          levinsonMontgomeryLogDerivArchimedeanComplex s +
          levinsonMontgomeryLogDerivArchimedeanComplex w) -
        (-D / Z + levinsonMontgomeryArchimedeanComplexShiftTwoApprox s +
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox w) =
      -(deriv riemannZeta w / riemannZeta w - D / Z) +
        (levinsonMontgomeryLogDerivArchimedeanComplex s -
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox s) +
        (levinsonMontgomeryLogDerivArchimedeanComplex w -
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox w) := by ring
  have hphase :
      ‖(-deriv riemannZeta w / riemannZeta w +
          levinsonMontgomeryLogDerivArchimedeanComplex s +
          levinsonMontgomeryLogDerivArchimedeanComplex w) -
        (-D / Z + levinsonMontgomeryArchimedeanComplexShiftTwoApprox s +
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox w)‖ ≤
        ed / (‖Z‖ - ez) + ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) +
          levinsonMontgomeryArchimedeanShiftTwoError s +
          levinsonMontgomeryArchimedeanShiftTwoError w := by
    rw [hdecomp]
    calc
      ‖-(deriv riemannZeta w / riemannZeta w - D / Z) +
            (levinsonMontgomeryLogDerivArchimedeanComplex s -
              levinsonMontgomeryArchimedeanComplexShiftTwoApprox s) +
            (levinsonMontgomeryLogDerivArchimedeanComplex w -
              levinsonMontgomeryArchimedeanComplexShiftTwoApprox w)‖ ≤
          ‖deriv riemannZeta w / riemannZeta w - D / Z‖ +
            ‖levinsonMontgomeryLogDerivArchimedeanComplex s -
              levinsonMontgomeryArchimedeanComplexShiftTwoApprox s‖ +
            ‖levinsonMontgomeryLogDerivArchimedeanComplex w -
              levinsonMontgomeryArchimedeanComplexShiftTwoApprox w‖ := by
        calc
          _ ≤ ‖-(deriv riemannZeta w / riemannZeta w - D / Z) +
              (levinsonMontgomeryLogDerivArchimedeanComplex s -
                levinsonMontgomeryArchimedeanComplexShiftTwoApprox s)‖ +
              ‖levinsonMontgomeryLogDerivArchimedeanComplex w -
                levinsonMontgomeryArchimedeanComplexShiftTwoApprox w‖ := norm_add_le _ _
          _ ≤ (‖-(deriv riemannZeta w / riemannZeta w - D / Z)‖ +
              ‖levinsonMontgomeryLogDerivArchimedeanComplex s -
                levinsonMontgomeryArchimedeanComplexShiftTwoApprox s‖) +
              ‖levinsonMontgomeryLogDerivArchimedeanComplex w -
                levinsonMontgomeryArchimedeanComplexShiftTwoApprox w‖ :=
            by
              have h := norm_add_le
                (-(deriv riemannZeta w / riemannZeta w - D / Z))
                (levinsonMontgomeryLogDerivArchimedeanComplex s -
                  levinsonMontgomeryArchimedeanComplexShiftTwoApprox s)
              linarith
          _ = ‖deriv riemannZeta w / riemannZeta w - D / Z‖ +
              ‖levinsonMontgomeryLogDerivArchimedeanComplex s -
                levinsonMontgomeryArchimedeanComplexShiftTwoApprox s‖ +
              ‖levinsonMontgomeryLogDerivArchimedeanComplex w -
                levinsonMontgomeryArchimedeanComplexShiftTwoApprox w‖ := by
            rw [norm_neg]
      _ ≤ ed / (‖Z‖ - ez) + ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) +
          levinsonMontgomeryArchimedeanShiftTwoError s +
          levinsonMontgomeryArchimedeanShiftTwoError w := by linarith
  have hspeiser :
      speiserZetaDerivRatio ((y : ℂ) * I) =
        -deriv riemannZeta w / riemannZeta w +
          levinsonMontgomeryLogDerivArchimedeanComplex s +
          levinsonMontgomeryLogDerivArchimedeanComplex w := by
    rw [show speiserZetaDerivRatio ((y : ℂ) * I) =
        logDeriv riemannZeta ((y : ℂ) * I) by rfl, hreflection,
      logDeriv_apply]
    dsimp only [s, w]
    ring
  rw [hspeiser]
  unfold leftLowMiddlePhaseCenter leftLowMiddlePhaseError
  dsimp only [s, w, Z, D, ez, ed] at hphase ⊢
  (convert hphase using 1; ring_nf)

/-- A positive real center margin certifies a positive actual quotient real part. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_of_phaseMargin
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    (hphase : leftLowMiddlePhaseError y N < (leftLowMiddlePhaseCenter y N).re) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re := by
  have hball := norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_le
    y hy hN hzMargin
  have hre := Complex.abs_re_le_norm
    (speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter y N)
  rw [Complex.sub_re] at hre
  have habs := hre.trans hball
  linarith [neg_abs_le
    ((speiserZetaDerivRatio ((y : ℂ) * I)).re -
      (leftLowMiddlePhaseCenter y N).re)]

/-- The singular reflected endpoint is discharged directly on the real bottom edge. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_at_zero :
    0 < (speiserZetaDerivRatio ((0 : ℂ) * I)).re := by
  simpa using speiserZetaDerivRatio_realSegment_re_pos 0 (by constructor <;> norm_num)

/-- Once the positive-height finite cover is supplied, the exact endpoint closes `[0,6]`. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_six_of_pos
    (hpos : ∀ y : ℝ, 0 < y → y ≤ 6 →
      0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re)
    {y : ℝ} (hy0 : 0 ≤ y) (hy6 : y ≤ 6) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re := by
  rcases eq_or_lt_of_le hy0 with rfl | hy
  · exact speiserZetaDerivRatio_leftVertical_re_pos_at_zero
  · exact hpos y hy hy6

/-- A negative imaginary center margin certifies a negative actual quotient imaginary part. -/
theorem speiserZetaDerivRatio_leftVertical_im_neg_of_phaseMargin
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    (hphase : (leftLowMiddlePhaseCenter y N).im < -leftLowMiddlePhaseError y N) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).im < 0 := by
  have hball := norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_le
    y hy hN hzMargin
  have him := Complex.abs_im_le_norm
    (speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter y N)
  rw [Complex.sub_im] at him
  have habs := him.trans hball
  linarith [le_abs_self
    ((speiserZetaDerivRatio ((y : ℂ) * I)).im -
      (leftLowMiddlePhaseCenter y N).im)]

/-- Either phase component places the rotated quotient in the principal slit plane. -/
theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_phase
    {y : ℝ}
    (hphase : (speiserZetaDerivRatio ((y : ℂ) * I)).re ≠ 0 ∨
      (speiserZetaDerivRatio ((y : ℂ) * I)).im < 0) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hphase with hre | him
  · right
    norm_num
    exact hre
  · left
    norm_num
    linarith

/-- The two frozen low/middle phase signs, together with the compiled high route, close the
complete left vertical edge. -/
theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_zero_ten_of_phaseSigns
    (hre : ∀ y : ℝ, 0 ≤ y → y ≤ 6 →
      0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re)
    (him : ∀ y : ℝ, 6 ≤ y → y ≤ 13 / 2 →
      (speiserZetaDerivRatio ((y : ℂ) * I)).im < 0)
    {y : ℝ} (hy0 : 0 ≤ y) (_hy10 : y ≤ 10) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane := by
  by_cases hy6 : y ≤ 6
  · exact speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_phase
      (Or.inl (ne_of_gt (hre y hy0 hy6)))
  have h6y : 6 ≤ y := (lt_of_not_ge hy6).le
  by_cases hyHalf : y ≤ 13 / 2
  · exact speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_phase
      (Or.inr (him y h6y hyHalf))
  have hHalfY : 13 / 2 ≤ y := (lt_of_not_ge hyHalf).le
  by_cases hy7 : y ≤ 7
  · exact
      speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_thirteenHalves_seven_lowZeroMass
        hHalfY hy7
  exact speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_of_seven_le
    (lt_of_not_ge hy7).le

end

end LeanLab.Riemann
