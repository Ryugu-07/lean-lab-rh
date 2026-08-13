import LeanLab.Riemann.ChebyshevReverseZeroExclusion
import LeanLab.Riemann.LevinsonMontgomeryHeightTenLeftLowMiddlePhase

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Pole-cancelled evaluator on the low left boundary

The reflected zeta value approaches its pole as the imaginary height tends to zero.  Multiplying
by `w - 1` before forming the quotient exposes the exact cancellation and makes the numerical
error shrink with the height.
-/

open Complex Real

namespace LeanLab.Riemann

noncomputable section

/-- The second-corrected center for the entire pole-removed zeta function. -/
def poleRemovedEulerZetaApprox (w : ℂ) (N : ℕ) : ℂ :=
  (w - 1) * eulerMaclaurinTwoZetaApprox w N

/-- The derivative center obtained by differentiating the pole-removed product. -/
def poleRemovedEulerZetaDerivApprox (w : ℂ) (N : ℕ) : ℂ :=
  eulerMaclaurinTwoZetaApprox w N +
    (w - 1) * eulerMaclaurinTwoZetaDerivApprox w N

/-- Multiplication by the pole coordinate improves the value error near `w = 1`. -/
def poleRemovedEulerZetaError (w : ℂ) (N : ℕ) : ℝ :=
  ‖w - 1‖ * eulerMaclaurinTwoZetaError w N

/-- Product differentiation combines the value and derivative errors. -/
def poleRemovedEulerZetaDerivError (w : ℂ) (N : ℕ) : ℝ :=
  eulerMaclaurinTwoZetaError w N +
    ‖w - 1‖ * eulerMaclaurinTwoZetaDerivError w N

/-- The second-corrected value ball transfers to the entire pole removal. -/
theorem norm_zetaPoleRemoved_sub_poleRemovedEulerZetaApprox_le
    {w : ℂ} (hwOne : w ≠ 1) (hwRe : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖zetaPoleRemoved w - poleRemovedEulerZetaApprox w N‖ ≤
      poleRemovedEulerZetaError w N := by
  have hvalue :=
    norm_riemannZeta_sub_eulerMaclaurinTwoZetaApprox_le_of_re_pos
      hwOne hwRe hN
  rw [zetaPoleRemoved_eq hwOne]
  unfold poleRemovedEulerZetaApprox poleRemovedEulerZetaError
  have hid :
      (w - 1) * riemannZeta w -
          (w - 1) * eulerMaclaurinTwoZetaApprox w N =
        (w - 1) *
          (riemannZeta w - eulerMaclaurinTwoZetaApprox w N) := by ring
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_left hvalue (norm_nonneg _)

/-- The second-corrected value and derivative balls transfer to the derivative of the entire
pole removal. -/
theorem norm_deriv_zetaPoleRemoved_sub_poleRemovedEulerZetaDerivApprox_le
    {w : ℂ} (hwOne : w ≠ 1) (hwRe : 0 < w.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖deriv zetaPoleRemoved w - poleRemovedEulerZetaDerivApprox w N‖ ≤
      poleRemovedEulerZetaDerivError w N := by
  have hvalue :=
    norm_riemannZeta_sub_eulerMaclaurinTwoZetaApprox_le_of_re_pos
      hwOne hwRe hN
  have hderiv :=
    norm_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_le_of_re_pos
      hwOne hwRe hN
  rw [deriv_zetaPoleRemoved_eq hwOne]
  unfold poleRemovedEulerZetaDerivApprox poleRemovedEulerZetaDerivError
  have hid :
      riemannZeta w + (w - 1) * deriv riemannZeta w -
          (eulerMaclaurinTwoZetaApprox w N +
            (w - 1) * eulerMaclaurinTwoZetaDerivApprox w N) =
        (riemannZeta w - eulerMaclaurinTwoZetaApprox w N) +
          (w - 1) *
            (deriv riemannZeta w -
              eulerMaclaurinTwoZetaDerivApprox w N) := by ring
  rw [hid]
  calc
    ‖(riemannZeta w - eulerMaclaurinTwoZetaApprox w N) +
        (w - 1) *
          (deriv riemannZeta w -
            eulerMaclaurinTwoZetaDerivApprox w N)‖ ≤
        ‖riemannZeta w - eulerMaclaurinTwoZetaApprox w N‖ +
          ‖(w - 1) *
            (deriv riemannZeta w -
              eulerMaclaurinTwoZetaDerivApprox w N)‖ := norm_add_le _ _
    _ = ‖riemannZeta w - eulerMaclaurinTwoZetaApprox w N‖ +
          ‖w - 1‖ *
            ‖deriv riemannZeta w -
              eulerMaclaurinTwoZetaDerivApprox w N‖ := by rw [norm_mul]
    _ ≤ eulerMaclaurinTwoZetaError w N +
          ‖w - 1‖ * eulerMaclaurinTwoZetaDerivError w N := by
      exact add_le_add hvalue
        (mul_le_mul_of_nonneg_left hderiv (norm_nonneg _))

/-- Away from the patched point, the logarithmic derivative of the pole removal is the zeta
logarithmic derivative plus the explicit pole. -/
theorem logDeriv_zetaPoleRemoved_eq_add_inv
    {w : ℂ} (hwOne : w ≠ 1) (hzeta : riemannZeta w ≠ 0) :
    logDeriv zetaPoleRemoved w =
      1 / (w - 1) + logDeriv riemannZeta w := by
  have hwSub : w - 1 ≠ 0 := sub_ne_zero.mpr hwOne
  rw [logDeriv_apply, deriv_zetaPoleRemoved_eq hwOne,
    zetaPoleRemoved_eq hwOne, logDeriv_apply]
  field_simp [hwSub, hzeta]

/-- The regular pole-cancelled archimedean term in the imaginary-axis reflection formula. -/
def levinsonMontgomeryPoleCancelledArchimedeanComplex (s : ℂ) : ℂ :=
  -1 / (s - 1) + (Real.log Real.pi : ℂ) -
    (Complex.digamma (s / 2 + 1) +
      Complex.digamma ((1 - s) / 2 + 1)) / 2

/-- The explicit twice-shifted digamma center without the zeta pole term. -/
def levinsonMontgomeryDigammaComplexShiftTwoApprox (s : ℂ) : ℂ :=
  Complex.log ((s / 2 + 1) + 2) -
    1 / (2 * ((s / 2 + 1) + 2)) -
    1 / (s / 2 + 1) - 1 / ((s / 2 + 1) + 1)

/-- A continuous explicit center for the regular reflected archimedean term. -/
def levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox
    (s : ℂ) : ℂ :=
  -1 / (s - 1) + (Real.log Real.pi : ℂ) -
    (levinsonMontgomeryDigammaComplexShiftTwoApprox s +
      levinsonMontgomeryDigammaComplexShiftTwoApprox (1 - s)) / 2

/-- The regular archimedean center inherits exactly the two shifted digamma remainder radii. -/
theorem norm_levinsonMontgomeryPoleCancelledArchimedeanComplex_sub_shiftTwoApprox_le
    {s : ℂ} (hsLower : -2 < s.re) (hsUpper : s.re < 3) :
    ‖levinsonMontgomeryPoleCancelledArchimedeanComplex s -
        levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s‖ ≤
      levinsonMontgomeryArchimedeanShiftTwoError s +
        levinsonMontgomeryArchimedeanShiftTwoError (1 - s) := by
  have hs :=
    norm_levinsonMontgomeryLogDerivArchimedeanComplex_sub_shiftTwoApprox_le
      (s := s) hsLower
  have hw :=
    norm_levinsonMontgomeryLogDerivArchimedeanComplex_sub_shiftTwoApprox_le
      (s := 1 - s) (by norm_num; linarith)
  have hdiff :
      levinsonMontgomeryPoleCancelledArchimedeanComplex s -
          levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s =
        (levinsonMontgomeryLogDerivArchimedeanComplex s -
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox s) +
        (levinsonMontgomeryLogDerivArchimedeanComplex (1 - s) -
          levinsonMontgomeryArchimedeanComplexShiftTwoApprox (1 - s)) := by
    unfold levinsonMontgomeryPoleCancelledArchimedeanComplex
      levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox
      levinsonMontgomeryDigammaComplexShiftTwoApprox
      levinsonMontgomeryLogDerivArchimedeanComplex
      levinsonMontgomeryArchimedeanComplexShiftTwoApprox
    ring
  rw [hdiff]
  exact (norm_add_le _ _).trans (add_le_add hs hw)

/-- The imaginary-axis reflection formula after the zeta pole is cancelled inside the entire
function `zetaPoleRemoved`. -/
theorem logDeriv_riemannZeta_eq_neg_logDeriv_zetaPoleRemoved_add_regular
    (y : ℝ) (hy : 0 < y)
    (hzeta : riemannZeta ((y : ℂ) * I) ≠ 0)
    (hreflected : riemannZeta (1 - (y : ℂ) * I) ≠ 0) :
    logDeriv riemannZeta ((y : ℂ) * I) =
      -logDeriv zetaPoleRemoved (1 - (y : ℂ) * I) +
        levinsonMontgomeryPoleCancelledArchimedeanComplex ((y : ℂ) * I) := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := 1 - s
  have hsZero : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [s] at him
    linarith
  have hwOne : w ≠ 1 := by
    intro h
    apply hsZero
    dsimp only [w] at h
    linear_combination -h
  have hpole := logDeriv_zetaPoleRemoved_eq_add_inv hwOne
    (by simpa only [w, s] using hreflected)
  have hreflection := logDeriv_riemannZeta_reflection_on_imaginaryAxis hy
    hzeta hreflected
  have hregular :
      levinsonMontgomeryPoleCancelledArchimedeanComplex s =
        levinsonMontgomeryLogDerivArchimedeanComplex s +
          levinsonMontgomeryLogDerivArchimedeanComplex w + 1 / (w - 1) := by
    dsimp only [w]
    unfold levinsonMontgomeryPoleCancelledArchimedeanComplex
      levinsonMontgomeryLogDerivArchimedeanComplex
    field_simp [hsZero]
    ring
  simpa only [s, w] using (show
      logDeriv riemannZeta s =
        -logDeriv zetaPoleRemoved w +
          levinsonMontgomeryPoleCancelledArchimedeanComplex s by
    rw [hreflection, hpole, hregular]
    ring)

/-- Pole-cancelled finite center for the actual logarithmic derivative on the low imaginary
axis. -/
def leftLowPoleCancelledPhaseCenter (y : ℝ) (N : ℕ) : ℂ :=
  -(poleRemovedEulerZetaDerivApprox (1 - (y : ℂ) * I) N /
      poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) N) +
    levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox
      ((y : ℂ) * I)

/-- Total radius of the pole-cancelled finite phase center. -/
def leftLowPoleCancelledPhaseError (y : ℝ) (N : ℕ) : ℝ :=
  let w : ℂ := 1 - (y : ℂ) * I
  let Z : ℂ := poleRemovedEulerZetaApprox w N
  let D : ℂ := poleRemovedEulerZetaDerivApprox w N
  let ez : ℝ := poleRemovedEulerZetaError w N
  let ed : ℝ := poleRemovedEulerZetaDerivError w N
  ed / (‖Z‖ - ez) + ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) +
    levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) +
    levinsonMontgomeryArchimedeanShiftTwoError w

/-- The actual imaginary-axis quotient lies in the regular pole-cancelled finite phase ball. -/
theorem norm_speiserZetaDerivRatio_sub_leftLowPoleCancelledPhaseCenter_le
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      poleRemovedEulerZetaError (1 - (y : ℂ) * I) N <
        ‖poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) N‖) :
    ‖speiserZetaDerivRatio ((y : ℂ) * I) -
        leftLowPoleCancelledPhaseCenter y N‖ ≤
      leftLowPoleCancelledPhaseError y N := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := 1 - s
  let Z : ℂ := poleRemovedEulerZetaApprox w N
  let D : ℂ := poleRemovedEulerZetaDerivApprox w N
  let ez : ℝ := poleRemovedEulerZetaError w N
  let ed : ℝ := poleRemovedEulerZetaDerivError w N
  have hwOne : w ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [w, s] at him
    linarith
  have hwRe : 0 < w.re := by norm_num [w, s]
  have hzBound : ‖zetaPoleRemoved w - Z‖ ≤ ez := by
    simpa only [Z, ez] using
      norm_zetaPoleRemoved_sub_poleRemovedEulerZetaApprox_le hwOne hwRe hN
  have hdBound : ‖deriv zetaPoleRemoved w - D‖ ≤ ed := by
    simpa only [D, ed] using
      norm_deriv_zetaPoleRemoved_sub_poleRemovedEulerZetaDerivApprox_le
        hwOne hwRe hN
  have hzMargin' : ez < ‖Z‖ := by
    simpa only [w, s, Z, ez] using hzMargin
  have hratio := norm_ratio_sub_approx_ratio_le hzBound hdBound hzMargin'
  have hpoleRemoved : zetaPoleRemoved w ≠ 0 := by
    intro hzero
    rw [hzero, zero_sub, norm_neg] at hzBound
    linarith
  have hreflected : riemannZeta w ≠ 0 := by
    intro hzero
    apply hpoleRemoved
    rw [zetaPoleRemoved_eq hwOne, hzero, mul_zero]
  have hzeta : riemannZeta s ≠ 0 := by
    simpa only [s] using riemannZeta_ne_zero_on_positive_imaginaryAxis hy
  have hreflection :=
    logDeriv_riemannZeta_eq_neg_logDeriv_zetaPoleRemoved_add_regular
      y hy (by simpa only [s] using hzeta) (by simpa only [w, s] using hreflected)
  have harch :=
    norm_levinsonMontgomeryPoleCancelledArchimedeanComplex_sub_shiftTwoApprox_le
      (s := s) (by norm_num [s]) (by norm_num [s])
  have hdecomp :
      (-deriv zetaPoleRemoved w / zetaPoleRemoved w +
          levinsonMontgomeryPoleCancelledArchimedeanComplex s) -
        (-D / Z +
          levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s) =
      -(deriv zetaPoleRemoved w / zetaPoleRemoved w - D / Z) +
        (levinsonMontgomeryPoleCancelledArchimedeanComplex s -
          levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s) := by ring
  have hphase :
      ‖(-deriv zetaPoleRemoved w / zetaPoleRemoved w +
          levinsonMontgomeryPoleCancelledArchimedeanComplex s) -
        (-D / Z +
          levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s)‖ ≤
        ed / (‖Z‖ - ez) + ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) +
          levinsonMontgomeryArchimedeanShiftTwoError s +
          levinsonMontgomeryArchimedeanShiftTwoError w := by
    rw [hdecomp]
    calc
      ‖-(deriv zetaPoleRemoved w / zetaPoleRemoved w - D / Z) +
          (levinsonMontgomeryPoleCancelledArchimedeanComplex s -
            levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s)‖ ≤
          ‖deriv zetaPoleRemoved w / zetaPoleRemoved w - D / Z‖ +
            ‖levinsonMontgomeryPoleCancelledArchimedeanComplex s -
              levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s‖ := by
        simpa only [norm_neg] using norm_add_le
          (-(deriv zetaPoleRemoved w / zetaPoleRemoved w - D / Z))
          (levinsonMontgomeryPoleCancelledArchimedeanComplex s -
            levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox s)
      _ ≤ (ed / (‖Z‖ - ez) + ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖)) +
          (levinsonMontgomeryArchimedeanShiftTwoError s +
            levinsonMontgomeryArchimedeanShiftTwoError w) := add_le_add hratio harch
      _ = _ := by ring
  have hspeiser :
      speiserZetaDerivRatio ((y : ℂ) * I) =
        -deriv zetaPoleRemoved w / zetaPoleRemoved w +
          levinsonMontgomeryPoleCancelledArchimedeanComplex s := by
    rw [show speiserZetaDerivRatio ((y : ℂ) * I) =
        logDeriv riemannZeta ((y : ℂ) * I) by rfl, hreflection,
      logDeriv_apply]
    dsimp only [s, w]
    ring
  rw [hspeiser]
  unfold leftLowPoleCancelledPhaseCenter leftLowPoleCancelledPhaseError
  dsimp only [s, w, Z, D, ez, ed] at hphase ⊢
  simpa only [neg_div] using hphase

/-- A strict positive real margin of the regular center certifies the actual quotient sign. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_of_poleCancelledPhaseMargin
    (y : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      poleRemovedEulerZetaError (1 - (y : ℂ) * I) N <
        ‖poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) N‖)
    (hphase :
      leftLowPoleCancelledPhaseError y N <
        (leftLowPoleCancelledPhaseCenter y N).re) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re := by
  have hball :=
    norm_speiserZetaDerivRatio_sub_leftLowPoleCancelledPhaseCenter_le
      y hy hN hzMargin
  have hre := Complex.abs_re_le_norm
    (speiserZetaDerivRatio ((y : ℂ) * I) -
      leftLowPoleCancelledPhaseCenter y N)
  rw [Complex.sub_re] at hre
  have habs := hre.trans hball
  linarith [neg_abs_le
    ((speiserZetaDerivRatio ((y : ℂ) * I)).re -
      (leftLowPoleCancelledPhaseCenter y N).re)]

/-- At cutoff one the pole-removed value center is an exact quadratic polynomial. -/
theorem poleRemovedEulerZetaApprox_leftLow_one_eq
    {y : ℝ} (hy : 0 < y) :
    poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) 1 =
      ((1 - y ^ 2 / 12 : ℝ) : ℂ) - ((7 * y / 12 : ℝ) : ℂ) * I := by
  unfold poleRemovedEulerZetaApprox eulerMaclaurinTwoZetaApprox
    eulerMaclaurinOneZetaApprox abelZetaApprox zetaPartialSum
  apply Complex.ext
  · norm_num [Finset.sum_range_succ, pow_two, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp [hy.ne']
    ring
  · norm_num [Finset.sum_range_succ, pow_two, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring

/-- At cutoff one the pole-removed derivative center is an exact affine polynomial. -/
theorem poleRemovedEulerZetaDerivApprox_leftLow_one_eq
    {y : ℝ} (hy : 0 < y) :
    poleRemovedEulerZetaDerivApprox (1 - (y : ℂ) * I) 1 =
      ((7 / 12 : ℝ) : ℂ) - ((y / 6 : ℝ) : ℂ) * I := by
  let w : ℂ := 1 - (y : ℂ) * I
  have hwOne : w ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [w] at him
    linarith
  have hwRe : 0 < w.re := by norm_num [w]
  rw [show poleRemovedEulerZetaDerivApprox w 1 =
      eulerMaclaurinTwoZetaApprox w 1 +
        (w - 1) * eulerMaclaurinTwoZetaDerivApprox w 1 by rfl,
    eulerMaclaurinTwoZetaDerivApprox_eq_finiteFormula w hwOne hwRe
      (by norm_num : 1 ≤ (1 : ℕ))]
  unfold eulerMaclaurinTwoZetaApprox eulerMaclaurinOneZetaApprox abelZetaApprox
    eulerMaclaurinTwoZetaDerivFiniteFormula
    eulerMaclaurinOneZetaDerivFiniteFormula
    eulerMaclaurinTwoCorrectionDerivFiniteFormula zetaPartialSum
  dsimp only [w]
  apply Complex.ext
  · norm_num [Finset.sum_range_succ, pow_two, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  · norm_num [Finset.sum_range_succ, pow_two, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp [hy.ne']
    ring

/-- The six rational reciprocal corrections in the regular archimedean center. -/
def leftLowPoleCancelledReciprocalReal (y : ℝ) : ℝ :=
  let s : ℂ := (y : ℂ) * I
  ((1 / (2 * (s / 2 + 3)) + 1 / (s / 2 + 1) + 1 / (s / 2 + 2) +
    1 / (2 * ((1 - s) / 2 + 3)) + 1 / ((1 - s) / 2 + 1) +
    1 / ((1 - s) / 2 + 2)).re) / 2

/-- The rational reciprocal correction retains a uniform low-height lower bound. -/
theorem sevenFifths_le_leftLowPoleCancelledReciprocalReal
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    (7 / 5 : ℝ) ≤ leftLowPoleCancelledReciprocalReal y := by
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  have h36 : (0 : ℝ) < 36 + y ^ 2 := by positivity
  have h4 : (0 : ℝ) < 4 + y ^ 2 := by positivity
  have h16 : (0 : ℝ) < 16 + y ^ 2 := by positivity
  have h49 : (0 : ℝ) < 49 + y ^ 2 := by positivity
  have h9 : (0 : ℝ) < 9 + y ^ 2 := by positivity
  have h25 : (0 : ℝ) < 25 + y ^ 2 := by positivity
  have hid :
      leftLowPoleCancelledReciprocalReal y =
        (6 / (36 + y ^ 2) + 4 / (4 + y ^ 2) + 8 / (16 + y ^ 2) +
          7 / (49 + y ^ 2) + 6 / (9 + y ^ 2) + 10 / (25 + y ^ 2)) / 2 := by
    unfold leftLowPoleCancelledReciprocalReal
    norm_num [Complex.div_re, Complex.normSq_apply, Complex.mul_re,
      Complex.mul_im, pow_two]
    field_simp [h36.ne', h4.ne', h16.ne', h49.ne', h9.ne', h25.ne']
    ring
  rw [hid]
  have t36 : (96 / 577 : ℝ) ≤ 6 / (36 + y ^ 2) := by
    rw [le_div_iff₀ h36]
    nlinarith
  have t4 : (64 / 65 : ℝ) ≤ 4 / (4 + y ^ 2) := by
    rw [le_div_iff₀ h4]
    nlinarith
  have t16 : (128 / 257 : ℝ) ≤ 8 / (16 + y ^ 2) := by
    rw [le_div_iff₀ h16]
    nlinarith
  have t49 : (112 / 785 : ℝ) ≤ 7 / (49 + y ^ 2) := by
    rw [le_div_iff₀ h49]
    nlinarith
  have t9 : (96 / 145 : ℝ) ≤ 6 / (9 + y ^ 2) := by
    rw [le_div_iff₀ h9]
    nlinarith
  have t25 : (160 / 401 : ℝ) ≤ 10 / (25 + y ^ 2) := by
    rw [le_div_iff₀ h25]
    nlinarith
  linarith

/-- The exact cutoff-one pole-removed finite quotient loses less than `3/5` in real part. -/
theorem neg_threeFifths_lt_neg_poleRemovedEulerZetaRatio_one_re
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1 / 4) :
    -(3 / 5 : ℝ) <
      (-(poleRemovedEulerZetaDerivApprox (1 - (y : ℂ) * I) 1 /
        poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) 1)).re := by
  rw [poleRemovedEulerZetaApprox_leftLow_one_eq hy,
    poleRemovedEulerZetaDerivApprox_leftLow_one_eq hy]
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  rw [Complex.neg_re, Complex.div_re]
  norm_num [pow_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  have ha : 0 < 1 - y ^ 2 / 12 := by nlinarith
  have hden : 0 <
      (1 - y ^ 2 / 12) * (1 - y ^ 2 / 12) +
        (7 * y / 12) * (7 * y / 12) := by nlinarith [sq_nonneg (7 * y / 12)]
  rw [← pow_two y]
  rw [show
      7 / 12 * (1 - y ^ 2 / 12) /
            ((1 - y ^ 2 / 12) * (1 - y ^ 2 / 12) +
              (7 * y / 12) * (7 * y / 12)) +
          y / 6 * (7 * y / 12) /
            ((1 - y ^ 2 / 12) * (1 - y ^ 2 / 12) +
              (7 * y / 12) * (7 * y / 12)) =
        (7 / 12 * (1 - y ^ 2 / 12) + y / 6 * (7 * y / 12)) /
          ((1 - y ^ 2 / 12) * (1 - y ^ 2 / 12) +
            (7 * y / 12) * (7 * y / 12)) by ring,
    div_lt_iff₀ hden]
  nlinarith [sq_nonneg (y ^ 2)]

/-- Each logarithm argument in the twice-shifted center has norm below four. -/
theorem leftLowPoleCancelled_logArguments_norm_lt_four
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    ‖((y : ℂ) * I) / 2 + 3‖ < 4 ∧
      ‖(1 - (y : ℂ) * I) / 2 + 3‖ < 4 := by
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  constructor
  · rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4),
      Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    nlinarith
  · rw [← sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4),
      Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    nlinarith

/-- Exact real-part decomposition of the regular low-height archimedean center. -/
theorem levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox_re_eq
    (y : ℝ) :
    (levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox
      ((y : ℂ) * I)).re =
      1 / (1 + y ^ 2) + Real.log Real.pi -
        (Real.log ‖((y : ℂ) * I) / 2 + 3‖ +
          Real.log ‖(1 - (y : ℂ) * I) / 2 + 3‖) / 2 +
        leftLowPoleCancelledReciprocalReal y := by
  unfold levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox
    levinsonMontgomeryDigammaComplexShiftTwoApprox
    leftLowPoleCancelledReciprocalReal
  norm_num only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.div_re,
    Complex.ofReal_re, Complex.natCast_re, Complex.one_re, Complex.log_re]
  norm_num [pow_two, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- The regular archimedean finite center has real part greater than one near zero. -/
theorem one_lt_levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox_re
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    1 < (levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox
      ((y : ℂ) * I)).re := by
  have hrec := sevenFifths_le_leftLowPoleCancelledReciprocalReal hy0 hy1
  have hnorm := leftLowPoleCancelled_logArguments_norm_lt_four hy0 hy1
  have hlog1 : Real.log ‖((y : ℂ) * I) / 2 + 3‖ < Real.log 4 :=
    Real.log_lt_log (by
      rw [norm_pos_iff]
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im] at hre) hnorm.1
  have hlog2 : Real.log ‖(1 - (y : ℂ) * I) / 2 + 3‖ < Real.log 4 :=
    Real.log_lt_log (by
      rw [norm_pos_iff]
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im] at hre) hnorm.2
  have hlogFour : Real.log 4 < (7 / 5 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only
    linarith [Real.log_two_lt_d9]
  have hlogPi : 1 < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    exact Real.exp_one_lt_three.trans Real.pi_gt_three
  rw [levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox_re_eq]
  have hinv : 0 < 1 / (1 + y ^ 2) := by positivity
  linarith

/-- The complete cutoff-one pole-cancelled phase center retains a wide positive real margin. -/
theorem twoFifths_lt_leftLowPoleCancelledPhaseCenter_one_re
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1 / 4) :
    (2 / 5 : ℝ) < (leftLowPoleCancelledPhaseCenter y 1).re := by
  have hfinite := neg_threeFifths_lt_neg_poleRemovedEulerZetaRatio_one_re hy hy1
  have harch :=
    one_lt_levinsonMontgomeryPoleCancelledArchimedeanComplexShiftTwoApprox_re
      hy.le hy1
  unfold leftLowPoleCancelledPhaseCenter
  norm_num only [Complex.add_re]
  linarith

private theorem norm_leftLowReflectedPoint_le_thirtyThreeThirtySeconds
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    ‖1 - (y : ℂ) * I‖ ≤ (33 / 32 : ℝ) := by
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 33 / 32),
    Complex.sq_norm, Complex.normSq_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  nlinarith

private theorem norm_leftLowReflectedPoint_add_one_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    ‖(1 - (y : ℂ) * I) + 1‖ ≤ (129 / 64 : ℝ) := by
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 129 / 64),
    Complex.sq_norm, Complex.normSq_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  nlinarith

private theorem norm_leftLowReflectedPoint_add_two_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    ‖(1 - (y : ℂ) * I) + 2‖ ≤ (193 / 64 : ℝ) := by
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 193 / 64),
    Complex.sq_norm, Complex.normSq_apply]
  norm_num [Complex.mul_re, Complex.mul_im]
  nlinarith

private theorem norm_leftLowReflectedProduct_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    ‖(1 - (y : ℂ) * I) * ((1 - (y : ℂ) * I) + 1) *
        ((1 - (y : ℂ) * I) + 2)‖ ≤ (63 / 10 : ℝ) := by
  rw [norm_mul, norm_mul]
  calc
    ‖1 - (y : ℂ) * I‖ * ‖(1 - (y : ℂ) * I) + 1‖ *
        ‖(1 - (y : ℂ) * I) + 2‖ ≤
        (33 / 32 : ℝ) * (129 / 64) * (193 / 64) := by
      gcongr
      · exact norm_leftLowReflectedPoint_le_thirtyThreeThirtySeconds hy0 hy1
      · exact norm_leftLowReflectedPoint_add_one_le hy0 hy1
      · exact norm_leftLowReflectedPoint_add_two_le hy0 hy1
    _ ≤ 63 / 10 := by norm_num

private theorem norm_leftLowReflectedDerivPolynomial_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    ‖3 * (1 - (y : ℂ) * I) ^ 2 + 6 * (1 - (y : ℂ) * I) + 2‖ ≤
      (45 / 4 : ℝ) := by
  have hySq : y ^ 2 ≤ (1 / 16 : ℝ) := by nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 45 / 4),
    Complex.sq_norm, Complex.normSq_apply]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg (y ^ 2)]

/-- The cutoff-one zeta value remainder is uniformly below `7/160`. -/
theorem eulerMaclaurinTwoZetaError_leftLow_one_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 1 ≤ (7 / 160 : ℝ) := by
  unfold eulerMaclaurinTwoZetaError
  norm_num
  have hp := norm_leftLowReflectedProduct_le hy0 hy1
  rw [norm_mul, norm_mul] at hp
  linarith

/-- The cutoff-one zeta derivative remainder is uniformly below `3/32`. -/
theorem eulerMaclaurinTwoZetaDerivError_leftLow_one_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) 1 ≤ (3 / 32 : ℝ) := by
  unfold eulerMaclaurinTwoZetaDerivError
  norm_num
  have hp := norm_leftLowReflectedDerivPolynomial_le hy0 hy1
  have hq := norm_leftLowReflectedProduct_le hy0 hy1
  rw [norm_mul, norm_mul] at hq
  linarith

/-- Pole cancellation shrinks the cutoff-one value radius below `1/80`. -/
theorem poleRemovedEulerZetaError_leftLow_one_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    poleRemovedEulerZetaError (1 - (y : ℂ) * I) 1 ≤ (1 / 80 : ℝ) := by
  have he := eulerMaclaurinTwoZetaError_leftLow_one_le hy0 hy1
  unfold poleRemovedEulerZetaError
  have hnorm : ‖(1 - (y : ℂ) * I) - 1‖ = y := by
    rw [show (1 - (y : ℂ) * I) - 1 = -(y : ℂ) * I by ring,
      norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hy0]
  rw [hnorm]
  have he0 : 0 ≤ eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 1 := by
    unfold eulerMaclaurinTwoZetaError
    norm_num
    positivity
  calc
    y * eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 1 ≤
        (1 / 4 : ℝ) * (7 / 160) := by
      gcongr
    _ ≤ 1 / 80 := by norm_num

/-- The cutoff-one pole-removed derivative radius is below `7/100`. -/
theorem poleRemovedEulerZetaDerivError_leftLow_one_le
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    poleRemovedEulerZetaDerivError (1 - (y : ℂ) * I) 1 ≤ (7 / 100 : ℝ) := by
  have he := eulerMaclaurinTwoZetaError_leftLow_one_le hy0 hy1
  have hed := eulerMaclaurinTwoZetaDerivError_leftLow_one_le hy0 hy1
  unfold poleRemovedEulerZetaDerivError
  have hnorm : ‖(1 - (y : ℂ) * I) - 1‖ = y := by
    rw [show (1 - (y : ℂ) * I) - 1 = -(y : ℂ) * I by ring,
      norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_I,
      mul_one, abs_of_nonneg hy0]
  rw [hnorm]
  have hed0 : 0 ≤
      eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) 1 := by
    unfold eulerMaclaurinTwoZetaDerivError
    norm_num
    positivity
  calc
    eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 1 +
        y * eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) 1 ≤
      (7 / 160 : ℝ) + (1 / 4) * (3 / 32) := by
        gcongr
    _ ≤ 7 / 100 := by norm_num

/-- At positive height the cutoff-one pole-removed value center stays uniformly away from zero. -/
theorem ninetyNineHundredths_le_norm_poleRemovedEulerZetaApprox_leftLow_one
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1 / 4) :
    (99 / 100 : ℝ) ≤
      ‖poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) 1‖ := by
  rw [poleRemovedEulerZetaApprox_leftLow_one_eq hy]
  calc
    (99 / 100 : ℝ) ≤ 1 - y ^ 2 / 12 := by nlinarith
    _ = ((((1 - y ^ 2 / 12 : ℝ) : ℂ) -
        ((7 * y / 12 : ℝ) : ℂ) * I)).re := by
          norm_num [pow_two, Complex.mul_re, Complex.mul_im]
    _ ≤ ‖(((1 - y ^ 2 / 12 : ℝ) : ℂ) -
        ((7 * y / 12 : ℝ) : ℂ) * I)‖ :=
      (le_abs_self _).trans (Complex.abs_re_le_norm _)

/-- The cutoff-one pole-removed derivative center has norm at most `5/8`. -/
theorem norm_poleRemovedEulerZetaDerivApprox_leftLow_one_le
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1 / 4) :
    ‖poleRemovedEulerZetaDerivApprox (1 - (y : ℂ) * I) 1‖ ≤ (5 / 8 : ℝ) := by
  rw [poleRemovedEulerZetaDerivApprox_leftLow_one_eq hy]
  have hySix : 0 ≤ y / 6 := by positivity
  calc
    ‖((7 / 12 : ℝ) : ℂ) - ((y / 6 : ℝ) : ℂ) * I‖ ≤
        |((((7 / 12 : ℝ) : ℂ) - ((y / 6 : ℝ) : ℂ) * I).re)| +
          |((((7 / 12 : ℝ) : ℂ) - ((y / 6 : ℝ) : ℂ) * I).im)| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 7 / 12 + y / 6 := by
      norm_num [Complex.mul_re, Complex.mul_im, abs_of_nonneg hySix]
    _ ≤ 5 / 8 := by linarith

/-- The two shifted digamma remainder radii total at most `1/24` near zero. -/
theorem leftLowPoleCancelledArchimedeanErrors_le
    {y : ℝ} (_hy0 : 0 ≤ y) (_hy1 : y ≤ 1 / 4) :
    levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) +
        levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I) ≤
      (1 / 24 : ℝ) := by
  have hfirst :
      levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) ≤
        (3 / 128 : ℝ) := by
    unfold levinsonMontgomeryArchimedeanShiftTwoError
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    rw [show y / 2 * (y / 2) = y ^ 2 / 4 by ring]
    have hden : 0 < 128 * (9 + y ^ 2 / 4) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg y]
  have hsecond :
      levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I) ≤
        (27 / 1568 : ℝ) := by
    unfold levinsonMontgomeryArchimedeanShiftTwoError
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    rw [show -y / 2 * (-y / 2) = y ^ 2 / 4 by ring]
    have hden : 0 < 128 * (49 / 4 + y ^ 2 / 4) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg y]
  linarith

/-- The cutoff-one pole-removed value ball has a strict nonvanishing margin. -/
theorem poleRemovedEulerZetaError_leftLow_one_lt_norm
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1 / 4) :
    poleRemovedEulerZetaError (1 - (y : ℂ) * I) 1 <
      ‖poleRemovedEulerZetaApprox (1 - (y : ℂ) * I) 1‖ := by
  have he := poleRemovedEulerZetaError_leftLow_one_le hy.le hy1
  have hz := ninetyNineHundredths_le_norm_poleRemovedEulerZetaApprox_leftLow_one hy hy1
  linarith

/-- The complete cutoff-one pole-cancelled phase radius is at most `1/8`. -/
theorem leftLowPoleCancelledPhaseError_one_le
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1 / 4) :
    leftLowPoleCancelledPhaseError y 1 ≤ (1 / 8 : ℝ) := by
  let w : ℂ := 1 - (y : ℂ) * I
  let Z : ℂ := poleRemovedEulerZetaApprox w 1
  let D : ℂ := poleRemovedEulerZetaDerivApprox w 1
  let ez : ℝ := poleRemovedEulerZetaError w 1
  let ed : ℝ := poleRemovedEulerZetaDerivError w 1
  have hez : ez ≤ (1 / 80 : ℝ) := by
    simpa only [ez, w] using poleRemovedEulerZetaError_leftLow_one_le hy.le hy1
  have hed : ed ≤ (7 / 100 : ℝ) := by
    simpa only [ed, w] using poleRemovedEulerZetaDerivError_leftLow_one_le hy.le hy1
  have hZ : (99 / 100 : ℝ) ≤ ‖Z‖ := by
    simpa only [Z, w] using
      ninetyNineHundredths_le_norm_poleRemovedEulerZetaApprox_leftLow_one hy hy1
  have hD : ‖D‖ ≤ (5 / 8 : ℝ) := by
    simpa only [D, w] using norm_poleRemovedEulerZetaDerivApprox_leftLow_one_le hy hy1
  have hgap : (39 / 40 : ℝ) ≤ ‖Z‖ - ez := by linarith
  have hgapPos : 0 < ‖Z‖ - ez := lt_of_lt_of_le (by norm_num) hgap
  have hez0 : 0 ≤ ez := by
    dsimp only [ez, w]
    unfold poleRemovedEulerZetaError
    have he0 : 0 ≤ eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 1 := by
      unfold eulerMaclaurinTwoZetaError
      norm_num
      positivity
    exact mul_nonneg (norm_nonneg _) he0
  have hed0 : 0 ≤ ed := by
    dsimp only [ed, w]
    unfold poleRemovedEulerZetaDerivError
    have he0 : 0 ≤ eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 1 := by
      unfold eulerMaclaurinTwoZetaError
      norm_num
      positivity
    have hed0' : 0 ≤
        eulerMaclaurinTwoZetaDerivError (1 - (y : ℂ) * I) 1 := by
      unfold eulerMaclaurinTwoZetaDerivError
      norm_num
      positivity
    positivity
  have htermOne : ed / (‖Z‖ - ez) ≤ (29 / 400 : ℝ) := by
    rw [div_le_iff₀ hgapPos]
    linarith
  have hdenProduct : (39 / 40 : ℝ) * (99 / 100) ≤
      (‖Z‖ - ez) * ‖Z‖ := by
    exact mul_le_mul hgap hZ (by norm_num) (by positivity)
  have hdenProductPos : 0 < (‖Z‖ - ez) * ‖Z‖ :=
    mul_pos hgapPos (lt_of_lt_of_le (by norm_num) hZ)
  have hnumProduct : ‖D‖ * ez ≤ (5 / 8 : ℝ) * (1 / 80) := by
    exact mul_le_mul hD hez hez0 (by norm_num)
  have htermTwo : ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) ≤ (1 / 120 : ℝ) := by
    rw [div_le_iff₀ hdenProductPos]
    calc
      ‖D‖ * ez ≤ (5 / 8 : ℝ) * (1 / 80) := hnumProduct
      _ ≤ (1 / 120 : ℝ) * ((39 / 40) * (99 / 100)) := by norm_num
      _ ≤ (1 / 120 : ℝ) * ((‖Z‖ - ez) * ‖Z‖) := by gcongr
  have harch := leftLowPoleCancelledArchimedeanErrors_le hy.le hy1
  unfold leftLowPoleCancelledPhaseError
  dsimp only [w, Z, D, ez, ed]
  linarith

/-- The actual zeta logarithmic derivative has positive real part on the frozen low cell. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_oneQuarter
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 4) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re := by
  rcases eq_or_lt_of_le hy0 with rfl | hy
  · exact speiserZetaDerivRatio_leftVertical_re_pos_at_zero
  · apply speiserZetaDerivRatio_leftVertical_re_pos_of_poleCancelledPhaseMargin
      y hy (by norm_num : 1 ≤ (1 : ℕ))
    · exact poleRemovedEulerZetaError_leftLow_one_lt_norm hy hy1
    · have herr := leftLowPoleCancelledPhaseError_one_le hy hy1
      have hcenter := twoFifths_lt_leftLowPoleCancelledPhaseCenter_one_re hy hy1
      linarith

/-- A future positive-real producer on `[1/4,6]` joins directly to the closed low cell. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_zero_six_of_oneQuarter_six
    (hupper : ∀ y : ℝ, 1 / 4 ≤ y → y ≤ 6 →
      0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re)
    {y : ℝ} (hy0 : 0 ≤ y) (hy6 : y ≤ 6) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re := by
  by_cases hyQuarter : y ≤ 1 / 4
  · exact speiserZetaDerivRatio_leftVertical_re_pos_zero_oneQuarter hy0 hyQuarter
  · exact hupper y (by linarith) hy6

end

end LeanLab.Riemann
