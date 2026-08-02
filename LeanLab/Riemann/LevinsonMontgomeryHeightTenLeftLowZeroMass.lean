import LeanLab.Riemann.LevinsonMontgomeryHeightTenLeftResidual
import LeanLab.Riemann.LevinsonMontgomeryHeightTenRiemannSiegelTailIntegral
import LeanLab.Riemann.HardyCriticalLineSign

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Low critical-line zero mass on the height-ten left boundary

This module retains one actual critical-line zero term in the Levinson--Montgomery paired sum.
It reduces the residual imaginary-axis interval `13/2 <= y <= 7` to a kernel-checked Hardy-xi
sign bracket between heights fourteen and fifteen.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

private theorem digamma_eq_shift_nat_sub_sum
    (w : ℂ) (n : ℕ)
    (hregular : ∀ k : ℕ, k < n → ∀ m : ℕ, w + k ≠ -m) :
    Complex.digamma w = Complex.digamma (w + n) -
      ∑ k ∈ Finset.range n, 1 / (w + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hregular' : ∀ k : ℕ, k < n → ∀ m : ℕ, w + k ≠ -m := by
        intro k hk
        exact hregular k (Nat.lt_succ_of_lt hk)
      have hshiftRegular : ∀ m : ℕ, w + n ≠ -m :=
        hregular n (Nat.lt_succ_self n)
      have hshift := Complex.digamma_apply_add_one (w + n) hshiftRegular
      rw [ih hregular']
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      change Complex.digamma (w + n) -
          (∑ k ∈ Finset.range n, 1 / (w + k)) =
        Complex.digamma (w + (n + 1)) -
          ((∑ k ∈ Finset.range n, 1 / (w + k)) + 1 / (w + n))
      rw [show w + ((n : ℂ) + 1) = (w + n) + 1 by ring]
      rw [hshift]
      ring

theorem log_sevenThousandSevenHundredSeventeen_div_oneThousand_gt_twoThousandFortyThree_div_oneThousand :
    (2043 / 1000 : ℝ) < Real.log (7717 / 1000) := by
  have hlog := abs_log_sub_binaryLogCenter_le
    (u := (7717 / 1000 : ℝ)) (by norm_num) 3 10
  have hlower := (abs_le.mp hlog).1
  have hcenter :
      (2043 / 1000 : ℝ) <
        binaryLogCenter 3 10 (7717 / 1000) -
          binaryLogError 3 10 (7717 / 1000) := by
    norm_num [binaryLogCenter, binaryLogError, logAtanhPartial,
      Finset.sum_range_succ]
  linarith

/-- The phase enclosure on the first Riemann--Siegel segment fixes the prefactor orientation. -/
theorem heightTenRiemannSiegelPrefactor_re_pos
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    0 < (deBruijnNewmanRiemannSiegelPrefactor
      (heightTenRiemannSiegelCriticalPoint y)).re := by
  let c := heightTenRiemannSiegelPrefactorScale y
  let W := heightTenRiemannSiegelStirlingExponent y +
    deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint y / 2)
  let theta := Real.pi + W.im
  have hcPos : 0 < c := by
    dsimp [c, heightTenRiemannSiegelPrefactorScale]
    have hyPos : 0 < y := by linarith
    positivity
  have htheta : |theta| < 7 / 16 := by
    exact abs_heightTenRiemannSiegel_totalShiftedPhase_lt_sevenSixteenths hy0 hy1
  have hthetaSq : theta ^ 2 < (7 / 16 : ℝ) ^ 2 := by
    simpa [pow_two, sq_abs] using
      mul_self_lt_mul_self (abs_nonneg theta) htheta
  have hcosLower := Real.one_sub_sq_div_two_le_cos (x := theta)
  have hcosTheta : (9 / 10 : ℝ) < Real.cos theta := by
    nlinarith
  have hcosW : Real.cos W.im < -(9 / 10 : ℝ) := by
    have hshift : Real.cos theta = -Real.cos W.im := by
      dsimp [theta]
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
      ring
    linarith
  have hnegCos : 0 < -Real.cos W.im := by linarith
  have hproduct : 0 < c * Real.exp W.re * (-Real.cos W.im) :=
    mul_pos (mul_pos hcPos (Real.exp_pos _)) hnegCos
  rw [heightTenRiemannSiegelPrefactor_eq_phaseExponential]
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re]
  simp only [neg_zero, zero_mul, sub_zero]
  convert hproduct using 1
  dsimp [c, W]
  ring

/-- The existing endpoint-mass estimate and the oriented phase imply the positive endpoint. -/
theorem hardyXi_ten_pos :
    0 < hardyXi 10 := by
  let s : ℂ := heightTenRiemannSiegelCriticalPoint 10
  have hsRe : s.re = 1 / 2 := by simp [s]
  have hsNoninteger : deBruijnNewmanRiemannSiegelIsNoninteger s := by
    simpa using
      (deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero
        (s := s) (by norm_num [s]) 0)
  have hprefPos :
      0 < (deBruijnNewmanRiemannSiegelPrefactor s).re := by
    simpa [s] using heightTenRiemannSiegelPrefactor_re_pos
      (by norm_num : (13 / 2 : ℝ) ≤ 10) le_rfl
  have hmargin :
      |(deBruijnNewmanRiemannSiegelR0N 1 s).re| <
        |(deBruijnNewmanRiemannSiegelPrefactor s).re| := by
    simpa [s, heightTenRiemannSiegelCriticalPoint] using
      heightTenRiemannSiegelOneRemainderMargin 10
        (by norm_num : (13 / 2 : ℝ) ≤ 10) le_rfl
  have hsumPos :
      0 < (deBruijnNewmanRiemannSiegelPrefactor s +
        deBruijnNewmanRiemannSiegelR0N 1 s).re := by
    rw [Complex.add_re]
    rw [abs_of_pos hprefPos] at hmargin
    have hremLower := (neg_lt_of_abs_lt hmargin)
    linarith
  have hidentity :=
    riemannSiegel_criticalLine_one_eq_prefactor_remainder_re hsRe hsNoninteger
  have hsHardy : hardyCriticalLinePoint 10 = s := by
    apply Complex.ext <;> norm_num [hardyCriticalLinePoint, s,
      heightTenRiemannSiegelCriticalPoint]
  have hreal := congrArg Complex.re hidentity
  have hxiReal : (riemannXi s).re = hardyXi 10 := by
    rw [← hsHardy]
    rfl
  norm_num at hreal
  rw [hxiReal] at hreal
  have hsumPos' :
      0 < (deBruijnNewmanRiemannSiegelPrefactor s).re +
        (deBruijnNewmanRiemannSiegelR0N 1 s).re := by
    simpa only [Complex.add_re] using hsumPos
  have hscaled : 0 < (1 / 8 : ℝ) * hardyXi 10 := by
    rw [hreal]
    exact mul_pos (by norm_num) hsumPos'
  by_contra h
  have hnonpos : hardyXi 10 ≤ 0 := le_of_not_gt h
  have hscaledNonpos : (1 / 8 : ℝ) * hardyXi 10 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hnonpos
  exact (not_le_of_gt hscaled) hscaledNonpos

theorem log_twentySeven_div_ten_gt_ninetyNine_div_oneHundred :
    (99 / 100 : ℝ) < Real.log (27 / 10) := by
  have h := abs_log_div_sub_logAtanhPartial_le
    (a := (27 : ℝ)) (b := (10 : ℝ)) (by norm_num) (by norm_num) 8
  have hlower := (abs_le.mp h).1
  have hcert :
      (99 / 100 : ℝ) <
        logAtanhPartial 8 ((27 - 10 : ℝ) / (27 + 10)) -
          2 * (|((27 - 10 : ℝ) / (27 + 10))| ^ (2 * 8 + 1) /
            (1 - ((27 - 10 : ℝ) / (27 + 10)) ^ 2)) := by
    norm_num [logAtanhPartial, Finset.sum_range_succ]
  norm_num only at hlower
  linarith

theorem heightSeventeenRiemannSiegel_halfCriticalRatio_lower :
    (27 / 10 : ℝ) ≤
      ‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos]
  apply (sq_le_sq₀ (by positivity)
    (norm_nonneg (heightTenRiemannSiegelCriticalPoint 17 / 2))).mp
  have hnormSq :
      ‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ ^ 2 = 1157 / 16 := by
    calc
      _ = 1 / 16 + (17 : ℝ) ^ 2 / 4 :=
        heightTenRiemannSiegel_halfCritical_norm_sq 17
      _ = 1157 / 16 := by norm_num
  have hpi : Real.pi ≤ (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h.le
  have hpiSq : Real.pi ^ 2 ≤ (31416 / 10000 : ℝ) ^ 2 := by
    nlinarith [Real.pi_pos]
  rw [hnormSq]
  nlinarith

theorem heightSeventeenRiemannSiegel_halfCriticalRatio_upper :
    ‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ / Real.pi ≤ (271 / 100 : ℝ) := by
  rw [div_le_iff₀ Real.pi_pos]
  apply (sq_le_sq₀
    (norm_nonneg (heightTenRiemannSiegelCriticalPoint 17 / 2)) (by positivity)).mp
  have hnormSq :
      ‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ ^ 2 = 1157 / 16 := by
    calc
      _ = 1 / 16 + (17 : ℝ) ^ 2 / 4 :=
        heightTenRiemannSiegel_halfCritical_norm_sq 17
      _ = 1157 / 16 := by norm_num
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hpiSq : (31415 / 10000 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_pos]
  rw [hnormSq]
  nlinarith

theorem heightSeventeenRiemannSiegel_logRatio_gt_ninetyNine_div_oneHundred :
    (99 / 100 : ℝ) <
      Real.log (‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ / Real.pi) := by
  exact log_twentySeven_div_ten_gt_ninetyNine_div_oneHundred.trans_le
    (Real.log_le_log (by norm_num)
      heightSeventeenRiemannSiegel_halfCriticalRatio_lower)

theorem heightSeventeenRiemannSiegel_logRatio_lt_one :
    Real.log (‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ / Real.pi) < 1 := by
  have hratioPos :
      0 < ‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ / Real.pi := by
    have hnormSq := heightTenRiemannSiegel_halfCritical_norm_sq 17
    have hnormPos : 0 < ‖heightTenRiemannSiegelCriticalPoint 17 / 2‖ := by
      nlinarith [norm_nonneg (heightTenRiemannSiegelCriticalPoint 17 / 2)]
    exact div_pos hnormPos Real.pi_pos
  rw [Real.log_lt_iff_lt_exp hratioPos]
  exact heightSeventeenRiemannSiegel_halfCriticalRatio_upper.trans_lt
    (by nlinarith [Real.exp_one_gt_d9])

theorem heightSeventeenRiemannSiegelStirlingPhase_gt_fiftyThree_div_twenty :
    (53 / 20 : ℝ) < heightTenRiemannSiegelStirlingPhase 17 := by
  rw [heightTenRiemannSiegelStirlingPhase_eq_inverseArctan (by norm_num)]
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hlog :=
    heightSeventeenRiemannSiegel_logRatio_gt_ninetyNine_div_oneHundred
  have harg : 0 ≤ Real.arctan (1 / (2 * 17 : ℝ)) :=
    Real.arctan_nonneg.mpr (by norm_num)
  norm_num only at hpi hlog harg ⊢
  nlinarith

theorem heightSeventeenRiemannSiegelStirlingPhase_lt_fourteen_div_five :
    heightTenRiemannSiegelStirlingPhase 17 < (14 / 5 : ℝ) := by
  rw [heightTenRiemannSiegelStirlingPhase_eq_inverseArctan (by norm_num)]
  have hpi : Real.pi ≤ (31416 / 10000 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num at h ⊢
    exact h.le
  have hlog := heightSeventeenRiemannSiegel_logRatio_lt_one
  have harg : Real.arctan (1 / 34 : ℝ) ≤ 1 / 34 :=
    arctan_le_self_of_nonneg (by norm_num)
  norm_num only at hpi hlog harg ⊢
  nlinarith

theorem norm_heightSeventeenStieltjesLogRemainder_lt_one_div_forty :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint 17 / 2)‖ < 1 / 40 := by
  let z := heightTenRiemannSiegelCriticalPoint 17 / 2
  have hzRe : z.re = 1 / 4 := by norm_num [z]
  have hzIm : z.im = 17 / 2 := by norm_num [z]
  have h := norm_deBruijnNewmanPolymathStieltjesLogRemainder_le_pi_div_im
    (z := z) (by rw [hzRe]; norm_num) (by rw [hzIm]; norm_num)
  rw [hzIm] at h
  have hpi : Real.pi < 13 / 4 := Real.pi_lt_d2.trans (by norm_num)
  exact h.trans_lt (by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 16 * (17 / 2))]
    nlinarith)

theorem heightSeventeenRiemannSiegel_totalShiftedPhase_mem :
    (21 / 8 : ℝ) < Real.pi +
        (heightTenRiemannSiegelStirlingExponent 17 +
          deBruijnNewmanPolymathStieltjesLogRemainder
            (heightTenRiemannSiegelCriticalPoint 17 / 2)).im ∧
      Real.pi +
        (heightTenRiemannSiegelStirlingExponent 17 +
          deBruijnNewmanPolymathStieltjesLogRemainder
            (heightTenRiemannSiegelCriticalPoint 17 / 2)).im < 113 / 40 := by
  let L := deBruijnNewmanPolymathStieltjesLogRemainder
    (heightTenRiemannSiegelCriticalPoint 17 / 2)
  have hLnorm := norm_heightSeventeenStieltjesLogRemainder_lt_one_div_forty
  have hLimAbs : |L.im| < 1 / 40 :=
    (Complex.abs_im_le_norm L).trans_lt hLnorm
  have hLim := abs_lt.mp hLimAbs
  have hlo := heightSeventeenRiemannSiegelStirlingPhase_gt_fiftyThree_div_twenty
  have hhi := heightSeventeenRiemannSiegelStirlingPhase_lt_fourteen_div_five
  rw [Complex.add_im]
  dsimp [heightTenRiemannSiegelStirlingPhase, L] at hlo hhi hLim ⊢
  constructor <;> linarith

theorem heightSeventeenRiemannSiegel_totalShiftedPhase_cos_lt_neg_fourFifths :
    Real.cos
        (Real.pi +
          (heightTenRiemannSiegelStirlingExponent 17 +
            deBruijnNewmanPolymathStieltjesLogRemainder
              (heightTenRiemannSiegelCriticalPoint 17 / 2)).im) <
      -(4 / 5 : ℝ) := by
  let W := heightTenRiemannSiegelStirlingExponent 17 +
    deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint 17 / 2)
  let theta := Real.pi + W.im
  let u := Real.pi - theta
  have htheta : (21 / 8 : ℝ) < theta ∧ theta < 113 / 40 := by
    simpa [theta, W] using heightSeventeenRiemannSiegel_totalShiftedPhase_mem
  have hu0 : 0 ≤ u := by
    dsimp [u]
    have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by
      have h := Real.pi_gt_d4
      norm_num at h ⊢
      exact h.le
    linarith [htheta.2]
  have huUpper : u < 13 / 25 := by
    dsimp [u]
    have hpi : Real.pi ≤ (31416 / 10000 : ℝ) := by
      have h := Real.pi_lt_d4
      norm_num at h ⊢
      exact h.le
    linarith [htheta.1]
  have huSq : u ^ 2 < (13 / 25 : ℝ) ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self hu0 huUpper
  have hcosLower := Real.one_sub_sq_div_two_le_cos (x := u)
  have hcosU : (4 / 5 : ℝ) < Real.cos u := by nlinarith
  have hcosTheta : Real.cos theta = -Real.cos u := by
    have hthetaEq : theta = Real.pi - u := by dsimp [u]; ring
    rw [hthetaEq, Real.cos_sub, Real.cos_pi, Real.sin_pi]
    ring
  change Real.cos theta < -(4 / 5 : ℝ)
  rw [hcosTheta]
  linarith

theorem heightSeventeenRiemannSiegelPrefactor_re_lt_neg_fourFifths_norm :
    (deBruijnNewmanRiemannSiegelPrefactor
        (heightTenRiemannSiegelCriticalPoint 17)).re <
      -(4 / 5 : ℝ) *
        ‖deBruijnNewmanRiemannSiegelPrefactor
          (heightTenRiemannSiegelCriticalPoint 17)‖ := by
  let c := heightTenRiemannSiegelPrefactorScale 17
  let W := heightTenRiemannSiegelStirlingExponent 17 +
    deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint 17 / 2)
  let theta := Real.pi + W.im
  have hcPos : 0 < c := by
    dsimp [c, heightTenRiemannSiegelPrefactorScale]
    positivity
  have hcos : Real.cos theta < -(4 / 5 : ℝ) := by
    exact heightSeventeenRiemannSiegel_totalShiftedPhase_cos_lt_neg_fourFifths
  have hpref := heightTenRiemannSiegelPrefactor_eq_phaseExponential 17
  have hnorm :
      ‖deBruijnNewmanRiemannSiegelPrefactor
          (heightTenRiemannSiegelCriticalPoint 17)‖ =
        c * Real.exp W.re := by
    rw [hpref, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcPos, Complex.norm_exp]
  have hre :
      (deBruijnNewmanRiemannSiegelPrefactor
          (heightTenRiemannSiegelCriticalPoint 17)).re =
        c * Real.exp W.re * Real.cos theta := by
    rw [hpref, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re]
    simp only [neg_zero, zero_mul, sub_zero]
    have hcosShift : Real.cos theta = -Real.cos W.im := by
      dsimp [theta]
      rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
      ring
    rw [hcosShift]
    ring
  rw [hre, hnorm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    mul_lt_mul_of_pos_left hcos (mul_pos hcPos (Real.exp_pos W.re))

theorem heightSeventeen_negativeCompactTotalExponent_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
        (-Real.pi * x ^ 2 -
          Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x) ≤
      (7 / 5 : ℝ) * x - (119 / 20) * x ^ 2 := by
  have harg := heightTen_negativeCompactAnglePolynomial_le hx0 hx1
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 17)
  have hsqrtUpper : Real.sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hfirst :
      (17 / 3 : ℝ) * Real.sqrt 2 ≤
        (17 / 3) * (14143 / 10000) := by gcongr
  have hpiSqrtHalf :
      (111 / 50 : ℝ) ≤ Real.pi * (Real.sqrt 2 / 2) :=
    oneHundredEleven_div_fifty_le_pi_mul_sqrtTwoHalf
  have hlinear :
      (17 / 3 : ℝ) * Real.sqrt 2 -
          3 * (Real.pi * (Real.sqrt 2 / 2)) ≤ 7 / 5 := by
    nlinarith
  have hpiLower : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    norm_num at h ⊢
    exact h.le
  have hquadratic : (119 / 20 : ℝ) ≤ Real.pi + 17 / 6 := by
    nlinarith
  have hlinearMul := mul_le_mul_of_nonneg_right hlinear hx0
  have hquadraticMul := mul_le_mul_of_nonneg_right hquadratic (sq_nonneg x)
  nlinarith

theorem heightSeventeen_negativeCompactTotalExponent_le_oneTwelfth
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
        (-Real.pi * (-x) ^ 2 +
          Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x)) ≤ 1 / 12 := by
  have h := heightSeventeen_negativeCompactTotalExponent_le hx0 hx1
  have hquad : (7 / 5 : ℝ) * x - (119 / 20) * x ^ 2 ≤ 1 / 12 := by
    nlinarith [sq_nonneg (x - 2 / 17)]
  have hleft :
      17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
          (-Real.pi * (-x) ^ 2 +
            Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x)) =
        17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
          (-Real.pi * x ^ 2 -
            Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x) := by ring
  rw [hleft]
  exact h.trans hquad

theorem exp_oneTwelfth_le_twelveElevenths :
    Real.exp (1 / 12 : ℝ) ≤ 12 / 11 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (x := (1 / 12 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le_half
    {v : ℝ} (hv : |v| ≤ 1 / 2) :
    1 / ‖deBruijnNewmanRiemannSiegelDenominator
        (deBruijnNewmanRiemannSiegelLine 1 v)‖ ≤ 1 / 2 := by
  have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le hv
  have hpow :
      0 ≤ (Real.pi * (deBruijnNewmanRiemannSiegelLine 1 v).im) ^ 4 :=
    by positivity
  exact hden.trans (by nlinarith)

theorem norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeCompact_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 17) (-x)‖ ≤ 9 / 20 := by
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hrpow :=
    rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_neg_le hx0
  have hexponent :=
    heightSeventeen_negativeCompactTotalExponent_le_oneTwelfth hx0 hx1
  have hden :=
    one_div_norm_deBruijnNewmanRiemannSiegelDenominator_compact_le_half
      (v := -x) (by simpa [abs_of_nonneg hx0] using hx1)
  have hexp : Real.exp
      (17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
        (-Real.pi * (-x) ^ 2 +
          Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x))) ≤ 12 / 11 :=
    (Real.exp_le_exp.mpr hexponent).trans exp_oneTwelfth_le_twelveElevenths
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 (-x)‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp
            (17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
              (-Real.pi * (-x) ^ 2 +
                Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x))) *
          (1 / ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 (-x))‖) ≤
        (1633 / 2000 : ℝ) * (12 / 11) * (1 / 2) := by
      exact mul_le_mul
        (mul_le_mul hrpow hexp (Real.exp_nonneg _) (by norm_num))
        hden (one_div_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (by norm_num) (by norm_num))
    _ ≤ 9 / 20 := by norm_num

theorem integral_norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeCompact_le :
    (∫ x in Set.Ioc (0 : ℝ) (1 / 2),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 17) (-x)‖) ≤ 9 / 40 := by
  let f : ℝ → ℝ := fun _ => 9 / 20
  have hactual : IntegrableOn (fun x : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 17) (-x)‖) (Set.Ioc 0 (1 / 2)) := by
    exact ((integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 17)).norm.comp_neg).integrableOn
  have hf : IntegrableOn f (Set.Ioc (0 : ℝ) (1 / 2)) := by
    have hc : Continuous f := by
      dsimp [f]
      fun_prop
    exact hc.integrableOn_Ioc
  calc
    (∫ x in Set.Ioc (0 : ℝ) (1 / 2),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint 17) (-x)‖) ≤
        ∫ x in Set.Ioc (0 : ℝ) (1 / 2), f x := by
      apply setIntegral_mono_on hactual hf measurableSet_Ioc
      intro x hx
      exact norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeCompact_le
        hx.1.le hx.2
    _ = ∫ x in (0 : ℝ)..(1 / 2), f x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
    _ = 9 / 40 := by norm_num [f]

theorem heightSeventeen_negativeTailAngleAffine_le
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) ≤
      1 / 25 + (31 / 100 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have harg := arg_deBruijnNewmanRiemannSiegelLine_one_neg_le_ratio hx0
  let t := Real.sqrt 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have htUpper : t ≤ (14143 / 10000 : ℝ) := by
    dsimp [t]
    have hsqrtSq : Real.sqrt 2 ^ 2 = (2 : ℝ) := by norm_num
    nlinarith [Real.sqrt_nonneg 2]
  have hden : 0 < 3 + t * x := by positivity
  have hratio :
      (Real.sqrt 2 / 2 * x) / (3 / 2 + Real.sqrt 2 / 2 * x) =
        t * x / (3 + t * x) := by
    dsimp [t]
    field_simp [hden.ne']
  rw [hratio] at harg
  have hbase : 0 ≤ (117 / 200 : ℝ) - (161 / 400) * t := by
    nlinarith
  have htx : t / 2 ≤ t * x := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hx ht0
  have hbracket :
      0 ≤ (93 / 100 : ℝ) + (31 / 100) * t * x - (161 / 200) * t := by
    nlinarith
  have hprod :
      0 ≤ (x - 1 / 2) *
        ((93 / 100 : ℝ) + (31 / 100) * t * x - (161 / 200) * t) :=
    mul_nonneg (sub_nonneg.mpr hx) hbracket
  have hdiff :
      (1 / 25 + (31 / 100 : ℝ) * x) * (3 + t * x) - t * x =
        ((117 / 200 : ℝ) - (161 / 400) * t) +
          (x - 1 / 2) *
            ((93 / 100 : ℝ) + (31 / 100) * t * x - (161 / 200) * t) := by
    ring
  have hcleared :
      t * x ≤ (1 / 25 + (31 / 100 : ℝ) * x) * (3 + t * x) := by
    rw [← sub_nonneg]
    rw [hdiff]
    positivity
  have hratioAffine :
      t * x / (3 + t * x) ≤ 1 / 25 + (31 / 100 : ℝ) * x := by
    rw [div_le_iff₀ hden]
    exact hcleared
  exact harg.trans hratioAffine

theorem heightSeventeen_negativeTailTotalExponent_le
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
          (-Real.pi * x ^ 2 - Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x) -
        Real.pi * (Real.sqrt 2 / 2) * x ≤
      17 / 25 - (259 / 50 : ℝ) * x := by
  have hx0 : 0 ≤ x := by linarith
  have harg := heightSeventeen_negativeTailAngleAffine_le hx
  have hphase := mul_le_mul_of_nonneg_left harg (by norm_num : (0 : ℝ) ≤ 17)
  have hpiSqrtHalf :
      (111 / 50 : ℝ) ≤ Real.pi * (Real.sqrt 2 / 2) :=
    oneHundredEleven_div_fifty_le_pi_mul_sqrtTwoHalf
  have hpiSqrtMul := mul_le_mul_of_nonneg_right hpiSqrtHalf hx0
  have hpiLower : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    exact h.le
  have hsquare : x / 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hquadDecay : (157 / 100 : ℝ) * x ≤ Real.pi * x ^ 2 := by
    have hhalf : (157 / 100 : ℝ) ≤ Real.pi / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hhalf hx0]
  nlinarith

theorem norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeTail_le
    {x : ℝ} (hx : 1 / 2 ≤ x) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 17) (-x)‖ ≤
      (1633 / 2000 : ℝ) * (9 / 8) *
        Real.exp (17 / 25 - (259 / 50 : ℝ) * x) := by
  have hx0 : 0 ≤ x := by linarith
  rw [norm_heightTenRiemannSiegelLineIntegrand_one_eq_factorization]
  have hrpow := rpow_neg_half_norm_deBruijnNewmanRiemannSiegelLine_one_neg_le hx0
  have hden := one_div_norm_deBruijnNewmanRiemannSiegelDenominator_tail_le
    (v := -x) (by simpa [abs_of_nonneg hx0] using hx)
  have hexponent := heightSeventeen_negativeTailTotalExponent_le hx
  let A := 17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
    (-Real.pi * x ^ 2 - Real.sqrt 2 * Real.pi * (1 + 1 / 2) * x)
  let B := -(Real.pi * (Real.sqrt 2 / 2) * x)
  have hdenB :
      1 / ‖deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 1 (-x))‖ ≤
        (9 / 8 : ℝ) * Real.exp B := by
    simpa [B, abs_of_nonneg hx0] using hden
  rw [show
    17 * Complex.arg (deBruijnNewmanRiemannSiegelLine 1 (-x)) +
        (-Real.pi * (-x) ^ 2 + Real.sqrt 2 * Real.pi * (1 + 1 / 2) * (-x)) = A by
      dsimp [A]
      ring]
  calc
    ‖deBruijnNewmanRiemannSiegelLine 1 (-x)‖ ^ (-(1 / 2 : ℝ)) *
          Real.exp A *
          (1 / ‖deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 1 (-x))‖) ≤
        (1633 / 2000 : ℝ) * Real.exp A * ((9 / 8) * Real.exp B) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)) hdenB
        (one_div_nonneg.mpr (norm_nonneg _))
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    _ = (1633 / 2000 : ℝ) * (9 / 8) * (Real.exp A * Real.exp B) := by ring
    _ = (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (A + B) := by
      rw [Real.exp_add A B]
    _ ≤ (1633 / 2000 : ℝ) * (9 / 8) *
        Real.exp (17 / 25 - (259 / 50 : ℝ) * x) := by
      gcongr
      dsimp [A, B]
      nlinarith

theorem six_le_exp_oneHundredNinetyOne_div_oneHundred :
    (6 : ℝ) ≤ Real.exp (191 / 100) := by
  have hseries := Real.sum_le_exp_of_nonneg
    (x := (191 / 100 : ℝ)) (by norm_num) 7
  have hpartial :
      (6 : ℝ) ≤ ∑ i ∈ range 7,
        (191 / 100 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hpartial.trans hseries

theorem integral_norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeTail_le :
    (∫ x in Set.Ioi (1 / 2 : ℝ),
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 17) (-x)‖) ≤ 3 / 100 := by
  let g : ℝ → ℝ := fun x =>
    (1633 / 2000 : ℝ) * (9 / 8) *
      Real.exp (17 / 25 - (259 / 50 : ℝ) * x)
  have hform : g = fun x =>
      ((1633 / 2000 : ℝ) * (9 / 8) * Real.exp (17 / 25)) *
        Real.exp (-(259 / 50 : ℝ) * x) := by
    funext x
    dsimp [g]
    have hexp :
        Real.exp (17 / 25 - (259 / 50 : ℝ) * x) =
          Real.exp (17 / 25) * Real.exp (-(259 / 50 : ℝ) * x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  have hactual : IntegrableOn (fun x : ℝ =>
      ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
        (heightTenRiemannSiegelCriticalPoint 17) (-x)‖) (Set.Ioi (1 / 2)) := by
    exact ((integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 17)).norm.comp_neg).integrableOn
  have hg : IntegrableOn g (Set.Ioi (1 / 2)) := by
    have hbase := integrableOn_exp_mul_Ioi
      (a := -(259 / 50 : ℝ)) (by norm_num) (1 / 2)
    rw [hform]
    exact hbase.const_mul _
  have hexpInv : Real.exp (-(191 / 100 : ℝ)) ≤ 1 / 6 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num)
        six_le_exp_oneHundredNinetyOne_div_oneHundred
  calc
    (∫ x in Set.Ioi (1 / 2 : ℝ),
        ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
          (heightTenRiemannSiegelCriticalPoint 17) (-x)‖) ≤
        ∫ x in Set.Ioi (1 / 2 : ℝ), g x := by
      apply setIntegral_mono_on hactual hg measurableSet_Ioi
      intro x hx
      exact norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeTail_le hx.le
    _ = (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (17 / 25) *
        (-(Real.exp (-(259 / 50 : ℝ) * (1 / 2))) / (-(259 / 50 : ℝ))) := by
      rw [hform]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_exp_mul_Ioi (a := -(259 / 50 : ℝ)) (by norm_num)]
    _ = (1633 / 2000 : ℝ) * (9 / 8) *
        (Real.exp (-(191 / 100 : ℝ)) / (259 / 50)) := by
      rw [show -(259 / 50 : ℝ) * (1 / 2) = -(259 / 100) by norm_num]
      rw [show -(Real.exp (-(259 / 100 : ℝ))) / (-(259 / 50 : ℝ)) =
        Real.exp (-(259 / 100 : ℝ)) / (259 / 50) by ring]
      have hcombine :
          Real.exp (17 / 25 : ℝ) * Real.exp (-(259 / 100 : ℝ)) =
            Real.exp (-(191 / 100 : ℝ)) := by
        rw [← Real.exp_add]
        norm_num
      calc
        (1633 / 2000 : ℝ) * (9 / 8) * Real.exp (17 / 25) *
              (Real.exp (-(259 / 100 : ℝ)) / (259 / 50)) =
            ((1633 / 2000 : ℝ) * (9 / 8)) *
              (Real.exp (17 / 25) * Real.exp (-(259 / 100 : ℝ))) /
                (259 / 50) := by ring
        _ = ((1633 / 2000 : ℝ) * (9 / 8)) *
              Real.exp (-(191 / 100 : ℝ)) / (259 / 50) := by rw [hcombine]
        _ = (1633 / 2000 : ℝ) * (9 / 8) *
              (Real.exp (-(191 / 100 : ℝ)) / (259 / 50)) := by ring
    _ ≤ 3 / 100 := by
      nlinarith

def heightSeventeenRiemannSiegelNegativeEndpointMass (N : ℕ) : ℝ :=
  ∫ v in Set.Iic (0 : ℝ),
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N
      (heightTenRiemannSiegelCriticalPoint 17) v‖

theorem heightSeventeenRiemannSiegelNegativeEndpointMass_one_le_fiftyOneTwoHundredths :
    heightSeventeenRiemannSiegelNegativeEndpointMass 1 ≤ 51 / 200 := by
  let f : ℝ → ℝ := fun x =>
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 17) (-x)‖
  have hfull : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    exact ((integrable_deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 17)).norm.comp_neg).integrableOn
  have htail : IntegrableOn f (Set.Ioi (1 / 2 : ℝ)) :=
    hfull.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsplit
  have hchange := integral_comp_neg_Ioi (0 : ℝ) (fun v : ℝ =>
    ‖deBruijnNewmanRiemannSiegelLineIntegrand 1
      (heightTenRiemannSiegelCriticalPoint 17) v‖)
  calc
    heightSeventeenRiemannSiegelNegativeEndpointMass 1 =
        ∫ x in Set.Ioi (0 : ℝ), f x := by
      simpa only [heightSeventeenRiemannSiegelNegativeEndpointMass, neg_zero, f]
        using hchange.symm
    _ = (∫ x in Set.Ioc (0 : ℝ) (1 / 2), f x) +
        ∫ x in Set.Ioi (1 / 2 : ℝ), f x := hsplit.symm
    _ ≤ 9 / 40 + 3 / 100 := by
      exact add_le_add
        integral_norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeCompact_le
        integral_norm_heightSeventeenRiemannSiegelLineIntegrand_one_negativeTail_le
    _ = 51 / 200 := by norm_num

theorem norm_cpow_heightTenRiemannSiegelCriticalPoint_le_seventeen_of_nonpos
    (N : ℕ) {v y : ℝ} (hv : v ≤ 0) (hy : y ≤ 17) :
    ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint y)‖ ≤
      ‖deBruijnNewmanRiemannSiegelLine N v ^
        (-heightTenRiemannSiegelCriticalPoint 17)‖ := by
  rw [norm_cpow_neg_heightTenRiemannSiegelCriticalPoint,
    norm_cpow_neg_heightTenRiemannSiegelCriticalPoint]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (Real.rpow_nonneg (norm_nonneg _) _)
  have harg := deBruijnNewmanRiemannSiegelLine_arg_nonneg_of_nonpos N hv
  nlinarith

theorem norm_heightTenRiemannSiegelLineIntegrand_le_seventeen_of_nonpos
    (N : ℕ) {v y : ℝ} (hv : v ≤ 0) (hy : y ≤ 17) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N
        (heightTenRiemannSiegelCriticalPoint y) v‖ ≤
      ‖deBruijnNewmanRiemannSiegelLineIntegrand N
        (heightTenRiemannSiegelCriticalPoint 17) v‖ := by
  unfold deBruijnNewmanRiemannSiegelLineIntegrand
    deBruijnNewmanRiemannSiegelKernel deBruijnNewmanRiemannSiegelNumerator
  simp only [norm_mul, norm_div]
  gcongr
  exact norm_cpow_heightTenRiemannSiegelCriticalPoint_le_seventeen_of_nonpos N hv hy

theorem norm_deBruijnNewmanRiemannSiegelRawIntegral_le_seventeenEndpointMasses
    (N : ℕ) {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 17) :
    ‖deBruijnNewmanRiemannSiegelRawIntegral N
        (heightTenRiemannSiegelCriticalPoint y)‖ ≤
      heightSeventeenRiemannSiegelNegativeEndpointMass N +
        heightTenRiemannSiegelPositiveEndpointMass N := by
  let f : ℝ → ℂ := deBruijnNewmanRiemannSiegelLineIntegrand N
    (heightTenRiemannSiegelCriticalPoint y)
  have hf : Integrable f :=
    integrable_deBruijnNewmanRiemannSiegelLineIntegrand N
      (heightTenRiemannSiegelCriticalPoint y)
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hf.integrableOn hf.integrableOn
  unfold deBruijnNewmanRiemannSiegelRawIntegral
  change ‖∫ v : ℝ, f v‖ ≤ _
  rw [← hsplit]
  calc
    ‖(∫ v in Set.Iic (0 : ℝ), f v) + (∫ v in Set.Ioi (0 : ℝ), f v)‖ ≤
        ‖∫ v in Set.Iic (0 : ℝ), f v‖ + ‖∫ v in Set.Ioi (0 : ℝ), f v‖ :=
      norm_add_le _ _
    _ ≤ heightSeventeenRiemannSiegelNegativeEndpointMass N +
          heightTenRiemannSiegelPositiveEndpointMass N := by
      apply add_le_add
      · apply MeasureTheory.norm_integral_le_of_norm_le
          (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N
            (heightTenRiemannSiegelCriticalPoint 17)).norm.integrableOn
        rw [ae_restrict_iff' measurableSet_Iic]
        filter_upwards with v hv
        exact norm_heightTenRiemannSiegelLineIntegrand_le_seventeen_of_nonpos
          N hv hy1
      · apply MeasureTheory.norm_integral_le_of_norm_le
          (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N
            (heightTenRiemannSiegelCriticalPoint (13 / 2))).norm.integrableOn
        rw [ae_restrict_iff' measurableSet_Ioi]
        filter_upwards with v hv
        exact norm_heightTenRiemannSiegelLineIntegrand_le_thirteenHalves_of_nonneg
          N hv.le hy0

theorem norm_heightSeventeenRiemannSiegelRawIntegral_one_le_threeFourths :
    ‖deBruijnNewmanRiemannSiegelRawIntegral 1
        (heightTenRiemannSiegelCriticalPoint 17)‖ ≤ 3 / 4 := by
  calc
    ‖deBruijnNewmanRiemannSiegelRawIntegral 1
        (heightTenRiemannSiegelCriticalPoint 17)‖ ≤
      heightSeventeenRiemannSiegelNegativeEndpointMass 1 +
        heightTenRiemannSiegelPositiveEndpointMass 1 :=
      norm_deBruijnNewmanRiemannSiegelRawIntegral_le_seventeenEndpointMasses
        1 (by norm_num) le_rfl
    _ ≤ 51 / 200 + 981 / 2000 := by
      exact add_le_add
        heightSeventeenRiemannSiegelNegativeEndpointMass_one_le_fiftyOneTwoHundredths
        heightTenRiemannSiegelPositiveEndpointMass_one_le_nineHundredEightyOneTwoThousandths
    _ ≤ 3 / 4 := by norm_num

theorem hardyXi_seventeen_neg :
    hardyXi 17 < 0 := by
  let s : ℂ := heightTenRiemannSiegelCriticalPoint 17
  have hsRe : s.re = 1 / 2 := by simp [s]
  have hsNoninteger : deBruijnNewmanRiemannSiegelIsNoninteger s := by
    simpa using
      (deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero
        (s := s) (by norm_num [s]) 0)
  have hpref :=
    heightSeventeenRiemannSiegelPrefactor_re_lt_neg_fourFifths_norm
  have hraw := norm_heightSeventeenRiemannSiegelRawIntegral_one_le_threeFourths
  have hrem :
      (deBruijnNewmanRiemannSiegelR0N 1 s).re ≤
        (3 / 4 : ℝ) * ‖deBruijnNewmanRiemannSiegelPrefactor s‖ := by
    calc
      (deBruijnNewmanRiemannSiegelR0N 1 s).re ≤
          |(deBruijnNewmanRiemannSiegelR0N 1 s).re| := le_abs_self _
      _ ≤ ‖deBruijnNewmanRiemannSiegelR0N 1 s‖ := Complex.abs_re_le_norm _
      _ = ‖deBruijnNewmanRiemannSiegelPrefactor s‖ *
          ‖deBruijnNewmanRiemannSiegelRawIntegral 1 s‖ := by
        rw [deBruijnNewmanRiemannSiegelR0N, norm_mul]
      _ ≤ ‖deBruijnNewmanRiemannSiegelPrefactor s‖ * (3 / 4) := by
        gcongr
      _ = (3 / 4 : ℝ) * ‖deBruijnNewmanRiemannSiegelPrefactor s‖ := by ring
  have hpref' :
      (deBruijnNewmanRiemannSiegelPrefactor s).re <
        -(4 / 5 : ℝ) * ‖deBruijnNewmanRiemannSiegelPrefactor s‖ := by
    simpa [s] using hpref
  have hsumNeg :
      (deBruijnNewmanRiemannSiegelPrefactor s +
        deBruijnNewmanRiemannSiegelR0N 1 s).re < 0 := by
    rw [Complex.add_re]
    nlinarith [norm_nonneg (deBruijnNewmanRiemannSiegelPrefactor s)]
  have hidentity :=
    riemannSiegel_criticalLine_one_eq_prefactor_remainder_re hsRe hsNoninteger
  have hsHardy : hardyCriticalLinePoint 17 = s := by
    apply Complex.ext <;> norm_num [hardyCriticalLinePoint, s,
      heightTenRiemannSiegelCriticalPoint]
  have hxiReal : (riemannXi s).re = hardyXi 17 := by
    rw [← hsHardy]
    rfl
  have hreal := congrArg Complex.re hidentity
  norm_num at hreal
  rw [hxiReal] at hreal
  have hscaled : (1 / 8 : ℝ) * hardyXi 17 < 0 := by
    rw [hreal]
    exact mul_neg_of_pos_of_neg (by norm_num) hsumNeg
  by_contra h
  have hnonneg : 0 ≤ hardyXi 17 := le_of_not_gt h
  have hscaledNonneg : 0 ≤ (1 / 8 : ℝ) * hardyXi 17 :=
    mul_nonneg (by norm_num) hnonneg
  exact (not_le_of_gt hscaled) hscaledNonneg

theorem hardyXiBracketsZero_ten_seventeen :
    HardyXiBracketsZero 10 17 := by
  right
  exact ⟨hardyXi_seventeen_neg.le, hardyXi_ten_pos.le⟩

/-- Six exact digamma shifts give a uniform rational upper bound on the residual interval. -/
theorem levinsonMontgomeryArchimedean_imaginaryAxis_lt_three_div_fiveHundred
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (_hy1 : y ≤ 7) :
    levinsonMontgomeryLogDerivArchimedeanTerm ((y : ℂ) * I) < 3 / 500 := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := s / 2 + 1
  let W : ℂ := w + 6
  have hwRe : w.re = 1 := by
    norm_num [w, s, div_re]
  have hWRe : W.re = 7 := by
    norm_num [W, w, s, div_re]
  have hWRePos : 0 < W.re := by rw [hWRe]; norm_num
  have hWNormSqComplex : 953 / 16 ≤ Complex.normSq W := by
    rw [Complex.normSq_apply]
    norm_num [W, w, s, div_re, div_im]
    nlinarith [sq_nonneg y]
  have hWNormSq : 953 / 16 ≤ ‖W‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hWNormSqComplex
  have hWNorm : 7717 / 1000 ≤ ‖W‖ := by
    have hnormNonneg : 0 ≤ ‖W‖ := norm_nonneg W
    nlinarith
  have hlogW : (2043 / 1000 : ℝ) < Real.log ‖W‖ := by
    exact
      log_sevenThousandSevenHundredSeventeen_div_oneThousand_gt_twoThousandFortyThree_div_oneThousand.trans_le
        (Real.log_le_log (by norm_num) hWNorm)
  have hlogPi : Real.log Real.pi < (229 / 200 : ℝ) :=
    log_pi_lt_twoHundredTwentyNine_div_twoHundred
  have hPoleDen : 173 / 4 ≤ Complex.normSq (s - 1) := by
    rw [Complex.normSq_apply]
    norm_num [s]
    nlinarith [sq_nonneg y]
  have hPoleDenPos : 0 < Complex.normSq (s - 1) :=
    lt_of_lt_of_le (by norm_num) hPoleDen
  have hPole : -(1 / (s - 1)).re ≤ 4 / 173 := by
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
  have hInvCorrection : (1 / (2 * W)).re / 2 ≤ 28 / 953 := by
    have hEq :
        (1 / (2 * W)).re / 2 = W.re / (4 * Complex.normSq W) := by
      rw [one_div, Complex.inv_re]
      norm_num [Complex.normSq_mul]
      ring
    rw [hEq, hWRe, div_le_iff₀ (mul_pos (by norm_num) hWNormSqPos)]
    nlinarith
  have hshiftNormSq (j : ℕ) :
      ((16 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) / 16 ≤
        Complex.normSq (w + j) := by
    rw [Complex.normSq_apply]
    norm_num [w, s, div_re, div_im]
    nlinarith [sq_nonneg y]
  have hshiftInv (j : ℕ) :
      (1 / (w + j)).re / 2 ≤
        (8 * ((j + 1 : ℕ) : ℝ)) /
          (16 * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) := by
    have hdenLower := hshiftNormSq j
    have hdenPos : 0 < Complex.normSq (w + j) := by
      have hbasePos :
          0 < ((16 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) / 16 := by positivity
      exact hbasePos.trans_le hdenLower
    have hEq :
        (1 / (w + j)).re / 2 =
          ((j + 1 : ℕ) : ℝ) / (2 * Complex.normSq (w + j)) := by
      rw [one_div, Complex.inv_re]
      have hre : (w + j).re = (j + 1 : ℕ) := by
        norm_num [hwRe]
        ring
      rw [hre]
      simp only [div_eq_mul_inv]
      ring
    rw [hEq]
    have hnat : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
    have hbasePos :
        (0 : ℝ) < 16 * ((j + 1 : ℕ) : ℝ) ^ 2 + 169 := by positivity
    calc
      ((j + 1 : ℕ) : ℝ) / (2 * Complex.normSq (w + j)) ≤
          ((j + 1 : ℕ) : ℝ) /
            (2 * (((16 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) / 16)) := by
        apply div_le_div_of_nonneg_left hnat
        · positivity
        · nlinarith
      _ = (8 * ((j + 1 : ℕ) : ℝ)) /
          (16 * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) := by
        field_simp
        ring
  have hInv0 : (1 / w).re / 2 ≤ 8 / 185 := by
    have h := hshiftInv 0
    norm_num [hwRe] at h ⊢
    exact h
  have hInv1 : (1 / (w + 1)).re / 2 ≤ 16 / 233 := by
    have h := hshiftInv 1
    norm_num [hwRe] at h ⊢
    exact h
  have hInv2 : (1 / (w + 2)).re / 2 ≤ 24 / 313 := by
    have h := hshiftInv 2
    norm_num [hwRe] at h ⊢
    exact h
  have hInv3 : (1 / (w + 3)).re / 2 ≤ 32 / 425 := by
    have h := hshiftInv 3
    norm_num [hwRe] at h ⊢
    exact h
  have hInv4 : (1 / (w + 4)).re / 2 ≤ 40 / 569 := by
    have h := hshiftInv 4
    norm_num [hwRe] at h ⊢
    exact h
  have hInv5 : (1 / (w + 5)).re / 2 ≤ 48 / 745 := by
    have h := hshiftInv 5
    norm_num [hwRe] at h ⊢
    exact h
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder W
  have hRnorm : ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) :=
    levinsonMontgomery_digamma_stirling_remainder_norm_le hWRePos
  have hRsmall : ‖R‖ ≤ 27 / 3812 := by
    calc
      ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) := hRnorm
      _ ≤ 27 / 3812 := by
        have hden : 0 < 64 * ‖W‖ ^ 2 := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
  have hRreal : -R.re / 2 ≤ 27 / 7624 := by
    have hre : -R.re ≤ ‖R‖ :=
      (neg_le_abs R.re).trans (Complex.abs_re_le_norm R)
    linarith
  have hregular : ∀ k : ℕ, k < 6 → ∀ m : ℕ, w + k ≠ -m := by
    intro k _hk m h
    have hre := congrArg Complex.re h
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num [hwRe] at hre
    linarith
  have hshift := digamma_eq_shift_nat_sub_sum w 6 hregular
  have hstirling := levinsonMontgomery_digamma_stirling hWRePos
  change Complex.digamma W = Complex.log W - 1 / (2 * W) + R at hstirling
  have hdigamma :
      Complex.digamma w = Complex.log W - 1 / (2 * W) + R -
        (1 / w + 1 / (w + 1) + 1 / (w + 2) +
          1 / (w + 3) + 1 / (w + 4) + 1 / (w + 5)) := by
    rw [show w + (6 : ℕ) = W by norm_num [W]] at hshift
    rw [hstirling] at hshift
    simpa [Finset.sum_range_succ] using hshift
  have hterm :
      levinsonMontgomeryLogDerivArchimedeanTerm s =
        -(1 / (s - 1)).re + Real.log Real.pi / 2 -
          Real.log ‖W‖ / 2 + (1 / (2 * W)).re / 2 - R.re / 2 +
          (1 / w).re / 2 + (1 / (w + 1)).re / 2 +
          (1 / (w + 2)).re / 2 + (1 / (w + 3)).re / 2 +
          (1 / (w + 4)).re / 2 + (1 / (w + 5)).re / 2 := by
    rw [levinsonMontgomeryLogDerivArchimedeanTerm,
      show s / 2 + 1 = w by rfl, hdigamma]
    simp only [Complex.add_re, Complex.sub_re, Complex.log_re]
    ring
  change levinsonMontgomeryLogDerivArchimedeanTerm s < 3 / 500
  rw [hterm]
  nlinarith

theorem log_oneThousandOneHundredNinetySix_div_oneHundredTwentyFive_gt_twoThousandTwoHundredFiftyEightOne_div_tenThousand :
    (22581 / 10000 : ℝ) < Real.log (1196 / 125) := by
  have hlog := abs_log_sub_binaryLogCenter_le
    (u := (1196 / 125 : ℝ)) (by norm_num) 3 6
  have hlower := (abs_le.mp hlog).1
  have hcenter :
      (22581 / 10000 : ℝ) <
        binaryLogCenter 3 6 (1196 / 125) -
          binaryLogError 3 6 (1196 / 125) := by
    norm_num [binaryLogCenter, binaryLogError, logAtanhPartial,
      Finset.sum_range_succ]
  linarith

/-- Eight exact digamma shifts sharpen the residual archimedean balance for a wider zero bracket. -/
theorem levinsonMontgomeryArchimedean_imaginaryAxis_lt_nine_div_twoThousand
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (_hy1 : y ≤ 7) :
    levinsonMontgomeryLogDerivArchimedeanTerm ((y : ℂ) * I) < 9 / 2000 := by
  let s : ℂ := (y : ℂ) * I
  let w : ℂ := s / 2 + 1
  let W : ℂ := w + 8
  have hwRe : w.re = 1 := by
    norm_num [w, s, div_re]
  have hWRe : W.re = 9 := by
    norm_num [W, w, s, div_re]
  have hWRePos : 0 < W.re := by rw [hWRe]; norm_num
  have hWNormSqComplex : 1465 / 16 ≤ Complex.normSq W := by
    rw [Complex.normSq_apply]
    norm_num [W, w, s, div_re, div_im]
    nlinarith [sq_nonneg y]
  have hWNormSq : 1465 / 16 ≤ ‖W‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact hWNormSqComplex
  have hWNorm : 1196 / 125 ≤ ‖W‖ := by
    have hnormNonneg : 0 ≤ ‖W‖ := norm_nonneg W
    nlinarith
  have hlogW : (22581 / 10000 : ℝ) < Real.log ‖W‖ := by
    exact
      log_oneThousandOneHundredNinetySix_div_oneHundredTwentyFive_gt_twoThousandTwoHundredFiftyEightOne_div_tenThousand.trans_le
        (Real.log_le_log (by norm_num) hWNorm)
  have hlogPi : Real.log Real.pi < (229 / 200 : ℝ) :=
    log_pi_lt_twoHundredTwentyNine_div_twoHundred
  have hPoleDen : 173 / 4 ≤ Complex.normSq (s - 1) := by
    rw [Complex.normSq_apply]
    norm_num [s]
    nlinarith [sq_nonneg y]
  have hPoleDenPos : 0 < Complex.normSq (s - 1) :=
    lt_of_lt_of_le (by norm_num) hPoleDen
  have hPole : -(1 / (s - 1)).re ≤ 4 / 173 := by
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
  have hInvCorrection : (1 / (2 * W)).re / 2 ≤ 36 / 1465 := by
    have hEq :
        (1 / (2 * W)).re / 2 = W.re / (4 * Complex.normSq W) := by
      rw [one_div, Complex.inv_re]
      norm_num [Complex.normSq_mul]
      ring
    rw [hEq, hWRe, div_le_iff₀ (mul_pos (by norm_num) hWNormSqPos)]
    nlinarith
  have hshiftNormSq (j : ℕ) :
      ((16 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) / 16 ≤
        Complex.normSq (w + j) := by
    rw [Complex.normSq_apply]
    norm_num [w, s, div_re, div_im]
    nlinarith [sq_nonneg y]
  have hshiftInv (j : ℕ) :
      (1 / (w + j)).re / 2 ≤
        (8 * ((j + 1 : ℕ) : ℝ)) /
          (16 * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) := by
    have hdenLower := hshiftNormSq j
    have hdenPos : 0 < Complex.normSq (w + j) := by
      have hbasePos :
          0 < ((16 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) / 16 := by
        positivity
      exact hbasePos.trans_le hdenLower
    have hEq :
        (1 / (w + j)).re / 2 =
          ((j + 1 : ℕ) : ℝ) / (2 * Complex.normSq (w + j)) := by
      rw [one_div, Complex.inv_re]
      have hre : (w + j).re = (j + 1 : ℕ) := by
        norm_num [hwRe]
        ring
      rw [hre]
      simp only [div_eq_mul_inv]
      ring
    rw [hEq]
    have hnat : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
    have hbasePos :
        (0 : ℝ) < 16 * ((j + 1 : ℕ) : ℝ) ^ 2 + 169 := by positivity
    calc
      ((j + 1 : ℕ) : ℝ) / (2 * Complex.normSq (w + j)) ≤
          ((j + 1 : ℕ) : ℝ) /
            (2 * (((16 : ℝ) * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) / 16)) := by
        apply div_le_div_of_nonneg_left hnat
        · positivity
        · nlinarith
      _ = (8 * ((j + 1 : ℕ) : ℝ)) /
          (16 * ((j + 1 : ℕ) : ℝ) ^ 2 + 169) := by
        field_simp
        ring
  have hInv0 : (1 / w).re / 2 ≤ 8 / 185 := by
    have h := hshiftInv 0
    norm_num [hwRe] at h ⊢
    exact h
  have hInv1 : (1 / (w + 1)).re / 2 ≤ 16 / 233 := by
    have h := hshiftInv 1
    norm_num [hwRe] at h ⊢
    exact h
  have hInv2 : (1 / (w + 2)).re / 2 ≤ 24 / 313 := by
    have h := hshiftInv 2
    norm_num [hwRe] at h ⊢
    exact h
  have hInv3 : (1 / (w + 3)).re / 2 ≤ 32 / 425 := by
    have h := hshiftInv 3
    norm_num [hwRe] at h ⊢
    exact h
  have hInv4 : (1 / (w + 4)).re / 2 ≤ 40 / 569 := by
    have h := hshiftInv 4
    norm_num [hwRe] at h ⊢
    exact h
  have hInv5 : (1 / (w + 5)).re / 2 ≤ 48 / 745 := by
    have h := hshiftInv 5
    norm_num [hwRe] at h ⊢
    exact h
  have hInv6 : (1 / (w + 6)).re / 2 ≤ 56 / 953 := by
    have h := hshiftInv 6
    norm_num [hwRe] at h ⊢
    exact h
  have hInv7 : (1 / (w + 7)).re / 2 ≤ 64 / 1193 := by
    have h := hshiftInv 7
    norm_num [hwRe] at h ⊢
    exact h
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder W
  have hRnorm : ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) :=
    levinsonMontgomery_digamma_stirling_remainder_norm_le hWRePos
  have hRsmall : ‖R‖ ≤ 27 / 5860 := by
    calc
      ‖R‖ ≤ 27 / (64 * ‖W‖ ^ 2) := hRnorm
      _ ≤ 27 / 5860 := by
        have hden : 0 < 64 * ‖W‖ ^ 2 := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
  have hRreal : -R.re / 2 ≤ 27 / 11720 := by
    have hre : -R.re ≤ ‖R‖ :=
      (neg_le_abs R.re).trans (Complex.abs_re_le_norm R)
    linarith
  have hregular : ∀ k : ℕ, k < 8 → ∀ m : ℕ, w + k ≠ -m := by
    intro k _hk m h
    have hre := congrArg Complex.re h
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num [hwRe] at hre
    linarith
  have hshift := digamma_eq_shift_nat_sub_sum w 8 hregular
  have hstirling := levinsonMontgomery_digamma_stirling hWRePos
  change Complex.digamma W = Complex.log W - 1 / (2 * W) + R at hstirling
  have hdigamma :
      Complex.digamma w = Complex.log W - 1 / (2 * W) + R -
        (1 / w + 1 / (w + 1) + 1 / (w + 2) + 1 / (w + 3) +
          1 / (w + 4) + 1 / (w + 5) + 1 / (w + 6) + 1 / (w + 7)) := by
    rw [show w + (8 : ℕ) = W by norm_num [W]] at hshift
    rw [hstirling] at hshift
    simpa [Finset.sum_range_succ] using hshift
  have hterm :
      levinsonMontgomeryLogDerivArchimedeanTerm s =
        -(1 / (s - 1)).re + Real.log Real.pi / 2 -
          Real.log ‖W‖ / 2 + (1 / (2 * W)).re / 2 - R.re / 2 +
          (1 / w).re / 2 + (1 / (w + 1)).re / 2 +
          (1 / (w + 2)).re / 2 + (1 / (w + 3)).re / 2 +
          (1 / (w + 4)).re / 2 + (1 / (w + 5)).re / 2 +
          (1 / (w + 6)).re / 2 + (1 / (w + 7)).re / 2 := by
    rw [levinsonMontgomeryLogDerivArchimedeanTerm,
      show s / 2 + 1 = w by rfl, hdigamma]
    simp only [Complex.add_re, Complex.sub_re, Complex.log_re]
    ring
  change levinsonMontgomeryLogDerivArchimedeanTerm s < 9 / 2000
  rw [hterm]
  nlinarith

theorem riemannXi_ne_zero_on_imaginaryAxis
    (y : ℝ) :
    riemannXi ((y : ℂ) * I) ≠ 0 := by
  intro hzero
  have hsNontrivial : IsNontrivialZero ((y : ℂ) * I) :=
    (isNontrivialZero_iff_riemannXi_eq_zero _).2 hzero
  have hsRePos := speiser_nontrivial_zero_re_pos hsNontrivial
  norm_num at hsRePos

theorem levinsonMontgomeryPairedReciprocalTerm_nonpos_on_imaginaryAxis
    (y : ℝ) (p : RiemannXiDivisorZeroIndex) :
    levinsonMontgomeryPairedReciprocalTerm ((y : ℂ) * I) p ≤ 0 := by
  let s : ℂ := (y : ℂ) * I
  have hsRe : s.re = 0 := by simp [s]
  have hxi : riemannXi s ≠ 0 := by
    simpa [s] using riemannXi_ne_zero_on_imaginaryAxis y
  have hpNe : s ≠ riemannXiDivisorZeroValue p := by
    intro hp
    apply hxi
    rw [hp]
    exact riemannXi_eq_zero_of_isNontrivialZero
      (riemannXiDivisorZeroIndex_val_isNontrivialZero p)
  have hpairNe : s ≠ riemannXiDivisorZeroValue
      (levinsonMontgomeryPairedZeroEquiv p) := by
    intro hp
    apply hxi
    rw [hp]
    exact riemannXi_eq_zero_of_isNontrivialZero
      (riemannXiDivisorZeroIndex_val_isNontrivialZero
        (levinsonMontgomeryPairedZeroEquiv p))
  rw [levinsonMontgomeryPairedReciprocalTerm_eq s p
    hpNe hpairNe]
  have hkernel := levinsonMontgomeryPairedKernel_nonneg_of_re_eq_zero hsRe hxi p
  rw [hsRe]
  norm_num
  linarith

theorem levinsonMontgomeryRealPairedZeroSum_le_selectedTerm_on_imaginaryAxis
    (y : ℝ) (p : RiemannXiDivisorZeroIndex) :
    levinsonMontgomeryRealPairedZeroSum ((y : ℂ) * I) ≤
      levinsonMontgomeryPairedReciprocalTerm ((y : ℂ) * I) p := by
  classical
  let s : ℂ := (y : ℂ) * I
  let f : RiemannXiDivisorZeroIndex → ℝ :=
    levinsonMontgomeryPairedReciprocalTerm s
  have hxi : riemannXi s ≠ 0 := by
    simpa [s] using riemannXi_ne_zero_on_imaginaryAxis y
  have hsum : Summable f := by
    simpa [f] using summable_levinsonMontgomeryPairedReciprocalTerm hxi
  have hrest : ∑' q, (if q = p then 0 else f q) ≤ 0 := by
    apply tsum_nonpos
    intro q
    split_ifs
    · rfl
    · simpa [f, s] using
        levinsonMontgomeryPairedReciprocalTerm_nonpos_on_imaginaryAxis y q
  rw [levinsonMontgomeryRealPairedZeroSum]
  change ∑' q, f q ≤ f p
  rw [hsum.tsum_eq_add_tsum_ite p]
  linarith

theorem levinsonMontgomeryPairedReciprocalTerm_le_neg_one_div_oneFortyFive_of_lowCriticalZero
    {y gamma : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7)
    (hgamma0 : 14 ≤ gamma) (hgamma1 : gamma ≤ 15)
    {p : RiemannXiDivisorZeroIndex}
    (hp : riemannXiDivisorZeroValue p = hardyCriticalLinePoint gamma) :
    levinsonMontgomeryPairedReciprocalTerm ((y : ℂ) * I) p ≤ -1 / 145 := by
  let s : ℂ := (y : ℂ) * I
  let rho : ℂ := hardyCriticalLinePoint gamma
  have hpair :
      riemannXiDivisorZeroValue (levinsonMontgomeryPairedZeroEquiv p) = rho := by
    rw [levinsonMontgomeryPairedZeroEquiv_val, hp]
    apply Complex.ext <;> norm_num [rho, hardyCriticalLinePoint]
  have hterm :
      levinsonMontgomeryPairedReciprocalTerm s p =
        -(1 / 2 : ℝ) / (1 / 4 + (y - gamma) ^ 2) := by
    rw [levinsonMontgomeryPairedReciprocalTerm, hp, hpair]
    simp only [rho]
    simp only [Complex.add_re, one_div, Complex.inv_re]
    norm_num [s, hardyCriticalLinePoint, Complex.normSq_apply]
    ring
  have hdiffLower : -(17 / 2 : ℝ) ≤ y - gamma := by linarith
  have hdiffUpper : y - gamma ≤ 17 / 2 := by linarith
  have hprod :
      0 ≤ (17 / 2 - (y - gamma)) * (17 / 2 + (y - gamma)) :=
    mul_nonneg (sub_nonneg.mpr hdiffUpper) (by linarith)
  have hdenUpper : 1 / 4 + (y - gamma) ^ 2 ≤ 145 / 2 := by
    nlinarith
  have hdenPos : 0 < 1 / 4 + (y - gamma) ^ 2 := by positivity
  rw [hterm, div_le_iff₀ hdenPos]
  nlinarith

theorem levinsonMontgomeryRealPairedZeroSum_le_neg_one_div_oneFortyFive_of_lowCriticalZero
    {y gamma : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7)
    (hgamma0 : 14 ≤ gamma) (hgamma1 : gamma ≤ 15)
    (hzero : IsNontrivialZero (hardyCriticalLinePoint gamma)) :
    levinsonMontgomeryRealPairedZeroSum ((y : ℂ) * I) ≤ -1 / 145 := by
  obtain ⟨p, hp⟩ :=
    exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hzero
  exact (levinsonMontgomeryRealPairedZeroSum_le_selectedTerm_on_imaginaryAxis y p).trans
    (levinsonMontgomeryPairedReciprocalTerm_le_neg_one_div_oneFortyFive_of_lowCriticalZero
      hy0 hy1 hgamma0 hgamma1 hp)

/-- One actual Hardy-xi sign bracket supplies enough paired mass to close the residual interval. -/
theorem speiserZetaDerivRatio_leftVertical_re_neg_thirteenHalves_seven_of_hardyXiBracket
    (hbracket : HardyXiBracketsZero 14 15)
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).re < 0 := by
  obtain ⟨gamma, hgamma, hzero, _hline⟩ :=
    exists_hardyXi_zero_of_bracket (by norm_num) hbracket
  have hyPos : 0 < y := by linarith
  have hzeta := riemannZeta_ne_zero_on_positive_imaginaryAxis hyPos
  have heq := levinsonMontgomery_equation_two_one_of_im_pos
    (s := (y : ℂ) * I) (by simpa using hyPos) hzeta
  have harch :=
    levinsonMontgomeryArchimedean_imaginaryAxis_lt_three_div_fiveHundred hy0 hy1
  have hmass :=
    levinsonMontgomeryRealPairedZeroSum_le_neg_one_div_oneFortyFive_of_lowCriticalZero
      hy0 hy1 hgamma.1 hgamma.2 hzero
  simpa only [speiserZetaDerivRatio, logDeriv_apply] using
    (show (logDeriv riemannZeta ((y : ℂ) * I)).re < 0 by
      rw [heq]
      nlinarith)

theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_thirteenHalves_seven_of_hardyXiBracket
    (hbracket : HardyXiBracketsZero 14 15)
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane := by
  have hneg :=
    speiserZetaDerivRatio_leftVertical_re_neg_thirteenHalves_seven_of_hardyXiBracket
      hbracket hy0 hy1
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num
  exact ne_of_lt hneg

theorem levinsonMontgomeryPairedReciprocalTerm_le_neg_one_div_twoHundredTwentyOne_of_lowCriticalZero
    {y gamma : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7)
    (hgamma0 : 10 ≤ gamma) (hgamma1 : gamma ≤ 17)
    {p : RiemannXiDivisorZeroIndex}
    (hp : riemannXiDivisorZeroValue p = hardyCriticalLinePoint gamma) :
    levinsonMontgomeryPairedReciprocalTerm ((y : ℂ) * I) p ≤ -1 / 221 := by
  let s : ℂ := (y : ℂ) * I
  let rho : ℂ := hardyCriticalLinePoint gamma
  have hpair :
      riemannXiDivisorZeroValue (levinsonMontgomeryPairedZeroEquiv p) = rho := by
    rw [levinsonMontgomeryPairedZeroEquiv_val, hp]
    apply Complex.ext <;> norm_num [rho, hardyCriticalLinePoint]
  have hterm :
      levinsonMontgomeryPairedReciprocalTerm s p =
        -(1 / 2 : ℝ) / (1 / 4 + (y - gamma) ^ 2) := by
    rw [levinsonMontgomeryPairedReciprocalTerm, hp, hpair]
    simp only [rho]
    simp only [Complex.add_re, one_div, Complex.inv_re]
    norm_num [s, hardyCriticalLinePoint, Complex.normSq_apply]
    ring
  have hdiffLower : -(21 / 2 : ℝ) ≤ y - gamma := by linarith
  have hdiffUpper : y - gamma ≤ 21 / 2 := by linarith
  have hprod :
      0 ≤ (21 / 2 - (y - gamma)) * (21 / 2 + (y - gamma)) :=
    mul_nonneg (sub_nonneg.mpr hdiffUpper) (by linarith)
  have hdenUpper : 1 / 4 + (y - gamma) ^ 2 ≤ 221 / 2 := by
    nlinarith
  have hdenPos : 0 < 1 / 4 + (y - gamma) ^ 2 := by positivity
  rw [hterm, div_le_iff₀ hdenPos]
  nlinarith

theorem levinsonMontgomeryRealPairedZeroSum_le_neg_one_div_twoHundredTwentyOne_of_lowCriticalZero
    {y gamma : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7)
    (hgamma0 : 10 ≤ gamma) (hgamma1 : gamma ≤ 17)
    (hzero : IsNontrivialZero (hardyCriticalLinePoint gamma)) :
    levinsonMontgomeryRealPairedZeroSum ((y : ℂ) * I) ≤ -1 / 221 := by
  obtain ⟨p, hp⟩ :=
    exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hzero
  exact (levinsonMontgomeryRealPairedZeroSum_le_selectedTerm_on_imaginaryAxis y p).trans
    (levinsonMontgomeryPairedReciprocalTerm_le_neg_one_div_twoHundredTwentyOne_of_lowCriticalZero
      hy0 hy1 hgamma0 hgamma1 hp)

/-- The actual `[10,17]` Hardy-xi bracket supplies enough paired mass on the residual interval. -/
theorem speiserZetaDerivRatio_leftVertical_re_neg_thirteenHalves_seven_lowZeroMass
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).re < 0 := by
  obtain ⟨gamma, hgamma, hzero, _hline⟩ :=
    exists_hardyXi_zero_of_bracket (by norm_num)
      hardyXiBracketsZero_ten_seventeen
  have hyPos : 0 < y := by linarith
  have hzeta := riemannZeta_ne_zero_on_positive_imaginaryAxis hyPos
  have heq := levinsonMontgomery_equation_two_one_of_im_pos
    (s := (y : ℂ) * I) (by simpa using hyPos) hzeta
  have harch :=
    levinsonMontgomeryArchimedean_imaginaryAxis_lt_nine_div_twoThousand hy0 hy1
  have hmass :=
    levinsonMontgomeryRealPairedZeroSum_le_neg_one_div_twoHundredTwentyOne_of_lowCriticalZero
      hy0 hy1 hgamma.1 hgamma.2 hzero
  simpa only [speiserZetaDerivRatio, logDeriv_apply] using
    (show (logDeriv riemannZeta ((y : ℂ) * I)).re < 0 by
      rw [heq]
      nlinarith)

theorem speiserZetaDerivRatio_leftVertical_rotated_mem_slitPlane_thirteenHalves_seven_lowZeroMass
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 7) :
    I * speiserZetaDerivRatio ((y : ℂ) * I) ∈ Complex.slitPlane := by
  have hneg :=
    speiserZetaDerivRatio_leftVertical_re_neg_thirteenHalves_seven_lowZeroMass
      hy0 hy1
  rw [Complex.mem_slitPlane_iff]
  right
  norm_num
  exact ne_of_lt hneg

end

end LeanLab.Riemann
