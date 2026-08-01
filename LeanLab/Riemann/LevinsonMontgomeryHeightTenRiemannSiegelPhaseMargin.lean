import LeanLab.Riemann.LevinsonMontgomeryHeightTenRiemannSiegelPhaseNorm
import LeanLab.Riemann.LevinsonMontgomeryTranscendentalInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option linter.style.header false

/-!
# Explicit prefactor phase margin for the height-ten Riemann--Siegel reduction

This module proves the open prefactor phase producer from the phase-aware norm reduction. It
derives an exact Stieltjes--Stirling factorization of the actual completed-zeta prefactor, traps
the shifted main phase by monotonicity and rational endpoint certificates, and absorbs the
Stieltjes logarithmic remainder using its rectangular `1/16` bound.
-/

open Complex Real Set

namespace LeanLab.Riemann

noncomputable section

def heightTenRiemannSiegelStirlingExponent (y : ℝ) : ℂ :=
  -(heightTenRiemannSiegelCriticalPoint y / 2) * (Real.log Real.pi : ℂ) +
    (heightTenRiemannSiegelCriticalPoint y / 2 - 1 / 2) *
      Complex.log (heightTenRiemannSiegelCriticalPoint y / 2) -
    heightTenRiemannSiegelCriticalPoint y / 2

def heightTenRiemannSiegelStirlingPhase (y : ℝ) : ℝ :=
  Real.pi + (heightTenRiemannSiegelStirlingExponent y).im

theorem heightTenRiemannSiegel_halfCritical_norm_sq (y : ℝ) :
    ‖heightTenRiemannSiegelCriticalPoint y / 2‖ ^ 2 =
      1 / 16 + y ^ 2 / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num [heightTenRiemannSiegelCriticalPoint, Complex.div_re, Complex.div_im]
  ring

theorem arg_heightTenRiemannSiegel_halfCritical (y : ℝ) :
    Complex.arg (heightTenRiemannSiegelCriticalPoint y / 2) =
      Real.arctan (2 * y) := by
  let z := heightTenRiemannSiegelCriticalPoint y / 2
  have hzRe : z.re = 1 / 4 := by
    norm_num [z, heightTenRiemannSiegelCriticalPoint, Complex.div_re]
  have hzRePos : 0 < z.re := by rw [hzRe]; norm_num
  have htan : Real.tan (Complex.arg z) = 2 * y := by
    rw [Complex.tan_arg]
    norm_num [z, heightTenRiemannSiegelCriticalPoint, Complex.div_re,
      Complex.div_im]
    ring_nf
  exact (Real.arctan_eq_of_tan_eq htan ⟨
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzRePos),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzRePos)⟩).symm

theorem heightTenRiemannSiegelStirlingPhase_eq (y : ℝ) :
    heightTenRiemannSiegelStirlingPhase y =
      Real.pi + y / 2 *
          (Real.log ‖heightTenRiemannSiegelCriticalPoint y / 2‖ -
            Real.log Real.pi - 1) -
        (1 / 4) * Real.arctan (2 * y) := by
  let z := heightTenRiemannSiegelCriticalPoint y / 2
  have hzRe : z.re = 1 / 4 := by
    norm_num [z, heightTenRiemannSiegelCriticalPoint, Complex.div_re]
  have hzIm : z.im = y / 2 := by
    norm_num [z, heightTenRiemannSiegelCriticalPoint, Complex.div_im]
  have harg : Complex.arg z = Real.arctan (2 * y) := by
    exact arg_heightTenRiemannSiegel_halfCritical y
  rw [heightTenRiemannSiegelStirlingPhase,
    heightTenRiemannSiegelStirlingExponent]
  change Real.pi +
      (-z * (Real.log Real.pi : ℂ) +
        (z - 1 / 2) * Complex.log z - z).im =
      Real.pi + y / 2 * (Real.log ‖z‖ - Real.log Real.pi - 1) -
        (1 / 4) * Real.arctan (2 * y)
  simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.neg_re,
    Complex.sub_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.log_re, Complex.log_im,
    hzRe, hzIm, harg]
  norm_num
  ring

def heightTenRiemannSiegelExplicitStirlingPhase (y : ℝ) : ℝ :=
  Real.pi + y / 4 * Real.log (1 / 16 + y ^ 2 / 4) -
    y / 2 * Real.log Real.pi - y / 2 -
    (1 / 4) * Real.arctan (2 * y)

theorem heightTenRiemannSiegelStirlingPhase_eq_explicit (y : ℝ) :
    heightTenRiemannSiegelStirlingPhase y =
      heightTenRiemannSiegelExplicitStirlingPhase y := by
  rw [heightTenRiemannSiegelStirlingPhase_eq]
  have hbase : 0 ≤ (1 / 16 : ℝ) + y ^ 2 / 4 := by positivity
  have hnorm :
      ‖heightTenRiemannSiegelCriticalPoint y / 2‖ =
        Real.sqrt (1 / 16 + y ^ 2 / 4) := by
    rw [Complex.norm_def]
    congr 1
    have hsq := heightTenRiemannSiegel_halfCritical_norm_sq y
    rwa [Complex.sq_norm] at hsq
  rw [hnorm, Real.log_sqrt hbase]
  unfold heightTenRiemannSiegelExplicitStirlingPhase
  ring

theorem log_eightyFive_div_eight_gt_fiftyNine_div_twentyFive :
    (59 / 25 : ℝ) < Real.log (85 / 8) := by
  have h := abs_log_sub_binaryLogCenter_le
    (u := (85 / 8 : ℝ)) (by norm_num) 3 5
  have hlower := (abs_le.mp h).1
  have hcert :
      (59 / 25 : ℝ) <
        binaryLogCenter 3 5 (85 / 8) -
          binaryLogError 3 5 (85 / 8) := by
    norm_num [binaryLogCenter, binaryLogError, logAtanhPartial,
      Finset.sum_range_succ]
  linarith

theorem heightTenRiemannSiegelExplicitStirlingPhase_hasDerivAt (y : ℝ) :
    HasDerivAt heightTenRiemannSiegelExplicitStirlingPhase
      ((1 / 4) * Real.log (1 / 16 + y ^ 2 / 4) -
        (1 / 2) * Real.log Real.pi -
        1 / (1 + 4 * y ^ 2)) y := by
  have hbasePos : 0 < (1 / 16 : ℝ) + y ^ 2 / 4 := by positivity
  have hbase : HasDerivAt
      (fun x : ℝ => (1 / 16 : ℝ) + x ^ 2 / 4) (2 * y / 4) y := by
    simpa [div_eq_mul_inv] using
      (((hasDerivAt_id y).pow 2).div_const 4 |>.const_add (1 / 16 : ℝ))
  have hlog := hbase.log hbasePos.ne'
  have harctan := Real.hasDerivAt_arctan (2 * y) |>.comp y
    ((hasDerivAt_const y (2 : ℝ)).mul (hasDerivAt_id y))
  have hraw := (((((hasDerivAt_const y Real.pi).add
      ((hasDerivAt_id y).div_const 4 |>.mul hlog)).sub
      (((hasDerivAt_id y).div_const 2).mul_const (Real.log Real.pi))).sub
      ((hasDerivAt_id y).div_const 2)).sub
      (harctan.const_mul (1 / 4)))
  change HasDerivAt heightTenRiemannSiegelExplicitStirlingPhase _ y at hraw
  simp only [id_eq] at hraw
  convert hraw using 1
  field_simp [hbasePos.ne']
  ring

theorem heightTenRiemannSiegelExplicitStirlingPhase_deriv_pos
    {y : ℝ} (hy : 13 / 2 ≤ y) :
    0 < deriv heightTenRiemannSiegelExplicitStirlingPhase y := by
  rw [(heightTenRiemannSiegelExplicitStirlingPhase_hasDerivAt y).deriv]
  have hy0 : 0 ≤ y := by linarith
  have hySq : (13 / 2 : ℝ) ^ 2 ≤ y ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 13 / 2) hy
  have hbase : (85 / 8 : ℝ) ≤ 1 / 16 + y ^ 2 / 4 := by
    nlinarith
  have hlogMono : Real.log (85 / 8) ≤ Real.log (1 / 16 + y ^ 2 / 4) :=
    Real.log_le_log (by norm_num) hbase
  have hlog : (59 / 25 : ℝ) < Real.log (1 / 16 + y ^ 2 / 4) :=
    log_eightyFive_div_eight_gt_fiftyNine_div_twentyFive.trans_le hlogMono
  have hden : (170 : ℝ) ≤ 1 + 4 * y ^ 2 := by nlinarith
  have hdenPos : 0 < 1 + 4 * y ^ 2 := by positivity
  have hinv : 1 / (1 + 4 * y ^ 2) ≤ (1 / 170 : ℝ) := by
    rw [div_le_div_iff₀ hdenPos (by norm_num : (0 : ℝ) < 170)]
    nlinarith
  have hpi := log_pi_lt_twoHundredTwentyNine_div_twoHundred
  nlinarith

theorem heightTenRiemannSiegelExplicitStirlingPhase_strictMonoOn :
    StrictMonoOn heightTenRiemannSiegelExplicitStirlingPhase (Ici (13 / 2)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (13 / 2))
  · intro y hy
    exact (heightTenRiemannSiegelExplicitStirlingPhase_hasDerivAt y).continuousAt.continuousWithinAt
  · intro y hy
    apply heightTenRiemannSiegelExplicitStirlingPhase_deriv_pos
    rw [interior_Ici] at hy
    exact hy.le

theorem heightTenRiemannSiegelStirlingPhase_eq_inverseArctan
    {y : ℝ} (hy : 0 < y) :
    heightTenRiemannSiegelStirlingPhase y =
      7 * Real.pi / 8 + y / 2 *
          (Real.log
            (‖heightTenRiemannSiegelCriticalPoint y / 2‖ / Real.pi) - 1) +
        (1 / 4) * Real.arctan (1 / (2 * y)) := by
  rw [heightTenRiemannSiegelStirlingPhase_eq]
  have hnormPos : 0 < ‖heightTenRiemannSiegelCriticalPoint y / 2‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num [heightTenRiemannSiegelCriticalPoint, Complex.div_im] at him
    exact hy.ne' him
  have hlog :
      Real.log ‖heightTenRiemannSiegelCriticalPoint y / 2‖ - Real.log Real.pi =
        Real.log (‖heightTenRiemannSiegelCriticalPoint y / 2‖ / Real.pi) := by
    exact (Real.log_div hnormPos.ne' Real.pi_ne_zero).symm
  have hargInv := Real.arctan_inv_of_pos (show 0 < 2 * y by positivity)
  have harg :
      Real.arctan (2 * y) = Real.pi / 2 - Real.arctan (1 / (2 * y)) := by
    rw [show (2 * y)⁻¹ = 1 / (2 * y) by rw [one_div]] at hargInv
    linarith
  rw [hlog, harg]
  ring

theorem log_eight_div_five_lt_fourHundredSeventyOne_div_oneThousand :
    Real.log (8 / 5) < (471 / 1000 : ℝ) := by
  have h := abs_log_div_sub_logAtanhPartial_le
    (a := (8 : ℝ)) (b := (5 : ℝ)) (by norm_num) (by norm_num) 4
  have hupper := (abs_le.mp h).2
  have hcert :
      logAtanhPartial 4 ((8 - 5 : ℝ) / (8 + 5)) +
          2 * (|((8 - 5 : ℝ) / (8 + 5))| ^ (2 * 4 + 1) /
            (1 - ((8 - 5 : ℝ) / (8 + 5)) ^ 2)) <
        (471 / 1000 : ℝ) := by
    norm_num [logAtanhPartial, Finset.sum_range_succ]
  norm_num only at hupper
  linarith

theorem arctan_one_div_thirteen_ge_thirteen_div_oneHundredSeventy :
    (13 / 170 : ℝ) ≤ Real.arctan (1 / 13) := by
  have hangle0 : 0 ≤ Real.arctan (1 / 13 : ℝ) :=
    Real.arctan_nonneg.mpr (by norm_num)
  have hsin := Real.sin_le hangle0
  rw [Real.sin_arctan] at hsin
  have hsqrtPos : 0 < Real.sqrt (1 + (1 / 13 : ℝ) ^ 2) := by positivity
  have hsqrtUpper :
      Real.sqrt (1 + (1 / 13 : ℝ) ^ 2) ≤ 170 / 169 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hlower :
      (13 / 170 : ℝ) ≤
        (1 / 13) / Real.sqrt (1 + (1 / 13 : ℝ) ^ 2) := by
    rw [le_div_iff₀ hsqrtPos]
    calc
      (13 / 170 : ℝ) * Real.sqrt (1 + (1 / 13 : ℝ) ^ 2) ≤
          (13 / 170) * (170 / 169) := by gcongr
      _ = 1 / 13 := by norm_num
  exact hlower.trans hsin

theorem heightTenRiemannSiegel_halfCriticalRatio_lowerEndpoint :
    (250 / 241 : ℝ) ≤
      ‖heightTenRiemannSiegelCriticalPoint (13 / 2) / 2‖ / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos]
  apply (sq_le_sq₀ (by positivity)
    (norm_nonneg (heightTenRiemannSiegelCriticalPoint (13 / 2) / 2))).mp
  have hnormSq :
      ‖heightTenRiemannSiegelCriticalPoint (13 / 2) / 2‖ ^ 2 = 85 / 8 := by
    calc
      _ = 1 / 16 + (13 / 2 : ℝ) ^ 2 / 4 :=
        heightTenRiemannSiegel_halfCritical_norm_sq (13 / 2)
      _ = 85 / 8 := by norm_num
  have hpi := pi_lt_threeThousandOneHundredFortyTwo_div_oneThousand
  have hpiSq : Real.pi ^ 2 < (1571 / 500 : ℝ) ^ 2 := by
    simpa [pow_two] using
      mul_self_lt_mul_self Real.pi_pos.le (by norm_num at hpi ⊢; exact hpi)
  rw [hnormSq]
  nlinarith

theorem heightTenRiemannSiegel_halfCriticalRatio_upperEndpoint :
    ‖heightTenRiemannSiegelCriticalPoint 10 / 2‖ / Real.pi ≤ (8 / 5 : ℝ) := by
  rw [div_le_iff₀ Real.pi_pos]
  apply (sq_le_sq₀
    (norm_nonneg (heightTenRiemannSiegelCriticalPoint 10 / 2)) (by positivity)).mp
  have hnormSq :
      ‖heightTenRiemannSiegelCriticalPoint 10 / 2‖ ^ 2 = 401 / 16 := by
    calc
      _ = 1 / 16 + (10 : ℝ) ^ 2 / 4 :=
        heightTenRiemannSiegel_halfCritical_norm_sq 10
      _ = 401 / 16 := by norm_num
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    convert Real.pi_gt_d2 using 1
    norm_num
  have hpiSq : (157 / 50 : ℝ) ^ 2 < Real.pi ^ 2 := by
    simpa [pow_two] using mul_self_lt_mul_self (by norm_num) hpi
  rw [hnormSq]
  nlinarith

theorem heightTenRiemannSiegel_lowerEndpoint_logRatio :
    (9 / 250 : ℝ) ≤
      Real.log
        (‖heightTenRiemannSiegelCriticalPoint (13 / 2) / 2‖ / Real.pi) := by
  let x : ℝ := ‖heightTenRiemannSiegelCriticalPoint (13 / 2) / 2‖ / Real.pi
  have hxPos : 0 < x := by
    dsimp [x]
    have hnormSq :
        ‖heightTenRiemannSiegelCriticalPoint (13 / 2) / 2‖ ^ 2 = 85 / 8 := by
      calc
        _ = 1 / 16 + (13 / 2 : ℝ) ^ 2 / 4 :=
          heightTenRiemannSiegel_halfCritical_norm_sq (13 / 2)
        _ = 85 / 8 := by norm_num
    have hnormPos :
        0 < ‖heightTenRiemannSiegelCriticalPoint (13 / 2) / 2‖ := by
      nlinarith [norm_nonneg (heightTenRiemannSiegelCriticalPoint (13 / 2) / 2)]
    exact div_pos hnormPos Real.pi_pos
  have hx : (250 / 241 : ℝ) ≤ x := by
    exact heightTenRiemannSiegel_halfCriticalRatio_lowerEndpoint
  have hinv : x⁻¹ ≤ ((250 / 241 : ℝ))⁻¹ :=
    (inv_le_inv₀ hxPos (by norm_num)).2 hx
  have hlog := Real.one_sub_inv_le_log_of_pos hxPos
  norm_num at hinv
  dsimp [x] at hlog ⊢
  nlinarith

theorem heightTenRiemannSiegel_upperEndpoint_logRatio :
    Real.log (‖heightTenRiemannSiegelCriticalPoint 10 / 2‖ / Real.pi) <
      (471 / 1000 : ℝ) := by
  have hxPos : 0 < ‖heightTenRiemannSiegelCriticalPoint 10 / 2‖ / Real.pi := by
    have hnormSq :
        ‖heightTenRiemannSiegelCriticalPoint 10 / 2‖ ^ 2 = 401 / 16 := by
      calc
        _ = 1 / 16 + (10 : ℝ) ^ 2 / 4 :=
          heightTenRiemannSiegel_halfCritical_norm_sq 10
        _ = 401 / 16 := by norm_num
    have hnormPos : 0 < ‖heightTenRiemannSiegelCriticalPoint 10 / 2‖ := by
      nlinarith [norm_nonneg (heightTenRiemannSiegelCriticalPoint 10 / 2)]
    exact div_pos hnormPos Real.pi_pos
  have hmono := Real.log_le_log hxPos
    heightTenRiemannSiegel_halfCriticalRatio_upperEndpoint
  exact hmono.trans_lt log_eight_div_five_lt_fourHundredSeventyOne_div_oneThousand

theorem heightTenRiemannSiegelStirlingPhase_lowerEndpoint :
    (-3 / 8 : ℝ) < heightTenRiemannSiegelStirlingPhase (13 / 2) := by
  rw [heightTenRiemannSiegelStirlingPhase_eq_inverseArctan (by norm_num)]
  have hpi : (157 / 50 : ℝ) < Real.pi := by
    convert Real.pi_gt_d2 using 1
    norm_num
  have hlog := heightTenRiemannSiegel_lowerEndpoint_logRatio
  have harg := arctan_one_div_thirteen_ge_thirteen_div_oneHundredSeventy
  norm_num only at hlog harg ⊢
  nlinarith

theorem heightTenRiemannSiegelStirlingPhase_upperEndpoint :
    heightTenRiemannSiegelStirlingPhase 10 < (1 / 8 : ℝ) := by
  rw [heightTenRiemannSiegelStirlingPhase_eq_inverseArctan (by norm_num)]
  have hpi := pi_lt_threeThousandOneHundredFortyTwo_div_oneThousand
  have hlog := heightTenRiemannSiegel_upperEndpoint_logRatio
  have harg : Real.arctan (1 / 20 : ℝ) ≤ 1 / 20 :=
    arctan_le_self_of_nonneg (by norm_num)
  norm_num only at hpi hlog harg ⊢
  nlinarith

theorem heightTenRiemannSiegelStirlingPhase_mem
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    (-3 / 8 : ℝ) < heightTenRiemannSiegelStirlingPhase y ∧
      heightTenRiemannSiegelStirlingPhase y < 1 / 8 := by
  have hloExplicit :
      heightTenRiemannSiegelExplicitStirlingPhase (13 / 2) ≤
        heightTenRiemannSiegelExplicitStirlingPhase y := by
    exact heightTenRiemannSiegelExplicitStirlingPhase_strictMonoOn.monotoneOn
      (by simp) hy0 hy0
  have hhiExplicit :
      heightTenRiemannSiegelExplicitStirlingPhase y ≤
        heightTenRiemannSiegelExplicitStirlingPhase 10 := by
    exact heightTenRiemannSiegelExplicitStirlingPhase_strictMonoOn.monotoneOn
      hy0 (by norm_num : (13 / 2 : ℝ) ≤ 10) hy1
  rw [← heightTenRiemannSiegelStirlingPhase_eq_explicit (13 / 2),
    ← heightTenRiemannSiegelStirlingPhase_eq_explicit y] at hloExplicit
  rw [← heightTenRiemannSiegelStirlingPhase_eq_explicit y,
    ← heightTenRiemannSiegelStirlingPhase_eq_explicit 10] at hhiExplicit
  exact ⟨heightTenRiemannSiegelStirlingPhase_lowerEndpoint.trans_le hloExplicit,
    hhiExplicit.trans_lt heightTenRiemannSiegelStirlingPhase_upperEndpoint⟩

def heightTenRiemannSiegelPrefactorScale (y : ℝ) : ℝ :=
  (y ^ 2 + 1 / 4) / 16 * Real.sqrt (2 * Real.pi)

theorem heightTenRiemannSiegelCriticalPoint_mul_sub_one (y : ℝ) :
    heightTenRiemannSiegelCriticalPoint y *
        (heightTenRiemannSiegelCriticalPoint y - 1) =
      (-((y ^ 2 + 1 / 4 : ℝ) : ℂ)) := by
  apply Complex.ext <;>
    simp [heightTenRiemannSiegelCriticalPoint, pow_two, Complex.mul_re,
      Complex.mul_im] <;> ring

theorem heightTenRiemannSiegelPrefactor_eq_phaseExponential (y : ℝ) :
    deBruijnNewmanRiemannSiegelPrefactor
        (heightTenRiemannSiegelCriticalPoint y) =
      -(heightTenRiemannSiegelPrefactorScale y : ℂ) *
        Complex.exp
          (heightTenRiemannSiegelStirlingExponent y +
            deBruijnNewmanPolymathStieltjesLogRemainder
              (heightTenRiemannSiegelCriticalPoint y / 2)) := by
  let s := heightTenRiemannSiegelCriticalPoint y
  let z := s / 2
  let L := deBruijnNewmanPolymathStieltjesLogRemainder z
  have hzRe : z.re = 1 / 4 := by
    norm_num [z, s, heightTenRiemannSiegelCriticalPoint, Complex.div_re]
  have hzRePos : 0 < z.re := by rw [hzRe]; norm_num
  have hscaled := deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes hzRePos
  change Complex.Gamma z / deBruijnNewmanPolymathGammaStirlingMain z =
    Complex.exp L at hscaled
  have hmainNe := deBruijnNewmanPolymathGammaStirlingMain_ne_zero z
  have hgamma :
      Complex.Gamma z =
        deBruijnNewmanPolymathGammaStirlingMain z * Complex.exp L := by
    apply (div_eq_iff hmainNe).mp at hscaled
    simpa [mul_comm] using hscaled
  have hpiC : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hexponent :
      heightTenRiemannSiegelStirlingExponent y =
        -(heightTenRiemannSiegelCriticalPoint y / 2) *
            (Real.log Real.pi : ℂ) +
          ((heightTenRiemannSiegelCriticalPoint y / 2 - 1 / 2) *
              Complex.log (heightTenRiemannSiegelCriticalPoint y / 2) -
            heightTenRiemannSiegelCriticalPoint y / 2) := by
    unfold heightTenRiemannSiegelStirlingExponent
    ring
  rw [deBruijnNewmanRiemannSiegelPrefactor]
  change (1 / 8 : ℂ) * (s * (s - 1) / 2) *
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma z = _
  rw [hgamma, deBruijnNewmanPolymathGammaStirlingMain,
    Complex.cpow_def_of_ne_zero hpiC]
  rw [← Complex.ofReal_log Real.pi_pos.le]
  dsimp [s, z, L]
  rw [heightTenRiemannSiegelCriticalPoint_mul_sub_one]
  unfold heightTenRiemannSiegelPrefactorScale
  rw [hexponent, Complex.exp_add, Complex.exp_add]
  have hexpPi :
      Complex.exp
          ((Real.log Real.pi : ℂ) *
            (-heightTenRiemannSiegelCriticalPoint y / 2)) =
        Complex.exp
          (-(heightTenRiemannSiegelCriticalPoint y / 2) *
            (Real.log Real.pi : ℂ)) := by
    congr 1
    ring
  rw [hexpPi]
  push_cast
  ring

theorem abs_heightTenRiemannSiegel_totalShiftedPhase_lt_sevenSixteenths
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    |Real.pi +
        (heightTenRiemannSiegelStirlingExponent y +
          deBruijnNewmanPolymathStieltjesLogRemainder
            (heightTenRiemannSiegelCriticalPoint y / 2)).im| < 7 / 16 := by
  have hphase := heightTenRiemannSiegelStirlingPhase_mem hy0 hy1
  let L := deBruijnNewmanPolymathStieltjesLogRemainder
    (heightTenRiemannSiegelCriticalPoint y / 2)
  have hLnorm : ‖L‖ ≤ 1 / 16 := by
    exact norm_heightTenStieltjesLogRemainder_halfCritical_le_oneSixteenth hy0
  have hLimAbs : |L.im| ≤ 1 / 16 :=
    (Complex.abs_im_le_norm L).trans hLnorm
  have hLim := abs_le.mp hLimAbs
  rw [Complex.add_im]
  rw [abs_lt]
  simp only [← add_assoc]
  change
    -(7 / 16 : ℝ) < heightTenRiemannSiegelStirlingPhase y + L.im ∧
      heightTenRiemannSiegelStirlingPhase y + L.im < 7 / 16
  constructor <;> linarith

theorem heightTenRiemannSiegel_totalExponent_cos_abs_gt_nineTenths
    {y : ℝ} (hy0 : 13 / 2 ≤ y) (hy1 : y ≤ 10) :
    (9 / 10 : ℝ) <
      |Real.cos
        (heightTenRiemannSiegelStirlingExponent y +
          deBruijnNewmanPolymathStieltjesLogRemainder
            (heightTenRiemannSiegelCriticalPoint y / 2)).im| := by
  let W := heightTenRiemannSiegelStirlingExponent y +
    deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint y / 2)
  let theta := Real.pi + W.im
  have htheta : |theta| < 7 / 16 := by
    exact abs_heightTenRiemannSiegel_totalShiftedPhase_lt_sevenSixteenths hy0 hy1
  have hthetaSq : theta ^ 2 < (7 / 16 : ℝ) ^ 2 := by
    simpa [pow_two, sq_abs] using
      mul_self_lt_mul_self (abs_nonneg theta) htheta
  have hcosLower := Real.one_sub_sq_div_two_le_cos (x := theta)
  have hcos : (9 / 10 : ℝ) < Real.cos theta := by
    nlinarith
  have hcosShift : Real.cos theta = -Real.cos W.im := by
    dsimp [theta]
    rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
    ring
  calc
    (9 / 10 : ℝ) < Real.cos theta := hcos
    _ ≤ |Real.cos theta| := le_abs_self _
    _ = |Real.cos W.im| := by rw [hcosShift, abs_neg]

theorem heightTenRiemannSiegelOnePrefactorPhaseMargin :
    HeightTenRiemannSiegelOnePrefactorPhaseMargin := by
  intro y hy0 hy1
  let c := heightTenRiemannSiegelPrefactorScale y
  let W := heightTenRiemannSiegelStirlingExponent y +
    deBruijnNewmanPolymathStieltjesLogRemainder
      (heightTenRiemannSiegelCriticalPoint y / 2)
  have hcPos : 0 < c := by
    dsimp [c, heightTenRiemannSiegelPrefactorScale]
    have hyPos : 0 < y := by linarith
    positivity
  have hcos : (9 / 10 : ℝ) < |Real.cos W.im| := by
    exact heightTenRiemannSiegel_totalExponent_cos_abs_gt_nineTenths hy0 hy1
  have hpref := heightTenRiemannSiegelPrefactor_eq_phaseExponential y
  change (9 / 10 : ℝ) *
      ‖deBruijnNewmanRiemannSiegelPrefactor
        (heightTenRiemannSiegelCriticalPoint y)‖ <
    |(deBruijnNewmanRiemannSiegelPrefactor
      (heightTenRiemannSiegelCriticalPoint y)).re|
  rw [hpref]
  have hnorm : ‖-(c : ℂ) * Complex.exp W‖ = c * Real.exp W.re := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcPos, Complex.norm_exp]
  have hre : |(-(c : ℂ) * Complex.exp W).re| =
      c * Real.exp W.re * |Real.cos W.im| := by
    rw [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re]
    simp only [neg_zero, zero_mul, sub_zero, abs_mul, abs_neg,
      abs_of_pos hcPos, abs_of_pos (Real.exp_pos _)]
    ring
  rw [hnorm, hre]
  calc
    (9 / 10 : ℝ) * (c * Real.exp W.re) <
        |Real.cos W.im| * (c * Real.exp W.re) :=
      mul_lt_mul_of_pos_right hcos (mul_pos hcPos (Real.exp_pos _))
    _ = c * Real.exp W.re * |Real.cos W.im| := by ring

end

end LeanLab.Riemann
