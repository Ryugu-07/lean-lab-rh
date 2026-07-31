import LeanLab.Riemann.LevinsonMontgomeryHeightTenFiniteEvaluator
import Mathlib.Analysis.Real.Pi.Leibniz

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Actual zeta sign at the height-ten critical endpoint

This module combines the kernel-checked thirty-term Euler--Maclaurin centers with explicit
analytic remainder and archimedean bounds.  All transcendental inequalities are reduced to
rationally checked logarithm or arctangent enclosures.
-/

open Complex Filter Finset Real
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

private theorem antitone_arctanTerm (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Antitone (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1)) := by
  intro a b hab
  have hpow : x ^ (2 * b + 1) ≤ x ^ (2 * a + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1 (by omega)
  have hden : (2 : ℝ) * a + 1 ≤ (2 : ℝ) * b + 1 := by
    exact_mod_cast (show 2 * a + 1 ≤ 2 * b + 1 by omega)
  exact div_le_div₀ (pow_nonneg hx0 _) hpow (by positivity) hden

private theorem arctan_le_firstTerm {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.arctan x ≤ x := by
  have hsum :
      Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))) atTop
        (nhds (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0])).tendsto_sum_nat
  have hanti := antitone_arctanTerm x hx0 hx1.le
  have hupper := hanti.tendsto_le_alternating_series hsum 0
  norm_num at hupper
  simpa using hupper

private theorem firstTwoTerms_le_arctan {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hsum :
      Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))) atTop
        (nhds (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0])).tendsto_sum_nat
  have hanti := antitone_arctanTerm x hx0 hx1.le
  have hlower := hanti.alternating_series_le_tendsto hsum 1
  norm_num [Finset.sum_range_succ] at hlower
  simpa [pow_three] using hlower

private theorem arctan_le_firstThreeTerms {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hsum :
      Tendsto (fun n => ∑ i ∈ range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))) atTop
        (nhds (Real.arctan x)) := by
    simpa only [div_eq_mul_inv, mul_assoc, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] using
      (Real.hasSum_arctan (x := x)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hx0])).tendsto_sum_nat
  have hanti := antitone_arctanTerm x hx0 hx1.le
  have hupper := hanti.tendsto_le_alternating_series hsum 1
  norm_num [Finset.sum_range_succ] at hupper
  simpa only [sub_eq_add_neg] using hupper

theorem pi_lt_threeThousandOneHundredFortyTwo_div_oneThousand :
    Real.pi < (3142 / 1000 : ℝ) := by
  have hmachin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hfive := arctan_le_firstThreeTerms (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num)
  have h239 := firstTwoTerms_le_arctan (x := (1 / 239 : ℝ)) (by norm_num) (by norm_num)
  rw [show Real.pi = 4 * (4 * Real.arctan (5 : ℝ)⁻¹ - Real.arctan (239 : ℝ)⁻¹) by
    linarith] 
  norm_num at hfive h239 ⊢
  calc
    4 * (4 * Real.arctan (1 / 5) - Real.arctan (1 / 239)) ≤
        4 * (4 * (9253 / 46875 : ℝ) - 171362 / 40955757) := by linarith
    _ < 1571 / 500 := by norm_num

theorem log_pi_lt_twoHundredTwentyNine_div_twoHundred :
    Real.log Real.pi < (229 / 200 : ℝ) := by
  have hpi := pi_lt_threeThousandOneHundredFortyTwo_div_oneThousand
  have hmono := Real.log_lt_log Real.pi_pos hpi
  have hlog := abs_log_div_sub_logAtanhPartial_le
    (a := (1571 : ℝ)) (b := (500 : ℝ)) (by norm_num) (by norm_num) 8
  have hupper := (abs_le.mp hlog).2
  have hcenter :
      logAtanhPartial 8 ((1571 - 500 : ℝ) / (1571 + 500)) +
          2 * (|((1571 - 500 : ℝ) / (1571 + 500))| ^ (2 * 8 + 1) /
            (1 - ((1571 - 500 : ℝ) / (1571 + 500)) ^ 2)) <
        (229 / 200 : ℝ) := by
    norm_num [logAtanhPartial, Finset.sum_range_succ]
  norm_num only at hupper
  linarith

theorem log_fourHundredTwentyFive_div_sixteen_gt_threeThousandTwoHundredSeventyEight_div_oneThousand :
    (3278 / 1000 : ℝ) < Real.log (425 / 16) := by
  have hlog := abs_log_sub_binaryLogCenter_le
    (u := (425 / 16 : ℝ)) (by norm_num) 5 10
  have hlower := (abs_le.mp hlog).1
  have hcenter :
      (3278 / 1000 : ℝ) <
        binaryLogCenter 5 10 (425 / 16) - binaryLogError 5 10 (425 / 16) := by
    norm_num [binaryLogCenter, binaryLogError, logAtanhPartial,
      Finset.sum_range_succ]
  linarith

def heightTenEndpoint : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I

theorem heightTenEndpoint_one_sub :
    1 - heightTenEndpoint = heightTenReflectedEndpoint := by
  apply Complex.ext <;>
    norm_num [heightTenEndpoint, heightTenReflectedEndpoint]

theorem heightTen_log_norm_lower :
    (1639 / 1000 : ℝ) < Real.log ‖heightTenEndpoint / 2 + 1‖ := by
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
  have hlog :=
    log_fourHundredTwentyFive_div_sixteen_gt_threeThousandTwoHundredSeventyEight_div_oneThousand
  rw [show Complex.normSq (heightTenEndpoint / 2 + 1) = (425 / 16 : ℝ) by
    norm_num [heightTenEndpoint, Complex.normSq_apply, Complex.div_re,
      Complex.div_im]]
  linarith

theorem heightTen_reflected_log_norm_lower :
    (1639 / 1000 : ℝ) <
      Real.log ‖heightTenReflectedEndpoint / 2 + 1‖ := by
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
  have hlog :=
    log_fourHundredTwentyFive_div_sixteen_gt_threeThousandTwoHundredSeventyEight_div_oneThousand
  rw [show Complex.normSq (heightTenReflectedEndpoint / 2 + 1) =
      (425 / 16 : ℝ) by
    norm_num [heightTenReflectedEndpoint, Complex.normSq_apply, Complex.div_re,
      Complex.div_im]]
  linarith

theorem heightTen_archimedeanApprox_lt_neg_twentyThree_div_oneHundred :
    levinsonMontgomeryArchimedeanApprox heightTenEndpoint <
      (-23 / 100 : ℝ) := by
  have hpi := log_pi_lt_twoHundredTwentyNine_div_twoHundred
  have hnorm : (1639 / 1000 : ℝ) <
      Real.log ‖((1 / 2 : ℂ) + (10 : ℂ) * I) / 2 + 1‖ := by
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    rw [show Complex.normSq (((1 / 2 : ℂ) + (10 : ℂ) * I) / 2 + 1) =
        (425 / 16 : ℝ) by
      norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]]
    linarith [
      log_fourHundredTwentyFive_div_sixteen_gt_threeThousandTwoHundredSeventyEight_div_oneThousand]
  unfold levinsonMontgomeryArchimedeanApprox
  rw [Complex.sub_re, Complex.log_re]
  norm_num [heightTenEndpoint, Complex.div_re, Complex.normSq,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im] at ⊢
  linarith

theorem heightTen_reflected_archimedeanApprox_lt_neg_twentyThree_div_oneHundred :
    levinsonMontgomeryArchimedeanApprox heightTenReflectedEndpoint <
      (-23 / 100 : ℝ) := by
  have hpi := log_pi_lt_twoHundredTwentyNine_div_twoHundred
  have hnorm : (1639 / 1000 : ℝ) <
      Real.log ‖((1 / 2 : ℂ) - (10 : ℂ) * I) / 2 + 1‖ := by
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _)]
    rw [show Complex.normSq (((1 / 2 : ℂ) - (10 : ℂ) * I) / 2 + 1) =
        (425 / 16 : ℝ) by
      norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im]]
    linarith [
      log_fourHundredTwentyFive_div_sixteen_gt_threeThousandTwoHundredSeventyEight_div_oneThousand]
  unfold levinsonMontgomeryArchimedeanApprox
  rw [Complex.sub_re, Complex.log_re]
  norm_num [heightTenReflectedEndpoint, Complex.div_re, Complex.normSq,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im] at ⊢
  linarith

theorem heightTen_archimedeanError_lt_one_div_oneHundredTwentyFive :
    levinsonMontgomeryArchimedeanError heightTenEndpoint <
      (1 / 125 : ℝ) := by
  unfold levinsonMontgomeryArchimedeanError
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [heightTenEndpoint, Complex.normSq_apply, Complex.div_re,
    Complex.div_im]

theorem heightTen_reflected_archimedeanError_lt_one_div_oneHundredTwentyFive :
    levinsonMontgomeryArchimedeanError heightTenReflectedEndpoint <
      (1 / 125 : ℝ) := by
  unfold levinsonMontgomeryArchimedeanError
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [heightTenReflectedEndpoint, Complex.normSq_apply, Complex.div_re,
    Complex.div_im]

theorem heightTen_reflectedArchimedeanUpper_lt_neg_eleven_div_twentyFive :
    levinsonMontgomeryReflectedArchimedeanUpper heightTenEndpoint <
      (-11 / 25 : ℝ) := by
  unfold levinsonMontgomeryReflectedArchimedeanUpper
  rw [show 1 - heightTenEndpoint = heightTenReflectedEndpoint from
    heightTenEndpoint_one_sub]
  linarith [heightTen_archimedeanApprox_lt_neg_twentyThree_div_oneHundred,
    heightTen_reflected_archimedeanApprox_lt_neg_twentyThree_div_oneHundred,
    heightTen_archimedeanError_lt_one_div_oneHundredTwentyFive,
    heightTen_reflected_archimedeanError_lt_one_div_oneHundredTwentyFive]

theorem thirty_rpow_neg_three_halves_lt_one_div_oneHundredSixtyFour :
    (30 : ℝ) ^ (-3 / 2 : ℝ) < 1 / 164 := by
  have hsqrtSq : Real.sqrt (30 : ℝ) ^ 2 = 30 := by
    rw [sq, Real.mul_self_sqrt (by norm_num)]
  have hsqrt : (82 / 15 : ℝ) < Real.sqrt 30 := by
    nlinarith [Real.sqrt_nonneg (30 : ℝ)]
  have hprod : (164 : ℝ) < 30 * Real.sqrt 30 := by linarith
  rw [show (-3 / 2 : ℝ) = -(1 + 1 / 2) by norm_num,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 30),
    Real.rpow_add (by norm_num : (0 : ℝ) < 30), Real.rpow_one,
    ← Real.sqrt_eq_rpow]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 164) hprod)

theorem norm_reflectedEndpoint_mul_add_one_lt_fourHundredFive_div_four :
    ‖heightTenReflectedEndpoint * (heightTenReflectedEndpoint + 1)‖ <
      (405 / 4 : ℝ) := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [heightTenReflectedEndpoint, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]

theorem norm_two_mul_reflectedEndpoint_add_one_lt_twoHundredOne_div_ten :
    ‖2 * heightTenReflectedEndpoint + 1‖ < (201 / 10 : ℝ) := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [heightTenReflectedEndpoint, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]

theorem log_thirty_lt_threeHundredFortyOne_div_oneHundred :
    Real.log 30 < (341 / 100 : ℝ) := by
  have hdata := heightTen_binaryLog_data
    (u := 30) (by norm_num) (by norm_num)
  have hcenter := (abs_le.mp hdata.2.1).2
  have herror := (abs_le.mp hdata.2.2).2
  have hcenterSharp :
      binaryLogCenter (heightTenBinaryIndex 30) 12 ((30 : ℕ) : ℝ) <
        (1701 / 500 : ℝ) := by
    norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial,
      Finset.sum_range_succ]
  norm_num only [Nat.cast_ofNat] at herror hcenterSharp ⊢
  linarith

theorem heightTen_eulerMaclaurinOneZetaError_lt_thirteen_div_twoHundredFifty :
    eulerMaclaurinOneZetaError heightTenReflectedEndpoint 30 <
      (13 / 250 : ℝ) := by
  unfold eulerMaclaurinOneZetaError
  rw [show heightTenReflectedEndpoint.re = (1 / 2 : ℝ) by
    norm_num [heightTenReflectedEndpoint],
    show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    show 8 * ((1 / 2 : ℝ) + 1) = 12 by norm_num]
  calc
    ‖heightTenReflectedEndpoint * (heightTenReflectedEndpoint + 1)‖ *
          (((30 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) / 12) <
        (405 / 4 : ℝ) * ((1 / 164) / 12) := by
      gcongr
      · exact norm_reflectedEndpoint_mul_add_one_lt_fourHundredFive_div_four
      · exact thirty_rpow_neg_three_halves_lt_one_div_oneHundredSixtyFour
    _ < 13 / 250 := by norm_num

theorem heightTen_eulerMaclaurinOneZetaDerivError_lt_eleven_div_fifty :
    eulerMaclaurinOneZetaDerivError heightTenReflectedEndpoint 30 <
      (11 / 50 : ℝ) := by
  unfold eulerMaclaurinOneZetaDerivError
  rw [show heightTenReflectedEndpoint.re = (1 / 2 : ℝ) by
    norm_num [heightTenReflectedEndpoint],
    show -(1 / 2 : ℝ) - 1 = -3 / 2 by norm_num,
    show 8 * ((1 / 2 : ℝ) + 1) = 12 by norm_num,
    show -((1 / 2 : ℝ) + 1) = -3 / 2 by norm_num,
    show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num]
  change
    ‖2 * heightTenReflectedEndpoint + 1‖ *
          (((30 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) / 12) +
        ‖heightTenReflectedEndpoint * (heightTenReflectedEndpoint + 1)‖ *
          (1 / 8 * (((30 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
            (Real.log 30 / (3 / 2) + 1 / (3 / 2) ^ 2))) <
      (11 / 50 : ℝ)
  calc
    ‖2 * heightTenReflectedEndpoint + 1‖ *
          (((30 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) / 12) +
        ‖heightTenReflectedEndpoint * (heightTenReflectedEndpoint + 1)‖ *
          (1 / 8 * (((30 : ℕ) : ℝ) ^ (-3 / 2 : ℝ) *
            (Real.log 30 / (3 / 2) + 1 / (3 / 2) ^ 2))) <
      (201 / 10 : ℝ) * ((1 / 164) / 12) +
        (405 / 4 : ℝ) * (1 / 8 * ((1 / 164) *
          ((341 / 100) / (3 / 2) + 1 / (3 / 2) ^ 2))) := by
      gcongr
      · exact norm_two_mul_reflectedEndpoint_add_one_lt_twoHundredOne_div_ten
      · exact thirty_rpow_neg_three_halves_lt_one_div_oneHundredSixtyFour
      · exact norm_reflectedEndpoint_mul_add_one_lt_fourHundredFive_div_four
      · exact thirty_rpow_neg_three_halves_lt_one_div_oneHundredSixtyFour
      · exact log_thirty_lt_threeHundredFortyOne_div_oneHundred
    _ < 11 / 50 := by norm_num

theorem seventySeven_div_fifty_lt_norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint :
    (77 / 50 : ℝ) <
      ‖eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30‖ := by
  have hz := norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_sub_rounded_le
  have hre := Complex.abs_re_le_norm
    (eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30 -
      heightTenRoundedEulerZetaApprox)
  have hreLower :=
    sevenHundredSeventyOne_div_fiveHundred_lt_heightTenRoundedEulerZetaApprox_re
  have hactualRe :
      (77 / 50 : ℝ) <
        (eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30).re := by
    have habs := (abs_le.mp (hre.trans hz)).1
    norm_num only [Complex.sub_re] at habs
    linarith
  exact hactualRe.trans_le (Complex.re_le_norm _)

theorem norm_heightTenRoundedEulerZetaApprox_lt_seventeen_div_ten :
    ‖heightTenRoundedEulerZetaApprox‖ < (17 / 10 : ℝ) := by
  have hre0 := seventySeven_div_fifty_lt_heightTenRoundedEulerZetaApprox_re
  have hre1 := heightTenRoundedEulerZetaApprox_re_lt_thirtyOne_div_twenty
  have him := heightTenRoundedEulerZetaApprox_im_bounds
  calc
    ‖heightTenRoundedEulerZetaApprox‖ ≤
        |heightTenRoundedEulerZetaApprox.re| +
          |heightTenRoundedEulerZetaApprox.im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = heightTenRoundedEulerZetaApprox.re +
        heightTenRoundedEulerZetaApprox.im := by
      rw [abs_of_pos (by linarith), abs_of_nonneg him.1]
    _ < 17 / 10 := by linarith

theorem norm_heightTenRoundedEulerZetaApprox_lt_oneThousandSixHundredSixtyOne_div_oneThousand :
    ‖heightTenRoundedEulerZetaApprox‖ < (1661 / 1000 : ℝ) := by
  have hre0 := seventySeven_div_fifty_lt_heightTenRoundedEulerZetaApprox_re
  have hre1 := heightTenRoundedEulerZetaApprox_re_lt_thirtyOne_div_twenty
  have him := heightTenRoundedEulerZetaApprox_im_bounds
  calc
    ‖heightTenRoundedEulerZetaApprox‖ ≤
        |heightTenRoundedEulerZetaApprox.re| +
          |heightTenRoundedEulerZetaApprox.im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = heightTenRoundedEulerZetaApprox.re +
        heightTenRoundedEulerZetaApprox.im := by
      rw [abs_of_pos (by linarith), abs_of_nonneg him.1]
    _ < 1661 / 1000 := by linarith

theorem norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_lt_seventeen_div_ten :
    ‖eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30‖ <
      (17 / 10 : ℝ) := by
  have hz := norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_sub_rounded_le
  calc
    ‖eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30‖ ≤
        ‖heightTenRoundedEulerZetaApprox‖ +
          ‖heightTenRoundedEulerZetaApprox -
            eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30‖ :=
      norm_le_norm_add_norm_sub _ _
    _ = ‖heightTenRoundedEulerZetaApprox‖ +
        ‖eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30 -
          heightTenRoundedEulerZetaApprox‖ := by rw [norm_sub_rev]
    _ < (17 / 10 : ℝ) := by
      nlinarith [
        norm_heightTenRoundedEulerZetaApprox_lt_oneThousandSixHundredSixtyOne_div_oneThousand]

theorem norm_heightTenRoundedEulerZetaDerivApprox_lt_two_div_five :
    ‖heightTenRoundedEulerZetaDerivApprox‖ < (2 / 5 : ℝ) := by
  have hre0 :=
    neg_threeHundredFiftyThree_div_oneThousand_lt_heightTenRoundedEulerZetaDerivApprox_re
  have hre1 :=
    heightTenRoundedEulerZetaDerivApprox_re_lt_neg_fortyFour_div_oneTwentyFive
  have him := heightTenRoundedEulerZetaDerivApprox_im_bounds
  calc
    ‖heightTenRoundedEulerZetaDerivApprox‖ ≤
        |heightTenRoundedEulerZetaDerivApprox.re| +
          |heightTenRoundedEulerZetaDerivApprox.im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = -heightTenRoundedEulerZetaDerivApprox.re +
        heightTenRoundedEulerZetaDerivApprox.im := by
      rw [abs_of_neg (by linarith), abs_of_nonneg him.1]
    _ < 2 / 5 := by linarith

theorem norm_heightTenRoundedEulerZetaDerivApprox_lt_threeHundredSeventyThree_div_oneThousand :
    ‖heightTenRoundedEulerZetaDerivApprox‖ < (373 / 1000 : ℝ) := by
  have hre0 :=
    neg_threeHundredFiftyThree_div_oneThousand_lt_heightTenRoundedEulerZetaDerivApprox_re
  have hre1 :=
    heightTenRoundedEulerZetaDerivApprox_re_lt_neg_fortyFour_div_oneTwentyFive
  have him := heightTenRoundedEulerZetaDerivApprox_im_bounds
  calc
    ‖heightTenRoundedEulerZetaDerivApprox‖ ≤
        |heightTenRoundedEulerZetaDerivApprox.re| +
          |heightTenRoundedEulerZetaDerivApprox.im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = -heightTenRoundedEulerZetaDerivApprox.re +
        heightTenRoundedEulerZetaDerivApprox.im := by
      rw [abs_of_neg (by linarith), abs_of_nonneg him.1]
    _ < 373 / 1000 := by linarith

theorem norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_lt_two_div_five :
    ‖eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30‖ <
      (2 / 5 : ℝ) := by
  have hd := norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_sub_rounded_le
  calc
    ‖eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30‖ ≤
        ‖heightTenRoundedEulerZetaDerivApprox‖ +
          ‖heightTenRoundedEulerZetaDerivApprox -
            eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30‖ :=
      norm_le_norm_add_norm_sub _ _
    _ = ‖heightTenRoundedEulerZetaDerivApprox‖ +
        ‖eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30 -
          heightTenRoundedEulerZetaDerivApprox‖ := by rw [norm_sub_rev]
    _ < (2 / 5 : ℝ) := by
      nlinarith [
        norm_heightTenRoundedEulerZetaDerivApprox_lt_threeHundredSeventyThree_div_oneThousand]

theorem neg_twoHundredSeventyFour_div_fiveHundred_lt_heightTenRoundedEuler_cross_re :
    (-274 / 500 : ℝ) <
      (heightTenRoundedEulerZetaDerivApprox *
        conj heightTenRoundedEulerZetaApprox).re := by
  have hzRe0 :=
    sevenHundredSeventyOne_div_fiveHundred_lt_heightTenRoundedEulerZetaApprox_re
  have hzRe1 := heightTenRoundedEulerZetaApprox_re_lt_thirtyOne_div_twenty
  have hzIm := heightTenRoundedEulerZetaApprox_im_bounds
  have hdRe0 :=
    neg_threeHundredFiftyThree_div_oneThousand_lt_heightTenRoundedEulerZetaDerivApprox_re
  have hdRe1 :=
    heightTenRoundedEulerZetaDerivApprox_re_lt_neg_fortyFour_div_oneTwentyFive
  have hdIm := heightTenRoundedEulerZetaDerivApprox_im_bounds
  have hprodRe :
      (-353 / 1000 : ℝ) * (31 / 20) <
        heightTenRoundedEulerZetaDerivApprox.re *
          heightTenRoundedEulerZetaApprox.re := by
    calc
      (-353 / 1000 : ℝ) * (31 / 20) <
          (-353 / 1000 : ℝ) * heightTenRoundedEulerZetaApprox.re := by
        exact mul_lt_mul_of_neg_left hzRe1 (by norm_num)
      _ < heightTenRoundedEulerZetaDerivApprox.re *
          heightTenRoundedEulerZetaApprox.re := by
        exact mul_lt_mul_of_pos_right hdRe0 (by linarith)
  have hprodIm :
      0 ≤ heightTenRoundedEulerZetaDerivApprox.im *
        heightTenRoundedEulerZetaApprox.im := mul_nonneg hdIm.1 hzIm.1
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith

theorem neg_fiveHundredFortyNine_div_oneThousand_lt_eulerMaclaurinOne_finite_cross_re :
    (-549 / 1000 : ℝ) <
      (eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30 *
        conj (eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30)).re := by
  let z : ℂ := eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30
  let d : ℂ := eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30
  let Z : ℂ := heightTenRoundedEulerZetaApprox
  let D : ℂ := heightTenRoundedEulerZetaDerivApprox
  have hz : ‖z - Z‖ ≤ (1 / 50000000 : ℝ) := by
    simpa only [z, Z] using
      norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_sub_rounded_le
  have hd : ‖d - D‖ ≤ (1 / 1000000 : ℝ) := by
    simpa only [d, D] using
      norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_sub_rounded_le
  have hzNorm : ‖z‖ < (17 / 10 : ℝ) := by
    simpa only [z] using
      norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_lt_seventeen_div_ten
  have hDNorm : ‖D‖ < (2 / 5 : ℝ) := by
    simpa only [D] using norm_heightTenRoundedEulerZetaDerivApprox_lt_two_div_five
  have hidentity :
      d * conj z - D * conj Z =
        (d - D) * conj z + D * conj (z - Z) := by
    simp only [map_sub]
    ring
  have hproductNorm :
      ‖d * conj z - D * conj Z‖ < (1 / 500000 : ℝ) := by
    rw [hidentity]
    calc
      ‖(d - D) * conj z + D * conj (z - Z)‖ ≤
          ‖d - D‖ * ‖z‖ + ‖D‖ * ‖z - Z‖ := by
        calc
          ‖(d - D) * conj z + D * conj (z - Z)‖ ≤
              ‖(d - D) * conj z‖ +
                ‖D * conj (z - Z)‖ := norm_add_le _ _
          _ = ‖d - D‖ * ‖z‖ + ‖D‖ * ‖z - Z‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      _ < (1 / 500000 : ℝ) := by
        nlinarith [norm_nonneg (d - D), norm_nonneg (z - Z), norm_nonneg z,
          norm_nonneg D]
  have hre := Complex.abs_re_le_norm
    (d * conj z - D * conj Z)
  have hrounded : (-274 / 500 : ℝ) < (D * conj Z).re := by
    simpa only [D, Z] using
      neg_twoHundredSeventyFour_div_fiveHundred_lt_heightTenRoundedEuler_cross_re
  have habs := (abs_lt.mp (hre.trans_lt hproductNorm)).1
  norm_num only [Complex.sub_re] at habs
  simpa only [z, d] using
    (show (-549 / 1000 : ℝ) < (d * conj z).re by linarith)

theorem speiserStrictNegativePoint_heightTenEndpoint :
    riemannZeta heightTenEndpoint ≠ 0 ∧
      deriv riemannZeta heightTenEndpoint ≠ 0 ∧
      (speiserZetaDerivRatio heightTenEndpoint).re < 0 := by
  apply speiserStrictNegativePoint_of_reflected_eulerMaclaurinOne_margins
    heightTenEndpoint (by norm_num [heightTenEndpoint])
    (by norm_num [heightTenEndpoint]) (N := 30) (by norm_num)
  · rw [heightTenEndpoint_one_sub]
    exact heightTen_eulerMaclaurinOneZetaError_lt_thirteen_div_twoHundredFifty.trans
      ((by norm_num : (13 / 250 : ℝ) < 77 / 50).trans
        seventySeven_div_fifty_lt_norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint)
  · exact heightTen_reflectedArchimedeanUpper_lt_neg_eleven_div_twentyFive.trans
      (by norm_num)
  · rw [heightTenEndpoint_one_sub]
    let z : ℂ := eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30
    let d : ℂ := eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30
    let ez : ℝ := eulerMaclaurinOneZetaError heightTenReflectedEndpoint 30
    let ed : ℝ := eulerMaclaurinOneZetaDerivError heightTenReflectedEndpoint 30
    let U : ℝ := levinsonMontgomeryReflectedArchimedeanUpper heightTenEndpoint
    have hez : ez < (13 / 250 : ℝ) := by
      simpa only [ez] using
        heightTen_eulerMaclaurinOneZetaError_lt_thirteen_div_twoHundredFifty
    have hed : ed < (11 / 50 : ℝ) := by
      simpa only [ed] using
        heightTen_eulerMaclaurinOneZetaDerivError_lt_eleven_div_fifty
    have hez0 : 0 ≤ ez := by
      dsimp only [ez]
      unfold eulerMaclaurinOneZetaError
      rw [show heightTenReflectedEndpoint.re = (1 / 2 : ℝ) by
        norm_num [heightTenReflectedEndpoint]]
      positivity
    have hed0 : 0 ≤ ed := by
      dsimp only [ed]
      unfold eulerMaclaurinOneZetaDerivError
      rw [show heightTenReflectedEndpoint.re = (1 / 2 : ℝ) by
        norm_num [heightTenReflectedEndpoint]]
      positivity
    have hzLower : (77 / 50 : ℝ) < ‖z‖ := by
      simpa only [z] using
        seventySeven_div_fifty_lt_norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint
    have hzUpper : ‖z‖ < (17 / 10 : ℝ) := by
      simpa only [z] using
        norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_lt_seventeen_div_ten
    have hdUpper : ‖d‖ < (2 / 5 : ℝ) := by
      simpa only [d] using
        norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_lt_two_div_five
    have hfiniteCross :
        (-549 / 1000 : ℝ) < (d * conj z).re := by
      simpa only [d, z] using
        neg_fiveHundredFortyNine_div_oneThousand_lt_eulerMaclaurinOne_finite_cross_re
    have hU : U < (-11 / 25 : ℝ) := by
      simpa only [U] using
        heightTen_reflectedArchimedeanUpper_lt_neg_eleven_div_twentyFive
    have hgap : (186 / 125 : ℝ) < ‖z‖ - ez := by linarith
    have hgapPos : 0 < ‖z‖ - ez := by linarith
    have hgapSq :
        (186 / 125 : ℝ) ^ 2 < (‖z‖ - ez) ^ 2 := by nlinarith
    have hleft : U * (‖z‖ - ez) ^ 2 < (-97 / 100 : ℝ) := by
      calc
        U * (‖z‖ - ez) ^ 2 <
            (-11 / 25 : ℝ) * (‖z‖ - ez) ^ 2 :=
          mul_lt_mul_of_pos_right hU (pow_pos hgapPos 2)
        _ < (-11 / 25 : ℝ) * (186 / 125) ^ 2 :=
          mul_lt_mul_of_neg_left hgapSq (by norm_num)
        _ < -97 / 100 := by norm_num
    have hcorrection :
        ed * (‖z‖ + ez) + ‖d‖ * ez < (411 / 1000 : ℝ) := by
      calc
        ed * (‖z‖ + ez) + ‖d‖ * ez <
            (11 / 50 : ℝ) * (17 / 10 + 13 / 250) +
              (2 / 5 : ℝ) * (13 / 250) := by
          gcongr
        _ < 411 / 1000 := by norm_num
    have hright :
        (-24 / 25 : ℝ) <
          (d * conj z).re -
            (ed * (‖z‖ + ez) + ‖d‖ * ez) := by
      linarith
    simpa only [U, z, d, ez, ed] using
      hleft.trans ((by norm_num : (-97 / 100 : ℝ) < -24 / 25).trans hright)

end

end LeanLab.Riemann
