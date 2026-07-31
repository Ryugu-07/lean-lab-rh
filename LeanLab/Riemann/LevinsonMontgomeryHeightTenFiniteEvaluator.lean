import LeanLab.Riemann.LevinsonMontgomeryTranscendentalInterval

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Proof-producing finite evaluator at the reflected height-ten endpoint

This module turns the generic binary-log and scaling-and-squaring backend into a checked table
for all thirty terms of the first Euler--Maclaurin center at `1/2 - 10 i`.  Decimal-looking
centers below are rationals; no floating-point value or external boolean enters a proof.
-/

open Complex Finset Real
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

/-- The worst reflected evaluator point suggested by navigation. -/
def heightTenReflectedEndpoint : ℂ :=
  (((1 / 2 : ℝ) : ℂ) - (10 : ℂ) * I)

/-- Nearest binary scale used to range-reduce `log u` for `1 <= u <= 30`. -/
def heightTenBinaryIndex (u : ℕ) : ℕ :=
  if u ≤ 1 then 0 else if u ≤ 2 then 1 else if u ≤ 5 then 2 else
    if u ≤ 11 then 3 else if u ≤ 22 then 4 else 5

/-- Rational rounded centers for the thirty scaling-and-squaring evaluations. -/
def heightTenRoundedCpowCenter : ℕ → ℂ
  | 1 => ((1000000000000 / 1000000000000 : ℝ) : ℂ) +
      ((0 / 1000000000000 : ℝ) : ℂ) * I
  | 2 => ((563648686752 / 1000000000000 : ℝ) : ℂ) +
      ((426966225740 / 1000000000000 : ℝ) : ℂ) * I
  | 3 => ((-5456687603 / 1000000000000 : ℝ) : ℂ) +
      ((-577324482327 / 1000000000000 : ℝ) : ℂ) * I
  | 4 => ((135399684155 / 1000000000000 : ℝ) : ℂ) +
      ((481317904852 / 1000000000000 : ℝ) : ℂ) * I
  | 5 => ((-414238643643 / 1000000000000 : ℝ) : ℂ) +
      ((-168541823037 / 1000000000000 : ℝ) : ℂ) * I
  | 6 => ((243422400445 / 1000000000000 : ℝ) : ℂ) +
      ((-327738007604 / 1000000000000 : ℝ) : ℂ) * I
  | 7 => ((309896194136 / 1000000000000 : ℝ) : ℂ) +
      ((216382743575 / 1000000000000 : ℝ) : ℂ) * I
  | 8 => ((-129188635055 / 1000000000000 : ℝ) : ℂ) +
      ((329105297090 / 1000000000000 : ℝ) : ℂ) * I
  | 9 => ((-333273782454 / 1000000000000 : ℝ) : ℂ) +
      ((6300558691 / 1000000000000 : ℝ) : ℂ) * I
  | 10 => ((-161523401430 / 1000000000000 : ℝ) : ℂ) +
      ((-271864287450 / 1000000000000 : ℝ) : ℂ) * I
  | 11 => ((122120087874 / 1000000000000 : ℝ) : ℂ) +
      ((-275673312177 / 1000000000000 : ℝ) : ℂ) * I
  | 12 => ((277137776475 / 1000000000000 : ℝ) : ℂ) +
      ((-80795954006 / 1000000000000 : ℝ) : ℂ) * I
  | 13 => ((241136022950 / 1000000000000 : ℝ) : ℂ) +
      ((137027352594 / 1000000000000 : ℝ) : ℂ) * I
  | 14 => ((82284459515 / 1000000000000 : ℝ) : ℂ) +
      ((254279057633 / 1000000000000 : ℝ) : ℂ) * I
  | 15 => ((-95042949864 / 1000000000000 : ℝ) : ℂ) +
      ((240069790577 / 1000000000000 : ℝ) : ℂ) * I
  | 16 => ((-213333851062 / 1000000000000 : ℝ) : ℂ) +
      ((130340584590 / 1000000000000 : ℝ) : ℂ) * I
  | 17 => ((-242130607645 / 1000000000000 : ℝ) : ℂ) +
      ((-14010647843 / 1000000000000 : ℝ) : ℂ) * I
  | 18 => ((-190539455574 / 1000000000000 : ℝ) : ℂ) +
      ((-138745347400 / 1000000000000 : ℝ) : ℂ) * I
  | 19 => ((-89495124842 / 1000000000000 : ℝ) : ℂ) +
      ((-211239678036 / 1000000000000 : ℝ) : ℂ) * I
  | 20 => ((25034415630 / 1000000000000 : ℝ) : ℂ) +
      ((-222200985673 / 1000000000000 : ℝ) : ℂ) * I
  | 21 => ((123232048698 / 1000000000000 : ℝ) : ℂ) +
      ((-180091392889 / 1000000000000 : ℝ) : ℂ) * I
  | 22 => ((186536020794 / 1000000000000 : ℝ) : ℂ) +
      ((-103241747374 / 1000000000000 : ℝ) : ℂ) * I
  | 23 => ((208126791840 / 1000000000000 : ℝ) : ℂ) +
      ((-12708240945 / 1000000000000 : ℝ) : ℂ) * I
  | 24 => ((190705487297 / 1000000000000 : ℝ) : ℂ) +
      ((72787937061 / 1000000000000 : ℝ) : ℂ) * I
  | 25 => ((143187307775 / 1000000000000 : ℝ) : ℂ) +
      ((139633072344 / 1000000000000 : ℝ) : ℂ) * I
  | 26 => ((77409951104 / 1000000000000 : ℝ) : ℂ) +
      ((180192224948 / 1000000000000 : ℝ) : ℂ) * I
  | 27 => ((5456037702 / 1000000000000 : ℝ) : ℂ) +
      ((192372733748 / 1000000000000 : ℝ) : ℂ) * I
  | 28 => ((-62189041977 / 1000000000000 : ℝ) : ℂ) +
      ((178456742020 / 1000000000000 : ℝ) : ℂ) * I
  | 29 => ((-117662002412 / 1000000000000 : ℝ) : ℂ) +
      ((143660752501 / 1000000000000 : ℝ) : ℂ) * I
  | 30 => ((-156072526273 / 1000000000000 : ℝ) : ℂ) +
      ((94734892601 / 1000000000000 : ℝ) : ℂ) * I
  | _ => 0

private theorem norm_cpow_endpoint_sub_binaryCenter_le
    {u k : ℕ} (hu : 1 ≤ u)
    (hL0 : 0 ≤ binaryLogCenter k 12 u)
    (hL : |binaryLogCenter k 12 u| ≤ 7 / 2)
    (hlogError : binaryLogError k 12 u ≤ 1 / 1000000000000000000) :
    ‖(u : ℂ) ^ (-heightTenReflectedEndpoint) -
        binaryScaledCpowCenter k 12 64 16 u heightTenReflectedEndpoint‖ ≤
      1 / 10000000000 := by
  have huPos : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_lt_of_lt hu)
  have hs : ‖heightTenReflectedEndpoint‖ ≤ (11 : ℝ) := by
    calc
      ‖heightTenReflectedEndpoint‖ ≤
          ‖(((1 / 2 : ℝ) : ℂ))‖ + ‖(10 : ℂ) * I‖ := by
        simpa only [heightTenReflectedEndpoint] using
          norm_sub_le (((1 / 2 : ℝ) : ℂ)) ((10 : ℂ) * I)
      _ = 21 / 2 := by norm_num
      _ ≤ 11 := by norm_num
  have hqRe :
      ((((binaryLogCenter k 12 u : ℝ) : ℂ) *
        (-heightTenReflectedEndpoint)).re ≤ 0) := by
    norm_num [heightTenReflectedEndpoint, Complex.mul_re]
    nlinarith
  have hdelta : binaryLogError k 12 u * (11 : ℝ) ≤ 1 := by
    calc
      binaryLogError k 12 u * 11 ≤
          (1 / 1000000000000000000 : ℝ) * 11 := by gcongr
      _ ≤ 1 := by norm_num
  have hB :
      ‖(((binaryLogCenter k 12 u : ℝ) : ℂ) *
          (-heightTenReflectedEndpoint)) / (64 : ℕ)‖ ≤ (1 : ℝ) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg]
    norm_num
    calc
      |binaryLogCenter k 12 u| * ‖heightTenReflectedEndpoint‖ / 64 ≤
          (7 / 2 : ℝ) * 11 / 64 := by gcongr
      _ ≤ 1 := by norm_num
  have h := norm_ofReal_cpow_sub_binaryScaledCpowCenter_le
    (u := (u : ℝ)) (s := heightTenReflectedEndpoint) (S := (11 : ℝ)) (B := (1 : ℝ))
    huPos k 12 hs hqRe hdelta (scale := 64) (expOrder := 16)
    (by norm_num) hB (by norm_num)
  calc
    ‖(u : ℂ) ^ (-heightTenReflectedEndpoint) -
        binaryScaledCpowCenter k 12 64 16 u heightTenReflectedEndpoint‖ ≤
        binaryScaledCpowError k 12 64 16 u 11 1 := h
    _ ≤ 1 / 10000000000 := by
      unfold binaryScaledCpowError
      calc
        2 * (binaryLogError k 12 u * 11) +
            64 * (1 + 1 ^ 16 / (16 : ℕ).factorial * 2) ^ 64 *
              (1 ^ 16 / (16 : ℕ).factorial * 2) ≤
            2 * ((1 / 1000000000000000000 : ℝ) * 11) +
              64 * (1 + 1 ^ 16 / (16 : ℕ).factorial * 2) ^ 64 *
                (1 ^ 16 / (16 : ℕ).factorial * 2) := by gcongr
        _ ≤ 1 / 10000000000 := by norm_num

/-- The analytic backend encloses all thirty exact complex powers at the reflected endpoint. -/
theorem norm_cpow_reflectedEndpoint_sub_binaryCenter_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    ‖(u : ℂ) ^ (-heightTenReflectedEndpoint) -
        binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
          heightTenReflectedEndpoint‖ ≤
      1 / 10000000000 := by
  have hdata :
      0 ≤ binaryLogCenter (heightTenBinaryIndex u) 12 u ∧
      |binaryLogCenter (heightTenBinaryIndex u) 12 u| ≤ 7 / 2 ∧
      binaryLogError (heightTenBinaryIndex u) 12 u ≤
        1 / 1000000000000000000 := by
    interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, binaryLogError]
  exact norm_cpow_endpoint_sub_binaryCenter_le hu1 hdata.1 hdata.2.1 hdata.2.2

private def HeightTenRoundedCenterChecked (u : ℕ) : Prop :=
    ‖binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
          heightTenReflectedEndpoint - heightTenRoundedCpowCenter u‖ ≤
      1 / 10000000000

local macro "check_height_ten_rounded_center" : tactic =>
  `(tactic| (
    unfold HeightTenRoundedCenterChecked
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    norm_num [heightTenBinaryIndex, heightTenReflectedEndpoint,
      heightTenRoundedCpowCenter, binaryScaledCpowCenter, scaledComplexExpTaylor,
      complexExpTaylor, binaryLogCenter, logAtanhPartial, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Finset.sum_range_succ, pow_succ]))

private theorem heightTenRoundedCenterChecked_1 : HeightTenRoundedCenterChecked 1 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_2 : HeightTenRoundedCenterChecked 2 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_3 : HeightTenRoundedCenterChecked 3 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_4 : HeightTenRoundedCenterChecked 4 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_5 : HeightTenRoundedCenterChecked 5 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_6 : HeightTenRoundedCenterChecked 6 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_7 : HeightTenRoundedCenterChecked 7 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_8 : HeightTenRoundedCenterChecked 8 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_9 : HeightTenRoundedCenterChecked 9 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_10 : HeightTenRoundedCenterChecked 10 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_11 : HeightTenRoundedCenterChecked 11 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_12 : HeightTenRoundedCenterChecked 12 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_13 : HeightTenRoundedCenterChecked 13 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_14 : HeightTenRoundedCenterChecked 14 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_15 : HeightTenRoundedCenterChecked 15 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_16 : HeightTenRoundedCenterChecked 16 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_17 : HeightTenRoundedCenterChecked 17 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_18 : HeightTenRoundedCenterChecked 18 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_19 : HeightTenRoundedCenterChecked 19 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_20 : HeightTenRoundedCenterChecked 20 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_21 : HeightTenRoundedCenterChecked 21 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_22 : HeightTenRoundedCenterChecked 22 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_23 : HeightTenRoundedCenterChecked 23 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_24 : HeightTenRoundedCenterChecked 24 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_25 : HeightTenRoundedCenterChecked 25 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_26 : HeightTenRoundedCenterChecked 26 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_27 : HeightTenRoundedCenterChecked 27 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_28 : HeightTenRoundedCenterChecked 28 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_29 : HeightTenRoundedCenterChecked 29 := by
  check_height_ten_rounded_center
private theorem heightTenRoundedCenterChecked_30 : HeightTenRoundedCenterChecked 30 := by
  check_height_ten_rounded_center

/-- Kernel-checked rational coordinate rounding for every scaling-and-squaring center. -/
theorem norm_binaryCenter_sub_heightTenRoundedCpowCenter_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    ‖binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
          heightTenReflectedEndpoint - heightTenRoundedCpowCenter u‖ ≤
      1 / 10000000000 := by
  change HeightTenRoundedCenterChecked u
  interval_cases u
  · exact heightTenRoundedCenterChecked_1
  · exact heightTenRoundedCenterChecked_2
  · exact heightTenRoundedCenterChecked_3
  · exact heightTenRoundedCenterChecked_4
  · exact heightTenRoundedCenterChecked_5
  · exact heightTenRoundedCenterChecked_6
  · exact heightTenRoundedCenterChecked_7
  · exact heightTenRoundedCenterChecked_8
  · exact heightTenRoundedCenterChecked_9
  · exact heightTenRoundedCenterChecked_10
  · exact heightTenRoundedCenterChecked_11
  · exact heightTenRoundedCenterChecked_12
  · exact heightTenRoundedCenterChecked_13
  · exact heightTenRoundedCenterChecked_14
  · exact heightTenRoundedCenterChecked_15
  · exact heightTenRoundedCenterChecked_16
  · exact heightTenRoundedCenterChecked_17
  · exact heightTenRoundedCenterChecked_18
  · exact heightTenRoundedCenterChecked_19
  · exact heightTenRoundedCenterChecked_20
  · exact heightTenRoundedCenterChecked_21
  · exact heightTenRoundedCenterChecked_22
  · exact heightTenRoundedCenterChecked_23
  · exact heightTenRoundedCenterChecked_24
  · exact heightTenRoundedCenterChecked_25
  · exact heightTenRoundedCenterChecked_26
  · exact heightTenRoundedCenterChecked_27
  · exact heightTenRoundedCenterChecked_28
  · exact heightTenRoundedCenterChecked_29
  · exact heightTenRoundedCenterChecked_30

/-- Each exact complex power is within `2e-10` of its compact rational table entry. -/
theorem norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    ‖(u : ℂ) ^ (-heightTenReflectedEndpoint) - heightTenRoundedCpowCenter u‖ ≤
      1 / 5000000000 := by
  calc
    ‖(u : ℂ) ^ (-heightTenReflectedEndpoint) - heightTenRoundedCpowCenter u‖ ≤
        ‖(u : ℂ) ^ (-heightTenReflectedEndpoint) -
          binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
            heightTenReflectedEndpoint‖ +
        ‖binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
            heightTenReflectedEndpoint - heightTenRoundedCpowCenter u‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le
          ((u : ℂ) ^ (-heightTenReflectedEndpoint) -
            binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
              heightTenReflectedEndpoint)
          (binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
              heightTenReflectedEndpoint - heightTenRoundedCpowCenter u)
    _ ≤ 1 / 10000000000 + 1 / 10000000000 :=
      add_le_add
        (norm_cpow_reflectedEndpoint_sub_binaryCenter_le hu1 hu30)
        (norm_binaryCenter_sub_heightTenRoundedCpowCenter_le hu1 hu30)
    _ = 1 / 5000000000 := by norm_num

/-- Compact rational center for the thirty-term partial sum. -/
def heightTenRoundedZetaPartialSum : ℂ :=
  ∑ n ∈ range 30, heightTenRoundedCpowCenter (n + 1)

/-- The exact thirty-term zeta partial sum lies in the aggregated rational ball. -/
theorem norm_zetaPartialSum_reflectedEndpoint_sub_rounded_le :
    ‖zetaPartialSum heightTenReflectedEndpoint 30 -
        heightTenRoundedZetaPartialSum‖ ≤
      3 / 500000000 := by
  unfold zetaPartialSum heightTenRoundedZetaPartialSum
  rw [← sum_sub_distrib]
  calc
    ‖∑ n ∈ range 30,
        (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint) -
          heightTenRoundedCpowCenter (n + 1))‖ ≤
        ∑ n ∈ range 30,
          ‖((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint) -
            heightTenRoundedCpowCenter (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range 30, (1 / 5000000000 : ℝ) := by
      apply sum_le_sum
      intro n hn
      simp only [mem_range] at hn
      have hn30 : n + 1 ≤ 30 := by omega
      simpa only [Nat.cast_add, Nat.cast_one] using
        norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le
          (u := n + 1) (by omega) hn30
    _ = 3 / 500000000 := by norm_num

/-- Uniform logarithm data for the same thirty binary range reductions. -/
theorem heightTen_binaryLog_data
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    0 ≤ binaryLogCenter (heightTenBinaryIndex u) 12 u ∧
    |binaryLogCenter (heightTenBinaryIndex u) 12 u| ≤ 7 / 2 ∧
    |Real.log u - binaryLogCenter (heightTenBinaryIndex u) 12 u| ≤
      1 / 1000000000000000000 := by
  have herror :
      binaryLogError (heightTenBinaryIndex u) 12 u ≤
        1 / 1000000000000000000 := by
    interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogError]
  have hlog := abs_log_sub_binaryLogCenter_le
    (u := (u : ℝ)) (by exact_mod_cast Nat.zero_lt_of_lt hu1)
    (heightTenBinaryIndex u) 12
  refine ⟨?_, ?_, hlog.trans herror⟩
  · interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial]
  · interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial]

/-- Every compact table entry has norm at most one. -/
theorem norm_heightTenRoundedCpowCenter_le_one
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    ‖heightTenRoundedCpowCenter u‖ ≤ 1 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  interval_cases u <;>
    norm_num [heightTenRoundedCpowCenter, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]

/-- The logarithm-weighted exact power is enclosed by the corresponding rational product. -/
theorem norm_log_mul_cpow_reflectedEndpoint_sub_rounded_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    ‖(((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ (-heightTenReflectedEndpoint)) -
        (((binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ) *
          heightTenRoundedCpowCenter u)‖ ≤
      1 / 1000000000 := by
  let P : ℂ := (u : ℂ) ^ (-heightTenReflectedEndpoint)
  let R : ℂ := heightTenRoundedCpowCenter u
  let L : ℝ := binaryLogCenter (heightTenBinaryIndex u) 12 u
  have hdata := heightTen_binaryLog_data hu1 hu30
  have hPR : ‖P - R‖ ≤ (1 / 5000000000 : ℝ) := by
    simpa only [P, R] using
      norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le hu1 hu30
  have hR : ‖R‖ ≤ (1 : ℝ) := by
    simpa only [R] using norm_heightTenRoundedCpowCenter_le_one hu1 hu30
  have hP : ‖P‖ ≤ 1 + (1 / 5000000000 : ℝ) := by
    calc
      ‖P‖ ≤ ‖R‖ + ‖R - P‖ := norm_le_norm_add_norm_sub R P
      _ = ‖R‖ + ‖P - R‖ := by rw [norm_sub_rev]
      _ ≤ 1 + (1 / 5000000000 : ℝ) := add_le_add hR hPR
  have hid :
      (((Real.log u : ℝ) : ℂ) * P) - ((L : ℂ) * R) =
        (((Real.log u - L : ℝ) : ℂ) * P) + (L : ℂ) * (P - R) := by
    norm_num only [Complex.ofReal_sub]
    ring
  rw [show (((Real.log u : ℝ) : ℂ) * (u : ℂ) ^ (-heightTenReflectedEndpoint)) -
        (((binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ) *
          heightTenRoundedCpowCenter u) =
      (((Real.log u : ℝ) : ℂ) * P) - ((L : ℂ) * R) by rfl, hid]
  calc
    ‖(((Real.log u - L : ℝ) : ℂ) * P) + (L : ℂ) * (P - R)‖ ≤
        ‖(((Real.log u - L : ℝ) : ℂ) * P)‖ + ‖(L : ℂ) * (P - R)‖ :=
      norm_add_le _ _
    _ = |Real.log u - L| * ‖P‖ + |L| * ‖P - R‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 / 1000000000000000000 : ℝ) *
          (1 + 1 / 5000000000) + (7 / 2 : ℝ) * (1 / 5000000000) := by
      gcongr
      · simpa only [L] using hdata.2.2
      · simpa only [L] using hdata.2.1
    _ ≤ 1 / 1000000000 := by norm_num

/-- Rational center for the logarithm-weighted partial sum in the derivative formula. -/
def heightTenRoundedLogCpowSum : ℂ :=
  ∑ n ∈ range 30,
    -(((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12 (n + 1) : ℝ) : ℂ)) *
      heightTenRoundedCpowCenter (n + 1)

/-- The exact logarithm-weighted finite sum lies in the aggregated rational ball. -/
theorem norm_logCpowSum_reflectedEndpoint_sub_rounded_le :
    ‖(∑ n ∈ range 30,
          -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint))) -
        heightTenRoundedLogCpowSum‖ ≤
      3 / 100000000 := by
  unfold heightTenRoundedLogCpowSum
  rw [← sum_sub_distrib]
  calc
    ‖∑ n ∈ range 30,
        (-(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
              (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)) -
          -(((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12 (n + 1) : ℝ) : ℂ)) *
            heightTenRoundedCpowCenter (n + 1))‖ ≤
        ∑ n ∈ range 30,
          ‖-(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
                (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)) -
            -(((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12 (n + 1) : ℝ) : ℂ)) *
              heightTenRoundedCpowCenter (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range 30, (1 / 1000000000 : ℝ) := by
      apply sum_le_sum
      intro n hn
      simp only [mem_range] at hn
      have hterm := norm_log_mul_cpow_reflectedEndpoint_sub_rounded_le
        (u := n + 1) (by omega) (by omega : n + 1 ≤ 30)
      rw [show
        -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
              (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)) -
            -(((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12 (n + 1) : ℝ) : ℂ)) *
              heightTenRoundedCpowCenter (n + 1) =
          -(((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
                (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint))) -
            (((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12 (n + 1) : ℝ) : ℂ)) *
              heightTenRoundedCpowCenter (n + 1)) by ring,
        norm_neg]
      simpa only [Nat.cast_add, Nat.cast_one] using hterm
    _ = 3 / 100000000 := by norm_num

/-- Compact rational center for the complete one-correction Euler--Maclaurin value. -/
def heightTenRoundedEulerZetaApprox : ℂ :=
  heightTenRoundedZetaPartialSum -
    (30 : ℂ) * heightTenRoundedCpowCenter 30 /
      (1 - heightTenReflectedEndpoint) -
    heightTenRoundedCpowCenter 30 / 2

/-- Compact rational center for the explicit derivative formula. -/
def heightTenRoundedEulerZetaDerivApprox : ℂ :=
  heightTenRoundedLogCpowSum -
    (((30 : ℂ) * heightTenRoundedCpowCenter 30 *
          ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12 ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1) *
          (1 - heightTenReflectedEndpoint) -
        (30 : ℂ) * heightTenRoundedCpowCenter 30 * (-1)) /
      (1 - heightTenReflectedEndpoint) ^ 2) -
    (heightTenRoundedCpowCenter 30 *
      ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12 ((30 : ℕ) : ℝ) : ℝ) : ℂ) *
        (-1)) / 2

private theorem thirty_cpow_one_sub_eq_mul_cpow_neg :
    ((30 : ℕ) : ℂ) ^ (1 - heightTenReflectedEndpoint) =
      ((30 : ℕ) : ℂ) * ((30 : ℕ) : ℂ) ^ (-heightTenReflectedEndpoint) := by
  rw [show (1 : ℂ) - heightTenReflectedEndpoint =
      (1 : ℂ) + (-heightTenReflectedEndpoint) by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]

private theorem norm_one_sub_heightTenReflectedEndpoint_le :
    ‖(1 : ℂ) - heightTenReflectedEndpoint‖ ≤ 11 := by
  calc
    ‖(1 : ℂ) - heightTenReflectedEndpoint‖ =
        ‖(((1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I)‖ := by
      congr 1
      apply Complex.ext <;> norm_num [heightTenReflectedEndpoint]
    _ ≤ ‖(((1 / 2 : ℝ) : ℂ))‖ + ‖(10 : ℂ) * I‖ := norm_add_le _ _
    _ ≤ 11 := by norm_num

private theorem norm_inv_one_sub_heightTenReflectedEndpoint_le :
    ‖((1 : ℂ) - heightTenReflectedEndpoint)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  apply inv_le_one_of_one_le₀
  calc
    1 ≤ |((1 : ℂ) - heightTenReflectedEndpoint).im| := by
      norm_num [heightTenReflectedEndpoint]
    _ ≤ ‖(1 : ℂ) - heightTenReflectedEndpoint‖ := Complex.abs_im_le_norm _

/-- The actual finite Euler--Maclaurin value center is within `2e-8` of its compact rational
center. -/
theorem norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_sub_rounded_le :
    ‖eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30 -
        heightTenRoundedEulerZetaApprox‖ ≤
      1 / 50000000 := by
  let P : ℂ := ((30 : ℕ) : ℂ) ^ (-heightTenReflectedEndpoint)
  let R : ℂ := heightTenRoundedCpowCenter 30
  let A : ℂ := zetaPartialSum heightTenReflectedEndpoint 30 -
    heightTenRoundedZetaPartialSum
  let D : ℂ := 1 - heightTenReflectedEndpoint
  have hP : ‖P - R‖ ≤ (1 / 5000000000 : ℝ) := by
    simpa only [P, R] using
      norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le
        (u := 30) (by norm_num) (by norm_num)
  have hA : ‖A‖ ≤ (3 / 500000000 : ℝ) := by
    simpa only [A] using norm_zetaPartialSum_reflectedEndpoint_sub_rounded_le
  have hDinv : ‖D⁻¹‖ ≤ (1 : ℝ) := by
    simpa only [D] using norm_inv_one_sub_heightTenReflectedEndpoint_le
  have hid :
      eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30 -
          heightTenRoundedEulerZetaApprox =
        A - ((30 : ℂ) * (P - R)) / D - (P - R) / 2 := by
    unfold eulerMaclaurinOneZetaApprox abelZetaApprox
      heightTenRoundedEulerZetaApprox
    rw [thirty_cpow_one_sub_eq_mul_cpow_neg]
    dsimp only [P, R, A, D]
    ring
  rw [hid]
  calc
    ‖A - ((30 : ℂ) * (P - R)) / D - (P - R) / 2‖ ≤
        ‖A‖ + ‖((30 : ℂ) * (P - R)) / D‖ + ‖(P - R) / 2‖ := by
      calc
        ‖A - ((30 : ℂ) * (P - R)) / D - (P - R) / 2‖ ≤
            ‖A - ((30 : ℂ) * (P - R)) / D‖ + ‖(P - R) / 2‖ :=
          norm_sub_le _ _
        _ ≤ (‖A‖ + ‖((30 : ℂ) * (P - R)) / D‖) + ‖(P - R) / 2‖ :=
          by gcongr; exact norm_sub_le _ _
    _ = ‖A‖ + (30 : ℝ) * ‖P - R‖ * ‖D⁻¹‖ + ‖P - R‖ / 2 := by
      simp only [div_eq_mul_inv, norm_mul, norm_inv]
      norm_num
    _ ≤ (3 / 500000000 : ℝ) +
        30 * (1 / 5000000000) * 1 + (1 / 5000000000) / 2 := by
      gcongr
    _ ≤ 1 / 50000000 := by norm_num

/-- The actual finite Euler--Maclaurin derivative center is within `1e-6` of its compact rational
center. -/
theorem norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_sub_rounded_le :
    ‖eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30 -
        heightTenRoundedEulerZetaDerivApprox‖ ≤
      1 / 1000000 := by
  let P : ℂ := ((30 : ℕ) : ℂ) ^ (-heightTenReflectedEndpoint)
  let R : ℂ := heightTenRoundedCpowCenter 30
  let LP : ℂ := ((Real.log ((30 : ℕ) : ℝ) : ℝ) : ℂ) * P
  let LR : ℂ :=
    ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12 ((30 : ℕ) : ℝ) : ℝ) : ℂ) * R
  let S : ℂ :=
    (∑ n ∈ range 30,
      -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
        (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint))) -
      heightTenRoundedLogCpowSum
  let D : ℂ := 1 - heightTenReflectedEndpoint
  have hP : ‖P - R‖ ≤ (1 / 5000000000 : ℝ) := by
    simpa only [P, R] using
      norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le
        (u := 30) (by norm_num) (by norm_num)
  have hLP : ‖LP - LR‖ ≤ (1 / 1000000000 : ℝ) := by
    simpa only [LP, LR] using
      norm_log_mul_cpow_reflectedEndpoint_sub_rounded_le
        (u := 30) (by norm_num) (by norm_num)
  have hS : ‖S‖ ≤ (3 / 100000000 : ℝ) := by
    simpa only [S] using norm_logCpowSum_reflectedEndpoint_sub_rounded_le
  have hD : ‖D‖ ≤ (11 : ℝ) := by
    simpa only [D] using norm_one_sub_heightTenReflectedEndpoint_le
  have hDinv : ‖D⁻¹‖ ≤ (1 : ℝ) := by
    simpa only [D] using norm_inv_one_sub_heightTenReflectedEndpoint_le
  have hmain :
      ‖((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
          (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2‖ ≤
        30 * (1 / 1000000000 : ℝ) * 11 +
          30 * (1 / 5000000000 : ℝ) := by
    rw [show
        (-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
            (-((30 : ℂ) * LR * D) + (30 : ℂ) * R) =
          -((30 : ℂ) * (LP - LR) * D) + (30 : ℂ) * (P - R) by ring]
    rw [div_eq_mul_inv, ← inv_pow, norm_mul, norm_pow]
    calc
      ‖-((30 : ℂ) * (LP - LR) * D) + (30 : ℂ) * (P - R)‖ * ‖D⁻¹‖ ^ 2 ≤
          (30 * ‖LP - LR‖ * ‖D‖ + 30 * ‖P - R‖) * ‖D⁻¹‖ ^ 2 := by
        gcongr
        calc
          ‖-((30 : ℂ) * (LP - LR) * D) + (30 : ℂ) * (P - R)‖ ≤
              ‖-((30 : ℂ) * (LP - LR) * D)‖ + ‖(30 : ℂ) * (P - R)‖ :=
            norm_add_le _ _
          _ = 30 * ‖LP - LR‖ * ‖D‖ + 30 * ‖P - R‖ := by
            rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
      _ ≤ (30 * (1 / 1000000000 : ℝ) * 11 +
          30 * (1 / 5000000000 : ℝ)) * 1 ^ 2 := by gcongr
      _ = 30 * (1 / 1000000000 : ℝ) * 11 +
          30 * (1 / 5000000000 : ℝ) := by ring
  have hsNe : heightTenReflectedEndpoint ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [heightTenReflectedEndpoint] at him
  rw [eulerMaclaurinOneZetaDerivApprox_eq_finiteFormula
    heightTenReflectedEndpoint hsNe (by norm_num)]
  unfold eulerMaclaurinOneZetaDerivFiniteFormula
    heightTenRoundedEulerZetaDerivApprox
  rw [thirty_cpow_one_sub_eq_mul_cpow_neg]
  have hid :
      (∑ n ∈ range 30,
          -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint))) -
          ((((30 : ℂ) * P) * ((Real.log ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1) * D -
              ((30 : ℂ) * P) * (-1)) / D ^ 2) -
          (P * ((Real.log ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1)) / 2 -
        (heightTenRoundedLogCpowSum -
          (((30 : ℂ) * R *
                ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12
                  ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1) * D -
              (30 : ℂ) * R * (-1)) / D ^ 2) -
          (R * ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12
            ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1)) / 2) =
        S -
          ((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
            (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2 -
          ((-(LP) - (-(LR))) / 2) := by
    dsimp only [P, R, LP, LR, S, D]
    ring
  change
    ‖(∑ n ∈ range 30,
        -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
          (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint))) -
        ((((30 : ℂ) * P) * ((Real.log ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1) * D -
            ((30 : ℂ) * P) * (-1)) / D ^ 2) -
        (P * ((Real.log ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1)) / 2 -
      (heightTenRoundedLogCpowSum -
        (((30 : ℂ) * R *
              ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12
                ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1) * D -
            (30 : ℂ) * R * (-1)) / D ^ 2) -
        (R * ((binaryLogCenter (heightTenBinaryIndex (30 : ℕ)) 12
          ((30 : ℕ) : ℝ) : ℝ) : ℂ) * (-1)) / 2)‖ ≤ _
  rw [hid]
  calc
    ‖S -
        ((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
          (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2 -
        ((-LP - -LR) / 2)‖ ≤
        ‖S‖ +
          ‖((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
            (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2‖ +
          ‖(-LP - -LR) / 2‖ := by
      calc
        ‖S -
            ((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
              (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2 -
            ((-LP - -LR) / 2)‖ ≤
            ‖S -
              ((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
                (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2‖ +
              ‖(-LP - -LR) / 2‖ := norm_sub_le _ _
        _ ≤ (‖S‖ +
              ‖((-((30 : ℂ) * LP * D) + (30 : ℂ) * P) -
                (-((30 : ℂ) * LR * D) + (30 : ℂ) * R)) / D ^ 2‖) +
              ‖(-LP - -LR) / 2‖ :=
          by gcongr; exact norm_sub_le _ _
    _ ≤ (3 / 100000000 : ℝ) +
        (30 * (1 / 1000000000) * 11 + 30 * (1 / 5000000000)) +
        (1 / 1000000000) / 2 := by
      gcongr
      rw [show -LP - -LR = -(LP - LR) by ring, norm_div, norm_neg]
      norm_num
      nlinarith [hLP]
    _ ≤ 1 / 1000000 := by norm_num

/-- Exact rational lower margin for the rounded value center. -/
theorem seventySeven_div_fifty_lt_heightTenRoundedEulerZetaApprox_re :
    (77 / 50 : ℝ) < heightTenRoundedEulerZetaApprox.re := by
  norm_num [heightTenRoundedEulerZetaApprox, heightTenRoundedZetaPartialSum,
    heightTenRoundedCpowCenter, heightTenReflectedEndpoint, Complex.div_re,
    Complex.normSq, Complex.mul_re, Finset.sum_range_succ]

theorem sevenHundredSeventyOne_div_fiveHundred_lt_heightTenRoundedEulerZetaApprox_re :
    (771 / 500 : ℝ) < heightTenRoundedEulerZetaApprox.re := by
  norm_num [heightTenRoundedEulerZetaApprox, heightTenRoundedZetaPartialSum,
    heightTenRoundedCpowCenter, heightTenReflectedEndpoint, Complex.div_re,
    Complex.normSq, Complex.mul_re, Finset.sum_range_succ]

theorem heightTenRoundedEulerZetaApprox_re_lt_thirtyOne_div_twenty :
    heightTenRoundedEulerZetaApprox.re < (31 / 20 : ℝ) := by
  norm_num [heightTenRoundedEulerZetaApprox, heightTenRoundedZetaPartialSum,
    heightTenRoundedCpowCenter, heightTenReflectedEndpoint, Complex.div_re,
    Complex.normSq, Complex.mul_re, Finset.sum_range_succ]

theorem heightTenRoundedEulerZetaApprox_im_bounds :
    0 ≤ heightTenRoundedEulerZetaApprox.im ∧
      heightTenRoundedEulerZetaApprox.im < (111 / 1000 : ℝ) := by
  norm_num [heightTenRoundedEulerZetaApprox, heightTenRoundedZetaPartialSum,
    heightTenRoundedCpowCenter, heightTenReflectedEndpoint, Complex.div_im,
    Complex.normSq, Complex.mul_im, Finset.sum_range_succ]

/-- Exact rational upper margin for the rounded derivative real part. -/
theorem heightTenRoundedEulerZetaDerivApprox_re_lt_neg_seven_div_twenty :
    heightTenRoundedEulerZetaDerivApprox.re < (-7 / 20 : ℝ) := by
  norm_num [heightTenRoundedEulerZetaDerivApprox, heightTenRoundedLogCpowSum,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, heightTenReflectedEndpoint, Complex.div_re, Complex.normSq,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, pow_two, Finset.sum_range_succ]

theorem heightTenRoundedEulerZetaDerivApprox_re_lt_neg_fortyFour_div_oneTwentyFive :
    heightTenRoundedEulerZetaDerivApprox.re < (-44 / 125 : ℝ) := by
  norm_num [heightTenRoundedEulerZetaDerivApprox, heightTenRoundedLogCpowSum,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, heightTenReflectedEndpoint, Complex.div_re, Complex.normSq,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, pow_two, Finset.sum_range_succ]

theorem neg_threeHundredFiftyThree_div_oneThousand_lt_heightTenRoundedEulerZetaDerivApprox_re :
    (-353 / 1000 : ℝ) < heightTenRoundedEulerZetaDerivApprox.re := by
  norm_num [heightTenRoundedEulerZetaDerivApprox, heightTenRoundedLogCpowSum,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, heightTenReflectedEndpoint, Complex.div_re, Complex.normSq,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, pow_two, Finset.sum_range_succ]

theorem heightTenRoundedEulerZetaDerivApprox_im_bounds :
    0 ≤ heightTenRoundedEulerZetaDerivApprox.im ∧
      heightTenRoundedEulerZetaDerivApprox.im < (19 / 1000 : ℝ) := by
  norm_num [heightTenRoundedEulerZetaDerivApprox, heightTenRoundedLogCpowSum,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, heightTenReflectedEndpoint, Complex.div_im, Complex.normSq,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, pow_two, Finset.sum_range_succ]

/-- Exact rational negative cross margin for the two rounded finite centers. -/
theorem heightTenRoundedEuler_cross_re_lt_neg_twentySeven_div_fifty :
    (heightTenRoundedEulerZetaDerivApprox *
        conj heightTenRoundedEulerZetaApprox).re < (-27 / 50 : ℝ) := by
  have hzRe :=
    sevenHundredSeventyOne_div_fiveHundred_lt_heightTenRoundedEulerZetaApprox_re
  have hzIm := heightTenRoundedEulerZetaApprox_im_bounds
  have hdRe :=
    heightTenRoundedEulerZetaDerivApprox_re_lt_neg_fortyFour_div_oneTwentyFive
  have hdIm := heightTenRoundedEulerZetaDerivApprox_im_bounds
  have hprodRe :
      heightTenRoundedEulerZetaDerivApprox.re *
          heightTenRoundedEulerZetaApprox.re <
        (-44 / 125 : ℝ) * (771 / 500) := by
    calc
      heightTenRoundedEulerZetaDerivApprox.re *
          heightTenRoundedEulerZetaApprox.re <
          (-44 / 125 : ℝ) * heightTenRoundedEulerZetaApprox.re := by
        gcongr
      _ < (-44 / 125 : ℝ) * (771 / 500) := by
        exact mul_lt_mul_of_neg_left hzRe (by norm_num)
  have hprodIm :
      heightTenRoundedEulerZetaDerivApprox.im *
          heightTenRoundedEulerZetaApprox.im <
        (19 / 1000 : ℝ) * (111 / 1000) := by
    calc
      heightTenRoundedEulerZetaDerivApprox.im *
          heightTenRoundedEulerZetaApprox.im ≤
          (19 / 1000 : ℝ) * heightTenRoundedEulerZetaApprox.im := by
        exact mul_le_mul_of_nonneg_right hdIm.2.le hzIm.1
      _ < (19 / 1000 : ℝ) * (111 / 1000) := by
        exact mul_lt_mul_of_pos_left hzIm.2 (by norm_num)
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith

theorem norm_heightTenRoundedEulerZetaApprox_lt_two :
    ‖heightTenRoundedEulerZetaApprox‖ < 2 := by
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
    _ < 2 := by linarith

theorem norm_heightTenRoundedEulerZetaDerivApprox_lt_one :
    ‖heightTenRoundedEulerZetaDerivApprox‖ < 1 := by
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
    _ < 1 := by linarith

/-- The actual finite value center already has a large nonvanishing margin at the reflected
critical endpoint. -/
theorem three_halves_lt_norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint :
    (3 / 2 : ℝ) < ‖eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30‖ := by
  have hz := norm_eulerMaclaurinOneZetaApprox_reflectedEndpoint_sub_rounded_le
  have hre := Complex.abs_re_le_norm
    (eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30 -
      heightTenRoundedEulerZetaApprox)
  have hreLower :=
    sevenHundredSeventyOne_div_fiveHundred_lt_heightTenRoundedEulerZetaApprox_re
  have hactualRe :
      (3 / 2 : ℝ) < (eulerMaclaurinOneZetaApprox
        heightTenReflectedEndpoint 30).re := by
    have habs := (abs_le.mp (hre.trans hz)).1
    norm_num only [Complex.sub_re] at habs
    linarith
  exact hactualRe.trans_le (Complex.re_le_norm _)

/-- The actual finite derivative center remains coarsely bounded after rational rounding. -/
theorem norm_eulerMaclaurinOneZetaDerivApprox_reflectedEndpoint_lt_two :
    ‖eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30‖ < 2 := by
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
    _ < 1 + (1 / 1000000 : ℝ) :=
      add_lt_add_of_lt_of_le norm_heightTenRoundedEulerZetaDerivApprox_lt_one hd
    _ < 2 := by norm_num

/-- The actual finite centers retain a strict negative cross margin after both rounding layers. -/
theorem eulerMaclaurinOne_finite_cross_re_lt_neg_fiftyThree_div_oneHundred :
    (eulerMaclaurinOneZetaDerivApprox heightTenReflectedEndpoint 30 *
        conj (eulerMaclaurinOneZetaApprox heightTenReflectedEndpoint 30)).re <
      (-53 / 100 : ℝ) := by
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
  have hZ : ‖Z‖ < (2 : ℝ) := by
    simpa only [Z] using norm_heightTenRoundedEulerZetaApprox_lt_two
  have hD : ‖D‖ < (1 : ℝ) := by
    simpa only [D] using norm_heightTenRoundedEulerZetaDerivApprox_lt_one
  have hzNorm : ‖z‖ ≤ 2 + (1 / 50000000 : ℝ) := by
    calc
      ‖z‖ ≤ ‖Z‖ + ‖Z - z‖ := norm_le_norm_add_norm_sub Z z
      _ = ‖Z‖ + ‖z - Z‖ := by rw [norm_sub_rev]
      _ ≤ 2 + (1 / 50000000 : ℝ) := add_le_add hZ.le hz
  have hidentity :
      d * conj z - D * conj Z =
        (d - D) * conj z + D * conj (z - Z) := by
    simp only [map_sub]
    ring
  have hproductNorm :
      ‖d * conj z - D * conj Z‖ ≤
        (1 / 1000000 : ℝ) * (2 + 1 / 50000000) +
          1 * (1 / 50000000) := by
    rw [hidentity]
    calc
      ‖(d - D) * conj z + D * conj (z - Z)‖ ≤
          ‖(d - D) * conj z‖ + ‖D * conj (z - Z)‖ := norm_add_le _ _
      _ = ‖d - D‖ * ‖z‖ + ‖D‖ * ‖z - Z‖ := by
        rw [norm_mul, norm_mul, norm_conj, norm_conj]
      _ ≤ (1 / 1000000 : ℝ) * (2 + 1 / 50000000) +
          1 * (1 / 50000000) := by gcongr
  have hre := Complex.abs_re_le_norm (d * conj z - D * conj Z)
  have hrounded : (D * conj Z).re < (-27 / 50 : ℝ) := by
    simpa only [D, Z] using heightTenRoundedEuler_cross_re_lt_neg_twentySeven_div_fifty
  have hupper := (abs_le.mp (hre.trans hproductNorm)).2
  have hreEq :
      (d * conj z - D * conj Z).re =
        (d * conj z).re - (D * conj Z).re := rfl
  rw [hreEq] at hupper
  norm_num at hproductNorm
  linarith

end

end LeanLab.Riemann
