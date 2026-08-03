import LeanLab.Riemann.LevinsonMontgomeryHeightTenLeftLowMiddlePhase
import LeanLab.Riemann.LevinsonMontgomeryHeightTenFiniteEvaluator

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Fixed-center phase cells on the middle left boundary

The pointwise phase evaluator is transported to one fixed rational center.  A cell certificate
therefore has two independently audited losses: the actual-function enclosure at the variable
height and the finite-center variation inside the cell.
-/

open Complex Finset Real
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The rational midpoint of the frozen middle-left interval `[6,13/2]`. -/
def leftMiddleCellHeight : ℝ := 25 / 4

/-- The reflected right-half-plane point at a variable middle-left height. -/
def leftMiddleCellReflectedPoint (y : ℝ) : ℂ :=
  1 - (y : ℂ) * I

/-- Rational rounded complex-power centers at the midpoint `1-25 I/4`. -/
def leftMiddleCellRoundedCpowCenter : ℕ → ℂ
  | 1 => (1 : ℂ)
  | 2 => ((-185561966340 / 1000000000000 : ℝ) : ℂ) +
      ((-464291671956 / 1000000000000 : ℝ) : ℂ) * I
  | 3 => ((278245636558 / 1000000000000 : ℝ) : ℂ) +
      ((183549657716 / 1000000000000 : ℝ) : ℂ) * I
  | 4 => ((-181133513296 / 1000000000000 : ℝ) : ℂ) +
      ((172309751207 / 1000000000000 : ℝ) : ℂ) * I
  | _ => 0

/-- Rational phase-preserving complex-power center over the complete middle cell. -/
def leftMiddleCellCpowCenter (y : ℝ) (u : ℕ) : ℂ :=
  leftMiddleCellRoundedCpowCenter u *
    complexExpTaylor 8
      (I * ((((y - leftMiddleCellHeight) *
        binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ)))

private theorem norm_cpow_leftMiddleCenter_sub_binaryCenter_le
    {u k : ℕ} (hu : 1 ≤ u)
    (hL0 : 0 ≤ binaryLogCenter k 12 u)
    (hL : |binaryLogCenter k 12 u| ≤ 3 / 2)
    (hlogError : binaryLogError k 12 u ≤ 1 / 1000000000000000000) :
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
        binaryScaledCpowCenter k 12 64 16 u
          (leftMiddleCellReflectedPoint leftMiddleCellHeight)‖ ≤
      1 / 10000000000 := by
  have huPos : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_lt_of_lt hu)
  have hs : ‖leftMiddleCellReflectedPoint leftMiddleCellHeight‖ ≤ (8 : ℝ) := by
    calc
      ‖leftMiddleCellReflectedPoint leftMiddleCellHeight‖ ≤
          ‖(1 : ℂ)‖ + ‖(leftMiddleCellHeight : ℂ) * I‖ := by
        simpa only [leftMiddleCellReflectedPoint] using
          norm_sub_le (1 : ℂ) ((leftMiddleCellHeight : ℂ) * I)
      _ = 29 / 4 := by norm_num [leftMiddleCellHeight]
      _ ≤ 8 := by norm_num
  have hqRe :
      ((((binaryLogCenter k 12 u : ℝ) : ℂ) *
        (-leftMiddleCellReflectedPoint leftMiddleCellHeight)).re ≤ 0) := by
    norm_num [leftMiddleCellReflectedPoint, leftMiddleCellHeight, Complex.mul_re]
    linarith
  have hdelta : binaryLogError k 12 u * (8 : ℝ) ≤ 1 := by
    calc
      binaryLogError k 12 u * 8 ≤
          (1 / 1000000000000000000 : ℝ) * 8 := by gcongr
      _ ≤ 1 := by norm_num
  have hB :
      ‖(((binaryLogCenter k 12 u : ℝ) : ℂ) *
          (-leftMiddleCellReflectedPoint leftMiddleCellHeight)) / (64 : ℕ)‖ ≤
        (1 : ℝ) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg]
    norm_num
    calc
      |binaryLogCenter k 12 u| *
          ‖leftMiddleCellReflectedPoint leftMiddleCellHeight‖ / 64 ≤
          (3 / 2 : ℝ) * 8 / 64 := by gcongr
      _ ≤ 1 := by norm_num
  have h := norm_ofReal_cpow_sub_binaryScaledCpowCenter_le
    (u := (u : ℝ)) (s := leftMiddleCellReflectedPoint leftMiddleCellHeight)
    (S := (8 : ℝ)) (B := (1 : ℝ)) huPos k 12 hs hqRe hdelta
    (scale := 64) (expOrder := 16) (by norm_num) hB (by norm_num)
  calc
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
        binaryScaledCpowCenter k 12 64 16 u
          (leftMiddleCellReflectedPoint leftMiddleCellHeight)‖ ≤
        binaryScaledCpowError k 12 64 16 u 8 1 := h
    _ ≤ 1 / 10000000000 := by
      unfold binaryScaledCpowError
      calc
        2 * (binaryLogError k 12 u * 8) +
            64 * (1 + 1 ^ 16 / (16 : ℕ).factorial * 2) ^ 64 *
              (1 ^ 16 / (16 : ℕ).factorial * 2) ≤
            2 * ((1 / 1000000000000000000 : ℝ) * 8) +
              64 * (1 + 1 ^ 16 / (16 : ℕ).factorial * 2) ^ 64 *
                (1 ^ 16 / (16 : ℕ).factorial * 2) := by gcongr
        _ ≤ 1 / 10000000000 := by norm_num

private theorem norm_cpow_leftMiddleCenter_sub_binaryCenter_le_of_range
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4) :
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
        binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
          (leftMiddleCellReflectedPoint leftMiddleCellHeight)‖ ≤
      1 / 10000000000 := by
  have hdata :
      0 ≤ binaryLogCenter (heightTenBinaryIndex u) 12 u ∧
      |binaryLogCenter (heightTenBinaryIndex u) 12 u| ≤ 3 / 2 ∧
      binaryLogError (heightTenBinaryIndex u) 12 u ≤
        1 / 1000000000000000000 := by
    interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, binaryLogError]
  exact norm_cpow_leftMiddleCenter_sub_binaryCenter_le
    hu1 hdata.1 hdata.2.1 hdata.2.2

private def LeftMiddleRoundedCenterChecked (u : ℕ) : Prop :=
  ‖binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
      (leftMiddleCellReflectedPoint leftMiddleCellHeight) -
      leftMiddleCellRoundedCpowCenter u‖ ≤ 1 / 10000000000

local macro "check_left_middle_rounded_center" : tactic =>
  `(tactic| (
    unfold LeftMiddleRoundedCenterChecked
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    norm_num [heightTenBinaryIndex, leftMiddleCellReflectedPoint, leftMiddleCellHeight,
      leftMiddleCellRoundedCpowCenter, binaryScaledCpowCenter, scaledComplexExpTaylor,
      complexExpTaylor, binaryLogCenter, logAtanhPartial, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Finset.sum_range_succ, pow_succ]))

private theorem leftMiddleRoundedCenterChecked_1 : LeftMiddleRoundedCenterChecked 1 := by
  check_left_middle_rounded_center
private theorem leftMiddleRoundedCenterChecked_2 : LeftMiddleRoundedCenterChecked 2 := by
  check_left_middle_rounded_center
private theorem leftMiddleRoundedCenterChecked_3 : LeftMiddleRoundedCenterChecked 3 := by
  check_left_middle_rounded_center
private theorem leftMiddleRoundedCenterChecked_4 : LeftMiddleRoundedCenterChecked 4 := by
  check_left_middle_rounded_center

private theorem norm_binaryCenter_sub_leftMiddleRoundedCpowCenter_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4) :
    ‖binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
        (leftMiddleCellReflectedPoint leftMiddleCellHeight) -
        leftMiddleCellRoundedCpowCenter u‖ ≤ 1 / 10000000000 := by
  interval_cases u
  · exact leftMiddleRoundedCenterChecked_1
  · exact leftMiddleRoundedCenterChecked_2
  · exact leftMiddleRoundedCenterChecked_3
  · exact leftMiddleRoundedCenterChecked_4

/-- Every midpoint complex power is enclosed by its rational rounded center. -/
theorem norm_cpow_leftMiddleCenter_sub_rounded_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4) :
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
        leftMiddleCellRoundedCpowCenter u‖ ≤ 1 / 5000000000 := by
  calc
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
        leftMiddleCellRoundedCpowCenter u‖ =
        ‖((u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
          binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
            (leftMiddleCellReflectedPoint leftMiddleCellHeight)) +
          (binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
            (leftMiddleCellReflectedPoint leftMiddleCellHeight) -
          leftMiddleCellRoundedCpowCenter u)‖ := by
      congr 1
      ring
    _ ≤
        ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) -
          binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
            (leftMiddleCellReflectedPoint leftMiddleCellHeight)‖ +
        ‖binaryScaledCpowCenter (heightTenBinaryIndex u) 12 64 16 u
            (leftMiddleCellReflectedPoint leftMiddleCellHeight) -
          leftMiddleCellRoundedCpowCenter u‖ := norm_add_le _ _
    _ ≤ (1 / 10000000000 : ℝ) + 1 / 10000000000 :=
      add_le_add
        (norm_cpow_leftMiddleCenter_sub_binaryCenter_le_of_range hu1 hu4)
        (norm_binaryCenter_sub_leftMiddleRoundedCpowCenter_le hu1 hu4)
    _ = 1 / 5000000000 := by norm_num

/-- The small variable phase across `[6,13/2]` has a uniform eighth-order rational enclosure. -/
theorem norm_leftMiddleCellPhase_sub_taylor_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4)
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖Complex.exp
          (I * ((((y - leftMiddleCellHeight) * Real.log u : ℝ) : ℂ))) -
        complexExpTaylor 8
          (I * ((((y - leftMiddleCellHeight) *
            binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ)))‖ ≤
      1 / 1000000 := by
  let L : ℝ := binaryLogCenter (heightTenBinaryIndex u) 12 u
  let x : ℂ := I * ((((y - leftMiddleCellHeight) * Real.log u : ℝ) : ℂ))
  let q : ℂ := I * ((((y - leftMiddleCellHeight) * L : ℝ) : ℂ))
  have hdata := heightTen_binaryLog_data hu1 (hu4.trans (by norm_num : 4 ≤ 30))
  have hL : |L| ≤ (3 / 2 : ℝ) := by
    dsimp only [L]
    interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial]
  have hyc : |y - leftMiddleCellHeight| ≤ (1 / 4 : ℝ) := by
    rw [abs_le]
    constructor <;> norm_num [leftMiddleCellHeight] <;> linarith
  have hnear : ‖x - q‖ ≤ (1 / 4000000000000000000 : ℝ) := by
    have hid : x - q =
        I * ((((y - leftMiddleCellHeight) * (Real.log u - L) : ℝ) : ℂ)) := by
      dsimp only [x, q]
      norm_num only [Complex.ofReal_mul, Complex.ofReal_sub]
      ring
    rw [hid, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    calc
      |y - leftMiddleCellHeight| * |Real.log u - L| ≤
          (1 / 4 : ℝ) * (1 / 1000000000000000000) := by
        gcongr
        simpa only [L] using hdata.2.2
      _ = 1 / 4000000000000000000 := by norm_num
  have hqRe : q.re ≤ 0 := by norm_num [q]
  have hqNorm : ‖q‖ ≤ (1 / 2 : ℝ) := by
    rw [show ‖q‖ = |y - leftMiddleCellHeight| * |L| by
      dsimp only [q]
      rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]]
    calc
      |y - leftMiddleCellHeight| * |L| ≤ (1 / 4 : ℝ) * (3 / 2) := by
        gcongr
      _ ≤ 1 / 2 := by norm_num
  have h := norm_complex_exp_sub_taylor_of_near hnear (by norm_num)
    hqRe hqNorm (n := 8) (by norm_num)
  simpa only [x, q, L] using h.trans (by norm_num)

private theorem cpow_leftMiddleCell_eq_midpoint_mul_phase
    {u : ℕ} (hu : 1 ≤ u) (y : ℝ) :
    (u : ℂ) ^ (-leftMiddleCellReflectedPoint y) =
      (u : ℂ) ^ (-leftMiddleCellReflectedPoint leftMiddleCellHeight) *
        Complex.exp
          (I * ((((y - leftMiddleCellHeight) * Real.log u : ℝ) : ℂ))) := by
  have huReal : (0 : ℝ) ≤ u := by positivity
  have huC : (u : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hu)
  rw [Complex.cpow_def_of_ne_zero huC, Complex.cpow_def_of_ne_zero huC,
    show Complex.log (u : ℂ) = ((Real.log (u : ℝ) : ℝ) : ℂ) by
      rw [show (u : ℂ) = ((u : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log huReal],
    ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    norm_num [leftMiddleCellReflectedPoint, leftMiddleCellHeight, Complex.mul_re,
      Complex.mul_im] <;>
    ring

private theorem norm_leftMiddleCellRoundedCpowCenter_le_one
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4) :
    ‖leftMiddleCellRoundedCpowCenter u‖ ≤ 1 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  interval_cases u <;>
    norm_num [leftMiddleCellRoundedCpowCenter, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]

/-- Every exact complex power over the whole middle cell lies in a polynomial rational ball. -/
theorem norm_cpow_leftMiddleCell_sub_center_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4)
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint y) -
        leftMiddleCellCpowCenter y u‖ ≤ 1 / 500000 := by
  let P : ℂ := (u : ℂ) ^
    (-leftMiddleCellReflectedPoint leftMiddleCellHeight)
  let R : ℂ := leftMiddleCellRoundedCpowCenter u
  let E : ℂ := Complex.exp
    (I * ((((y - leftMiddleCellHeight) * Real.log u : ℝ) : ℂ)))
  let T : ℂ := complexExpTaylor 8
    (I * ((((y - leftMiddleCellHeight) *
      binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ)))
  have hP : ‖P - R‖ ≤ (1 / 5000000000 : ℝ) := by
    simpa only [P, R] using norm_cpow_leftMiddleCenter_sub_rounded_le hu1 hu4
  have hphase : ‖E - T‖ ≤ (1 / 1000000 : ℝ) := by
    simpa only [E, T] using norm_leftMiddleCellPhase_sub_taylor_le hu1 hu4 hy0 hy1
  have hE : ‖E‖ = 1 := by
    rw [show E = Complex.exp
        (I * ((((y - leftMiddleCellHeight) * Real.log u : ℝ) : ℂ))) by rfl,
      Complex.norm_exp]
    have hre :
        (I * ((((y - leftMiddleCellHeight) * Real.log u : ℝ) : ℂ))).re = 0 := by
      simp only [Complex.mul_re, I_re, I_im, ofReal_re, ofReal_im, mul_zero,
        zero_mul, sub_zero]
    rw [hre, Real.exp_zero]
  have hEle : ‖E‖ ≤ (1 : ℝ) := hE.le
  have hR : ‖R‖ ≤ (1 : ℝ) := by
    simpa only [R] using norm_leftMiddleCellRoundedCpowCenter_le_one hu1 hu4
  have hid : P * E - R * T = (P - R) * E + R * (E - T) := by ring
  rw [cpow_leftMiddleCell_eq_midpoint_mul_phase hu1 y]
  change ‖P * E - R * T‖ ≤ _
  rw [hid]
  calc
    ‖(P - R) * E + R * (E - T)‖ ≤
        ‖(P - R) * E‖ + ‖R * (E - T)‖ := norm_add_le _ _
    _ = ‖P - R‖ * ‖E‖ + ‖R‖ * ‖E - T‖ := by rw [norm_mul, norm_mul]
    _ ≤ (1 / 5000000000 : ℝ) * 1 + 1 * (1 / 1000000) := by
      gcongr
    _ ≤ 1 / 500000 := by norm_num

/-- Rational polynomial center for a logarithm-weighted complex power. -/
def leftMiddleCellLogCpowCenter (y : ℝ) (u : ℕ) : ℂ :=
  ((binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ) *
    leftMiddleCellCpowCenter y u

private theorem norm_cpow_leftMiddleCell_le_one
    {u : ℕ} (hu1 : 1 ≤ u) (y : ℝ) :
    ‖(u : ℂ) ^ (-leftMiddleCellReflectedPoint y)‖ ≤ 1 := by
  have huPos : (0 : ℝ) < u := by exact_mod_cast (Nat.zero_lt_of_lt hu1)
  change ‖((u : ℝ) : ℂ) ^ (-leftMiddleCellReflectedPoint y)‖ ≤ 1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos]
  norm_num [leftMiddleCellReflectedPoint]
  rw [Real.rpow_neg_one]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hu1)

/-- Logarithm-weighted powers inherit a uniform rational polynomial enclosure. -/
theorem norm_log_mul_cpow_leftMiddleCell_sub_center_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu4 : u ≤ 4)
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖((Real.log u : ℝ) : ℂ) *
          (u : ℂ) ^ (-leftMiddleCellReflectedPoint y) -
        leftMiddleCellLogCpowCenter y u‖ ≤ 1 / 250000 := by
  let P : ℂ := (u : ℂ) ^ (-leftMiddleCellReflectedPoint y)
  let R : ℂ := leftMiddleCellCpowCenter y u
  let L : ℝ := binaryLogCenter (heightTenBinaryIndex u) 12 u
  have hdata := heightTen_binaryLog_data hu1 (hu4.trans (by norm_num : 4 ≤ 30))
  have hL : |L| ≤ (3 / 2 : ℝ) := by
    dsimp only [L]
    interval_cases u <;>
      norm_num [heightTenBinaryIndex, binaryLogCenter, logAtanhPartial]
  have hP : ‖P‖ ≤ (1 : ℝ) := by
    simpa only [P] using norm_cpow_leftMiddleCell_le_one hu1 y
  have hPR : ‖P - R‖ ≤ (1 / 500000 : ℝ) := by
    simpa only [P, R] using norm_cpow_leftMiddleCell_sub_center_le hu1 hu4 hy0 hy1
  have hid :
      (((Real.log u : ℝ) : ℂ) * P) - (L : ℂ) * R =
        (((Real.log u - L : ℝ) : ℂ) * P) + (L : ℂ) * (P - R) := by
    norm_num only [Complex.ofReal_sub]
    ring
  unfold leftMiddleCellLogCpowCenter
  change ‖(((Real.log u : ℝ) : ℂ) * P) - (L : ℂ) * R‖ ≤ _
  rw [hid]
  calc
    ‖(((Real.log u - L : ℝ) : ℂ) * P) + (L : ℂ) * (P - R)‖ ≤
        ‖(((Real.log u - L : ℝ) : ℂ) * P)‖ +
          ‖(L : ℂ) * (P - R)‖ := norm_add_le _ _
    _ = |Real.log u - L| * ‖P‖ + |L| * ‖P - R‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 / 1000000000000000000 : ℝ) * 1 +
        (3 / 2) * (1 / 500000) := by
      gcongr
      simpa only [L] using hdata.2.2
    _ ≤ 1 / 250000 := by norm_num

/-- Polynomial rational center for the four-term zeta partial sum. -/
def leftMiddleCellZetaPartialSumCenter (y : ℝ) : ℂ :=
  ∑ n ∈ range 4, leftMiddleCellCpowCenter y (n + 1)

/-- Polynomial rational center for the four logarithm-weighted terms. -/
def leftMiddleCellLogCpowSumCenter (y : ℝ) : ℂ :=
  ∑ n ∈ range 4, -leftMiddleCellLogCpowCenter y (n + 1)

theorem norm_zetaPartialSum_leftMiddleCell_sub_center_le
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖zetaPartialSum (leftMiddleCellReflectedPoint y) 4 -
        leftMiddleCellZetaPartialSumCenter y‖ ≤ 1 / 125000 := by
  unfold zetaPartialSum leftMiddleCellZetaPartialSumCenter
  rw [← sum_sub_distrib]
  calc
    ‖∑ n ∈ range 4,
        (((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y) -
          leftMiddleCellCpowCenter y (n + 1))‖ ≤
        ∑ n ∈ range 4,
          ‖((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y) -
            leftMiddleCellCpowCenter y (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range 4, (1 / 500000 : ℝ) := by
      apply sum_le_sum
      intro n hn
      simp only [mem_range] at hn
      simpa only [Nat.cast_add, Nat.cast_one] using
        norm_cpow_leftMiddleCell_sub_center_le
          (u := n + 1) (by omega) (by omega) hy0 hy1
    _ = 1 / 125000 := by norm_num

theorem norm_logCpowSum_leftMiddleCell_sub_center_le
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖(∑ n ∈ range 4,
          -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
            (((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y))) -
        leftMiddleCellLogCpowSumCenter y‖ ≤ 1 / 62500 := by
  unfold leftMiddleCellLogCpowSumCenter
  rw [← sum_sub_distrib]
  calc
    ‖∑ n ∈ range 4,
        (-(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
            (((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y)) -
          -leftMiddleCellLogCpowCenter y (n + 1))‖ ≤
        ∑ n ∈ range 4,
          ‖-(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
              (((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y)) -
            -leftMiddleCellLogCpowCenter y (n + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range 4, (1 / 250000 : ℝ) := by
      apply sum_le_sum
      intro n hn
      simp only [mem_range] at hn
      have hterm := norm_log_mul_cpow_leftMiddleCell_sub_center_le
        (u := n + 1) (by omega) (by omega) hy0 hy1
      rw [show
          -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
              (((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y)) -
            -leftMiddleCellLogCpowCenter y (n + 1) =
          -(((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
              (((n : ℂ) + 1) ^ (-leftMiddleCellReflectedPoint y))) -
            leftMiddleCellLogCpowCenter y (n + 1)) by ring,
        norm_neg]
      simpa only [Nat.cast_add, Nat.cast_one] using hterm
    _ = 1 / 62500 := by norm_num

private theorem four_cpow_one_sub_eq_mul_cpow_neg (y : ℝ) :
    ((4 : ℕ) : ℂ) ^ (1 - leftMiddleCellReflectedPoint y) =
      (4 : ℂ) * ((4 : ℕ) : ℂ) ^ (-leftMiddleCellReflectedPoint y) := by
  rw [show (1 : ℂ) - leftMiddleCellReflectedPoint y =
      (1 : ℂ) + (-leftMiddleCellReflectedPoint y) by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  norm_num

private theorem four_cpow_neg_sub_one_eq_div (y : ℝ) :
    ((4 : ℕ) : ℂ) ^ (-leftMiddleCellReflectedPoint y - 1) =
      ((4 : ℕ) : ℂ) ^ (-leftMiddleCellReflectedPoint y) / 4 := by
  rw [show -leftMiddleCellReflectedPoint y - 1 =
      -leftMiddleCellReflectedPoint y + (-1 : ℂ) by ring,
    Complex.cpow_add _ _ (by norm_num), Complex.cpow_neg_one]
  ring

/-- Complete polynomial-rational center for the second-corrected `N=4` zeta approximation. -/
def leftMiddleCellZetaApproxCenter (y : ℝ) : ℂ :=
  let s := leftMiddleCellReflectedPoint y
  let P := leftMiddleCellCpowCenter y 4
  leftMiddleCellZetaPartialSumCenter y - (4 : ℂ) * P / (1 - s) - P / 2 + s * P / 48

/-- Complete polynomial-rational center for the explicit `N=4` derivative approximation. -/
def leftMiddleCellZetaDerivApproxCenter (y : ℝ) : ℂ :=
  let s := leftMiddleCellReflectedPoint y
  let P := leftMiddleCellCpowCenter y 4
  let LP := leftMiddleCellLogCpowCenter y 4
  leftMiddleCellLogCpowSumCenter y -
    (((4 : ℂ) * LP * (-1) * (1 - s) - (4 : ℂ) * P * (-1)) /
      (1 - s) ^ 2) -
    (LP * (-1)) / 2 + (P / 4 - s * (P / 4) *
      ((binaryLogCenter (heightTenBinaryIndex 4) 12 ((4 : ℕ) : ℝ) : ℝ) : ℂ)) / 12

/-- The exact second-corrected `N=4` value center is enclosed by the polynomial-rational cell
center. -/
theorem norm_eulerMaclaurinTwoZetaApprox_leftMiddleCell_sub_center_le
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖eulerMaclaurinTwoZetaApprox (leftMiddleCellReflectedPoint y) 4 -
        leftMiddleCellZetaApproxCenter y‖ ≤ 1 / 50000 := by
  let s : ℂ := leftMiddleCellReflectedPoint y
  let P : ℂ := ((4 : ℕ) : ℂ) ^ (-s)
  let R : ℂ := leftMiddleCellCpowCenter y 4
  let A : ℂ := zetaPartialSum s 4 - leftMiddleCellZetaPartialSumCenter y
  let d : ℂ := 1 - s
  have hP : ‖P - R‖ ≤ (1 / 500000 : ℝ) := by
    simpa only [P, R, s] using
      norm_cpow_leftMiddleCell_sub_center_le (u := 4) (by norm_num) (by norm_num) hy0 hy1
  have hA : ‖A‖ ≤ (1 / 125000 : ℝ) := by
    simpa only [A, s] using norm_zetaPartialSum_leftMiddleCell_sub_center_le hy0 hy1
  have hdLower : (6 : ℝ) ≤ ‖d‖ := by
    calc
      6 ≤ y := hy0
      _ = |d.im| := by
        dsimp only [d, s]
        norm_num [leftMiddleCellReflectedPoint, abs_of_nonneg (by linarith : 0 ≤ y)]
      _ ≤ ‖d‖ := Complex.abs_im_le_norm d
  have hdInv : ‖d⁻¹‖ ≤ (1 / 6 : ℝ) := by
    rw [norm_inv]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hdLower
  have hsNorm : ‖s‖ ≤ (15 / 2 : ℝ) := by
    calc
      ‖s‖ ≤ ‖(1 : ℂ)‖ + ‖(y : ℂ) * I‖ := by
        simpa only [s, leftMiddleCellReflectedPoint] using
          norm_sub_le (1 : ℂ) ((y : ℂ) * I)
      _ = 1 + |y| := by norm_num [Real.norm_eq_abs]
      _ ≤ 15 / 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hid :
      eulerMaclaurinTwoZetaApprox s 4 - leftMiddleCellZetaApproxCenter y =
        A - (4 : ℂ) * (P - R) / d - (P - R) / 2 + s * (P - R) / 48 := by
    unfold eulerMaclaurinTwoZetaApprox eulerMaclaurinOneZetaApprox abelZetaApprox
      leftMiddleCellZetaApproxCenter
    rw [show ((4 : ℕ) : ℂ) ^ (1 - s) =
        (4 : ℂ) * ((4 : ℕ) : ℂ) ^ (-s) by
          simpa only [s] using four_cpow_one_sub_eq_mul_cpow_neg y,
      show ((4 : ℕ) : ℂ) ^ (-s - 1) =
        ((4 : ℕ) : ℂ) ^ (-s) / 4 by
          simpa only [s] using four_cpow_neg_sub_one_eq_div y]
    dsimp only [s, P, R, A, d]
    ring
  rw [hid]
  calc
    ‖A - (4 : ℂ) * (P - R) / d - (P - R) / 2 + s * (P - R) / 48‖ ≤
        ‖A‖ + 4 * ‖P - R‖ * ‖d⁻¹‖ + ‖P - R‖ / 2 +
          ‖s‖ * ‖P - R‖ / 48 := by
      calc
        _ ≤ ‖A - (4 : ℂ) * (P - R) / d - (P - R) / 2‖ +
            ‖s * (P - R) / 48‖ := norm_add_le _ _
        _ ≤ (‖A - (4 : ℂ) * (P - R) / d‖ + ‖(P - R) / 2‖) +
            ‖s * (P - R) / 48‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ((‖A‖ + ‖(4 : ℂ) * (P - R) / d‖) + ‖(P - R) / 2‖) +
            ‖s * (P - R) / 48‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖A‖ + 4 * ‖P - R‖ * ‖d⁻¹‖ + ‖P - R‖ / 2 +
            ‖s‖ * ‖P - R‖ / 48 := by
          simp only [div_eq_mul_inv, norm_mul, norm_inv]
          norm_num
    _ ≤ (1 / 125000 : ℝ) + 4 * (1 / 500000) * (1 / 6) +
        (1 / 500000) / 2 + (15 / 2) * (1 / 500000) / 48 := by gcongr
    _ ≤ 1 / 50000 := by norm_num

/-- The exact explicit `N=4` derivative center is enclosed by the polynomial-rational cell
center. -/
theorem norm_eulerMaclaurinTwoZetaDerivFiniteFormula_leftMiddleCell_sub_center_le
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖eulerMaclaurinTwoZetaDerivFiniteFormula (leftMiddleCellReflectedPoint y) 4 -
        leftMiddleCellZetaDerivApproxCenter y‖ ≤ 1 / 25000 := by
  let s : ℂ := leftMiddleCellReflectedPoint y
  let P : ℂ := ((4 : ℕ) : ℂ) ^ (-s)
  let R : ℂ := leftMiddleCellCpowCenter y 4
  let L : ℂ :=
    ((binaryLogCenter (heightTenBinaryIndex 4) 12 ((4 : ℕ) : ℝ) : ℝ) : ℂ)
  let LP : ℂ := ((Real.log ((4 : ℕ) : ℝ) : ℝ) : ℂ) * P
  let LR : ℂ := L * R
  let S : ℂ :=
    (∑ n ∈ range 4,
      -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
        (((n : ℂ) + 1) ^ (-s))) - leftMiddleCellLogCpowSumCenter y
  let d : ℂ := 1 - s
  have hP : ‖P - R‖ ≤ (1 / 500000 : ℝ) := by
    simpa only [P, R, s] using
      norm_cpow_leftMiddleCell_sub_center_le (u := 4) (by norm_num) (by norm_num) hy0 hy1
  have hLP : ‖LP - LR‖ ≤ (1 / 250000 : ℝ) := by
    simpa only [LP, LR, L, P, R, s, leftMiddleCellLogCpowCenter] using
      norm_log_mul_cpow_leftMiddleCell_sub_center_le
        (u := 4) (by norm_num) (by norm_num) hy0 hy1
  have hS : ‖S‖ ≤ (1 / 62500 : ℝ) := by
    simpa only [S, s] using norm_logCpowSum_leftMiddleCell_sub_center_le hy0 hy1
  have hdLower : (6 : ℝ) ≤ ‖d‖ := by
    calc
      6 ≤ y := hy0
      _ = |d.im| := by
        dsimp only [d, s]
        norm_num [leftMiddleCellReflectedPoint, abs_of_nonneg (by linarith : 0 ≤ y)]
      _ ≤ ‖d‖ := Complex.abs_im_le_norm d
  have hdInv : ‖d⁻¹‖ ≤ (1 / 6 : ℝ) := by
    rw [norm_inv]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hdLower
  have hdNorm : ‖d‖ ≤ (13 / 2 : ℝ) := by
    have hdEq : d = (y : ℂ) * I := by
      apply Complex.ext <;>
        norm_num [d, s, leftMiddleCellReflectedPoint, Complex.mul_re, Complex.mul_im]
    rw [hdEq, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    exact hy1
  have hsNorm : ‖s‖ ≤ (15 / 2 : ℝ) := by
    calc
      ‖s‖ ≤ ‖(1 : ℂ)‖ + ‖(y : ℂ) * I‖ := by
        simpa only [s, leftMiddleCellReflectedPoint] using
          norm_sub_le (1 : ℂ) ((y : ℂ) * I)
      _ = 1 + |y| := by norm_num [Real.norm_eq_abs]
      _ ≤ 15 / 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hid :
      eulerMaclaurinTwoZetaDerivFiniteFormula s 4 -
          leftMiddleCellZetaDerivApproxCenter y =
        S - (((4 : ℂ) * (LP - LR) * (-1) * d -
            (4 : ℂ) * (P - R) * (-1)) / d ^ 2) -
          ((LP - LR) * (-1)) / 2 +
          ((P - R) / 4 - s * ((LP - LR) / 4)) / 12 := by
    unfold eulerMaclaurinTwoZetaDerivFiniteFormula
      eulerMaclaurinOneZetaDerivFiniteFormula
      eulerMaclaurinTwoCorrectionDerivFiniteFormula
      leftMiddleCellZetaDerivApproxCenter leftMiddleCellLogCpowCenter
    rw [show ((4 : ℕ) : ℂ) ^ (1 - s) =
        (4 : ℂ) * ((4 : ℕ) : ℂ) ^ (-s) by
          simpa only [s] using four_cpow_one_sub_eq_mul_cpow_neg y,
      show ((4 : ℕ) : ℂ) ^ (-s - 1) =
        ((4 : ℕ) : ℂ) ^ (-s) / 4 by
          simpa only [s] using four_cpow_neg_sub_one_eq_div y]
    dsimp only [s, P, R, L, LP, LR, S, d]
    ring
  rw [hid]
  have hmain :
      ‖(((4 : ℂ) * (LP - LR) * (-1) * d -
          (4 : ℂ) * (P - R) * (-1)) / d ^ 2)‖ ≤
        4 * (1 / 250000 : ℝ) * (13 / 2) * (1 / 6) ^ 2 +
          4 * (1 / 500000 : ℝ) * (1 / 6) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow, norm_mul, norm_pow]
    calc
      ‖(4 : ℂ) * (LP - LR) * (-1) * d -
          (4 : ℂ) * (P - R) * (-1)‖ * ‖d⁻¹‖ ^ 2 ≤
          (4 * ‖LP - LR‖ * ‖d‖ + 4 * ‖P - R‖) * ‖d⁻¹‖ ^ 2 := by
        gcongr
        calc
          ‖(4 : ℂ) * (LP - LR) * (-1) * d -
              (4 : ℂ) * (P - R) * (-1)‖ ≤
              ‖(4 : ℂ) * (LP - LR) * (-1) * d‖ +
                ‖(4 : ℂ) * (P - R) * (-1)‖ := norm_sub_le _ _
          _ = 4 * ‖LP - LR‖ * ‖d‖ + 4 * ‖P - R‖ := by norm_num
      _ ≤ (4 * (1 / 250000 : ℝ) * (13 / 2) +
          4 * (1 / 500000)) * (1 / 6) ^ 2 := by gcongr
      _ = 4 * (1 / 250000 : ℝ) * (13 / 2) * (1 / 6) ^ 2 +
          4 * (1 / 500000 : ℝ) * (1 / 6) ^ 2 := by ring
  calc
    ‖S - (((4 : ℂ) * (LP - LR) * (-1) * d -
          (4 : ℂ) * (P - R) * (-1)) / d ^ 2) -
        ((LP - LR) * (-1)) / 2 +
        ((P - R) / 4 - s * ((LP - LR) / 4)) / 12‖ ≤
        ‖S‖ +
          ‖(((4 : ℂ) * (LP - LR) * (-1) * d -
            (4 : ℂ) * (P - R) * (-1)) / d ^ 2)‖ +
          ‖LP - LR‖ / 2 +
          (‖P - R‖ / 4 + ‖s‖ * (‖LP - LR‖ / 4)) / 12 := by
      calc
        _ ≤ ‖S - (((4 : ℂ) * (LP - LR) * (-1) * d -
              (4 : ℂ) * (P - R) * (-1)) / d ^ 2) -
            ((LP - LR) * (-1)) / 2‖ +
            ‖((P - R) / 4 - s * ((LP - LR) / 4)) / 12‖ := norm_add_le _ _
        _ ≤ (‖S - (((4 : ℂ) * (LP - LR) * (-1) * d -
              (4 : ℂ) * (P - R) * (-1)) / d ^ 2)‖ +
            ‖((LP - LR) * (-1)) / 2‖) +
            ‖((P - R) / 4 - s * ((LP - LR) / 4)) / 12‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖S‖ + ‖(((4 : ℂ) * (LP - LR) * (-1) * d -
              (4 : ℂ) * (P - R) * (-1)) / d ^ 2)‖) +
            ‖((LP - LR) * (-1)) / 2‖) +
            ‖((P - R) / 4 - s * ((LP - LR) / 4)) / 12‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ‖S‖ +
            ‖(((4 : ℂ) * (LP - LR) * (-1) * d -
              (4 : ℂ) * (P - R) * (-1)) / d ^ 2)‖ +
            ‖LP - LR‖ / 2 +
            (‖P - R‖ / 4 + ‖s‖ * (‖LP - LR‖ / 4)) / 12 := by
          rw [show ‖((LP - LR) * (-1)) / 2‖ = ‖LP - LR‖ / 2 by
            rw [norm_div, norm_mul]
            norm_num]
          gcongr
          calc
            ‖((P - R) / 4 - s * ((LP - LR) / 4)) / 12‖ =
                ‖(P - R) / 4 - s * ((LP - LR) / 4)‖ / 12 := by norm_num
            _ ≤ (‖(P - R) / 4‖ + ‖s * ((LP - LR) / 4)‖) / 12 := by
              gcongr
              exact norm_sub_le _ _
            _ = (‖P - R‖ / 4 + ‖s‖ * (‖LP - LR‖ / 4)) / 12 := by
              simp only [norm_div, norm_mul]
              norm_num
    _ ≤ (1 / 62500 : ℝ) +
        (4 * (1 / 250000) * (13 / 2) * (1 / 6) ^ 2 +
          4 * (1 / 500000) * (1 / 6) ^ 2) +
        (1 / 250000) / 2 +
        ((1 / 500000) / 4 + (15 / 2) * ((1 / 250000) / 4)) / 12 := by
      gcongr
    _ ≤ 1 / 25000 := by norm_num

/-- The non-expanded derivative approximation is enclosed by the same polynomial-rational cell
center. -/
theorem norm_eulerMaclaurinTwoZetaDerivApprox_leftMiddleCell_sub_center_le
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖eulerMaclaurinTwoZetaDerivApprox (leftMiddleCellReflectedPoint y) 4 -
        leftMiddleCellZetaDerivApproxCenter y‖ ≤ 1 / 25000 := by
  have hsOne : leftMiddleCellReflectedPoint y ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [leftMiddleCellReflectedPoint] at him
    linarith
  have hsRe : 0 < (leftMiddleCellReflectedPoint y).re := by
    norm_num [leftMiddleCellReflectedPoint]
  rw [eulerMaclaurinTwoZetaDerivApprox_eq_finiteFormula
    (leftMiddleCellReflectedPoint y) hsOne hsRe (by norm_num)]
  exact norm_eulerMaclaurinTwoZetaDerivFiniteFormula_leftMiddleCell_sub_center_le hy0 hy1

/-- The rational value center stays uniformly in the right half-plane on the complete cell. -/
theorem sevenEighths_le_leftMiddleCellZetaApproxCenter_re
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (7 / 8 : ℝ) ≤ (leftMiddleCellZetaApproxCenter y).re := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hpoly :
      0 ≤
        177755902077835554263919373193394341673750338981379504551590326789447566366676054295403794878837894395174443720732555362353189946344192385183420696663087602202486378017853018244764080889865532781888725423468784157593298636066492454634588936992430491568411172413498899970366321838398356211456018334277588613089281117604080457433356993806572583407472561539269386277803368770608057768904732892781080417756162313876063656739187088 * v ^ 9 +
        31575015107148683250148585416733028537652525653904277011776771906999691630306545203549017258536899129516891529187039613844952617138672125662677616220383070534017625441325854942561026724397084013792218999515684486047835279298002513574465266069513005961685392879463105122227957874465710283418890741158138152938036920602509064917566511682517810423589812947300134511062761680928873411382913965766994082037351725506170081953009233416 * u * v ^ 8 +
        250820662811277233377532165333969777753163123151099399194112772454595334886654235276910731576473096878098595995084969860972942152556247581458042191818677760345017422880306220677435467824882620723629282352700719928257290571092872377532014811436210183770767561049057579236385685206496547045332363700584084313788341448158013766602816498385770688667812373671267419189801295545625263755325461760808100140334117397867753788832966891625 * u ^ 2 * v ^ 7 +
        886685235188617937568584282634273053745965441567311502570394387776916540950304006999921054987717605205315730934876281968247085570791421248186038000221875363413636336916937630678302734253158391405401840774372712848332866689845783925073192842125912373150879703531203048742100295585229095170303191262622836126814757185731783374555816987201374775903354942642930772971999728699533877579051933777901267920079737575449723279236015087935 * u ^ 3 * v ^ 6 +
        1798650599165911091001103493143986591177587680956141492586218802057905701306740061689315198037658814672286150929332112818085294031639114354208131352152488604744785089812986075585916361409181679774383043633954076153620432983685241299483253421382232746073656196558095502162909431220622501096781502316768695000014493504769834955007001062983804663839747042431528033915320990212004023146725929435789186057194559298005259579664843496381 * u ^ 4 * v ^ 5 +
        2283839638022578669719584351967094628280924853282668896758887902877261292063208841347208369981830496942637984807568492536670635745029111691314279926761101868316573279015682637101485654279965107822419630001484407186350038026276326218978686591105830599837866114853913778415760974114015444856697055319624045460951010437006190156357146841569753647088695483219290249990712649868943929337031286836652959242576686302495684263492535454987 * u ^ 5 * v ^ 4 +
        1857103964167335108053188621281415464694927671874731495446027069583724219277821776574304852790561707116813371758053444779237516570960122697160918317906888631479980103092121679671408096971261467140297585197307177465770872853414780284212939220345908751001251720643614763505613908185136571026138042152887527576289901495046596531617253643559718908616601809193849181718964343318073613749024240196451031868730736564258932016094640213979 * u ^ 6 * v ^ 3 +
        944033929472584361712922620079035447527306194702978070768424002454945946875921198736244958100787258156308390130158285509942419403260836311832346677556034246758226767387798182212930499160571029718352055048601909554421772228374837734119411873066021801653480618428416503887408650233481151276851209621405304573538859670159993726508594540893676287563130925476623445698936708767093597965744887458585117468295972269621283618954593850365 * u ^ 7 * v ^ 2 +
        274228692000507475125011041077672588767969710032537030619802382885877060547832638038573888208672869464304940748358787985948419004585352385739661545191410836226140960543790066360731119221834034074369314759911660479415964781454667245037561465585271532726402147135493404173435413226462305052585492807083539716498171887552938031713435147888808704687884590423706278195705918162924236558673314163955169899577474268156829823465322035375 * u ^ 8 * v +
        34847857315335830874944364508740350925839187071762869312080157572533438804491748317590075735563980142687645967176783288983855428906663247232194144121645344796941056748154011599580000277473568502240723241221385815005964062791094565028632290312210836508856391931895377457535493367608799584150889324806392174510162425353259145211044799699565326338621904278234746167302694521894939777515921771780223502197018290332099722930584548849 * u ^ 9 := by
    positivity
  have hid :
      ((leftMiddleCellZetaApproxCenter y).re - 7 / 8) * y =
        (177755902077835554263919373193394341673750338981379504551590326789447566366676054295403794878837894395174443720732555362353189946344192385183420696663087602202486378017853018244764080889865532781888725423468784157593298636066492454634588936992430491568411172413498899970366321838398356211456018334277588613089281117604080457433356993806572583407472561539269386277803368770608057768904732892781080417756162313876063656739187088 * v ^ 9 +
          31575015107148683250148585416733028537652525653904277011776771906999691630306545203549017258536899129516891529187039613844952617138672125662677616220383070534017625441325854942561026724397084013792218999515684486047835279298002513574465266069513005961685392879463105122227957874465710283418890741158138152938036920602509064917566511682517810423589812947300134511062761680928873411382913965766994082037351725506170081953009233416 * u * v ^ 8 +
          250820662811277233377532165333969777753163123151099399194112772454595334886654235276910731576473096878098595995084969860972942152556247581458042191818677760345017422880306220677435467824882620723629282352700719928257290571092872377532014811436210183770767561049057579236385685206496547045332363700584084313788341448158013766602816498385770688667812373671267419189801295545625263755325461760808100140334117397867753788832966891625 * u ^ 2 * v ^ 7 +
          886685235188617937568584282634273053745965441567311502570394387776916540950304006999921054987717605205315730934876281968247085570791421248186038000221875363413636336916937630678302734253158391405401840774372712848332866689845783925073192842125912373150879703531203048742100295585229095170303191262622836126814757185731783374555816987201374775903354942642930772971999728699533877579051933777901267920079737575449723279236015087935 * u ^ 3 * v ^ 6 +
          1798650599165911091001103493143986591177587680956141492586218802057905701306740061689315198037658814672286150929332112818085294031639114354208131352152488604744785089812986075585916361409181679774383043633954076153620432983685241299483253421382232746073656196558095502162909431220622501096781502316768695000014493504769834955007001062983804663839747042431528033915320990212004023146725929435789186057194559298005259579664843496381 * u ^ 4 * v ^ 5 +
          2283839638022578669719584351967094628280924853282668896758887902877261292063208841347208369981830496942637984807568492536670635745029111691314279926761101868316573279015682637101485654279965107822419630001484407186350038026276326218978686591105830599837866114853913778415760974114015444856697055319624045460951010437006190156357146841569753647088695483219290249990712649868943929337031286836652959242576686302495684263492535454987 * u ^ 5 * v ^ 4 +
          1857103964167335108053188621281415464694927671874731495446027069583724219277821776574304852790561707116813371758053444779237516570960122697160918317906888631479980103092121679671408096971261467140297585197307177465770872853414780284212939220345908751001251720643614763505613908185136571026138042152887527576289901495046596531617253643559718908616601809193849181718964343318073613749024240196451031868730736564258932016094640213979 * u ^ 6 * v ^ 3 +
          944033929472584361712922620079035447527306194702978070768424002454945946875921198736244958100787258156308390130158285509942419403260836311832346677556034246758226767387798182212930499160571029718352055048601909554421772228374837734119411873066021801653480618428416503887408650233481151276851209621405304573538859670159993726508594540893676287563130925476623445698936708767093597965744887458585117468295972269621283618954593850365 * u ^ 7 * v ^ 2 +
          274228692000507475125011041077672588767969710032537030619802382885877060547832638038573888208672869464304940748358787985948419004585352385739661545191410836226140960543790066360731119221834034074369314759911660479415964781454667245037561465585271532726402147135493404173435413226462305052585492807083539716498171887552938031713435147888808704687884590423706278195705918162924236558673314163955169899577474268156829823465322035375 * u ^ 8 * v +
          34847857315335830874944364508740350925839187071762869312080157572533438804491748317590075735563980142687645967176783288983855428906663247232194144121645344796941056748154011599580000277473568502240723241221385815005964062791094565028632290312210836508856391931895377457535493367608799584150889324806392174510162425353259145211044799699565326338621904278234746167302694521894939777515921771780223502197018290332099722930584548849 * u ^ 9) /
        73606295558611738037056070726753718167181318627220814776542289192343656932121792106035368293830706900367466304998225751371747645039978166009869265939584869440783190075112421794947258310228732659609259749396697841923747331335466136951538753931191034722756215190357921670555763873872907755297724532367157949071228933171547199261762132939587887154187858143392007470577330841182887309497167656212030562092126953125000000000000000000 := by
    dsimp only [u, v]
    norm_num [leftMiddleCellZetaApproxCenter, leftMiddleCellZetaPartialSumCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_re,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hnonneg : 0 ≤ ((leftMiddleCellZetaApproxCenter y).re - 7 / 8) * y := by
    rw [hid]
    positivity
  nlinarith

/-- The rational value-center real part has a uniform upper bound on the complete cell. -/
theorem leftMiddleCellZetaApproxCenter_re_le_nineteenTwentieths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (leftMiddleCellZetaApproxCenter y).re ≤ (19 / 20 : ℝ) := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let z : ℂ := leftMiddleCellZetaApproxCenter y
  let pZreUpper : ℝ := 32945077099297446562411312453845778833557843043267987144892439809765198053088130393420511937344980210770185393528469032754933250321645982319257748976150103646149949155782736789481502158713064164042278161805045244708093000464893269173557850332043535133671885663247565851779727421404410133672520021230943488468963738809592159210359602829007976635977063602987133975481995509761691231504820712402632672523700966592373936343260812912 * v ^ 9 + 269290717988676795976318103678872794470701114234860803387339835166705006079741280029870550642496115325735126992493208144887065881962238627902663008307670083305183663990696169144285891618662860732360630226143317942815481937535715321214949390624230348467580636711124899706168726959989800166360558284892619963890611343736190112064886206708047678319153057213814696024922078132406178466186758828999680840514217195392267418046990766584 * u * v ^ 8 + 963683213905816444233893001657466572005328634198044044618834999219075004493355334472672845271733566977964598037385755036660893990603392157704800696184472585427905213359048738939194294293891468159923503512344794463484540395942318882168374628428441889154709989591848128327784418712406430917080091083474021845886935949172515021216258695117429449376287285694700704074724663333892376851377804566690404134185977328694746211167033108375 * u ^ 2 * v ^ 7 + 1972919347263448085171044065100108897049028787100217151498273547345634530862627616319553003227605357873960335014304788472545310439011730501297382981530996814360790597501179956055398251099227872420417900489688998310404717132537075495494087748100859325828199256614202208158991130914733371123013406819841250194602486867982825316763641877501614640036843346227848717259929574480421294394913029665936119417199394553456526720763984912065 * u ^ 3 * v ^ 6 + 2529399579680459105577793465589132037052673854324442416274467802451901326302021314145564457639586751069320867804563561362573467496711601807172181485095101718373266486603624325956982427232267800610641429630571756951495910098840167553267225309771800095624409256634950292065769484563104474914724700186420192405373767765717140361584612353863963100826499016399922005354626063249549750651707528749478210993822505545744740420335156503619 * u ^ 4 * v ^ 5 + 2082853845992062689328767043897569701987106874277205939859483403458526155434916475343339854049676189921661953736451250163458293296967593007221214275104770511257889472190361785883760444974354457208899704631474692285776272405200202355671349985862077535089646351314069924689959717703494807726340452563057599867699646023395847439846891695071297758333499201137440593201287502284230860298888184368125753853538745191644940736507464545013 * u ^ 5 * v ^ 4 + 1079787228621273239625348600716057890175606941351379014138010269190787692313837728456506342133283498207848533811375762700495214466135006126632865393082547659207269180904863949946987509606864965978111878803621066426986645666870318580153457061508613534436721265451666311149561070382392448410241166688562074591652132938498136718927055460729837788835493730727491916357071157245123589899912749286408987558745128865428567983905359786021 * u ^ 6 * v ^ 3 + 325674668913468119426294599957466190856571551616580984126930486112982135203179715092865144967792435875030403631061108701220227473678787051837898159901804751095283261407891093749909706690874608659907675628491128218762869237161953128294631632247023547314064093605257644929678276590826507502034538561928170047939839427049195460756802252314214765846609627496888683168522248243311208123081254611072409727793217671784966381045406149635 * u ^ 7 * v ^ 2 + 45958693679453585336182866583706085259269025995873513658156575100817847106897157622679963869490705552293537678383494032518683251338552636403269761645783345841265916282948968447289454427660952994930965149963975132952336109854610450701632114015409468317587388942563555093482159624884843682959608908713597361961673971743292285075230130398398604432832592500048954301305470996221323237639365140567163045523277977936920176534677964625 * u ^ 8 * v + 1035211769487391418120469970552086680661705759007277891484208408734093949917625334102166307678489471241493856509851764809871548050326108697617123023902279055440748413463294025456788148762938669318790886609504382931862761234945176735242852229244792918487262973404109356860441520904242946556751384722597325662061679567870114429064240108483768649044676566668857474603754263181717785863947460623141396822893599316337777069415451151 * u ^ 9
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pZreUpper := by
    dsimp only [pZreUpper]
    positivity
  have hid :
      (19 / 20 - z.re) * y = pZreUpper / 73606295558611738037056070726753718167181318627220814776542289192343656932121792106035368293830706900367466304998225751371747645039978166009869265939584869440783190075112421794947258310228732659609259749396697841923747331335466136951538753931191034722756215190357921670555763873872907755297724532367157949071228933171547199261762132939587887154187858143392007470577330841182887309497167656212030562092126953125000000000000000000 := by
    dsimp only [u, v, z, pZreUpper]
    norm_num [leftMiddleCellZetaApproxCenter, leftMiddleCellZetaPartialSumCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_re,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (19 / 20 - z.re) * y := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ 19 / 20 - z.re :=
    nonneg_of_mul_nonneg_left hscaled hyPos
  simpa only [z] using sub_nonneg.mp hnonneg

/-- The rational value-center imaginary part stays above `-3/10` on the complete cell. -/
theorem neg_threeTenths_le_leftMiddleCellZetaApproxCenter_im
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    -(3 / 10 : ℝ) ≤ (leftMiddleCellZetaApproxCenter y).im := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let z : ℂ := leftMiddleCellZetaApproxCenter y
  let pZimLower : ℝ := 637162795896656377201901778490337254843256761138260215106701053709849852661596209386028844718866922670685024669291319468874958222093544224031947197283977859860790257037233540300911259946466462597914827485041533565802227660320178463183669052557127732991314911602508567147378859582617854765789691534391573974217971893338659318603570563273132220251268038207081801445660543918605965732764362268653419727753545909217364725240626212 * v ^ 9 + 5113504185862559643102485641539225708028125556902604386155161393838723705940155440363071037709635404559469886972263085102829427203261153421450025109794685723996984330594868728480557391471740799204430393753126496849455570430987297903719847769744511773645302473924031338122033672349824100777417232392431372224252672256272413144224037528242223815168032499736665688966182680037658069679018651246580541812675758331062757921992385639 * u * v ^ 8 + 18045677683653050823966381149373557689391438995766861050423678160228530465245570348378476005361906000778442946291943960946141119745105847287921075026458606894718346607630449837416489493582136277502587451968290321925453751780821330382051176942152227454873604404409937439961558855957893920136302836627295913391418954400461117181823844693766325444247548416996927539452490625903978094262977024966922406276770628750995753101893100800 * u ^ 2 * v ^ 7 + 36685488098276895292809751591543124235545466555456810317237009966745748125054426592830745678591680177903308978114343864030598041340499901274202869679220586598845698021828394207012780196716390424103605340315339926344448526478468056241194954154219816985741767245654871231169465280635192421569905755423225448813546516666785668122240532222682521287367690280543529874414594346124792810638035326799113428363223670145534064062325253100 * u ^ 3 * v ^ 6 + 47228903445523571693334477489270960158879396118896462094640484308890075581926628423809763490691530020365259049616636403051546416805396723876187096435900468116646159154283420816762837848348533686838923670832734695909397377629040706766508173319443138116710993591170513318417753742755652694984149005497390225212402117984885975637510299500055680622067336122023895512520464260760841190145882150079101777047944557932686229811058486104 * u ^ 4 * v ^ 5 + 39798096598638518549376322554902977703403105820428880467704550627970081658705042211145023913080344015783674217766869342437304920119703701235635148892003734361555242797239494558646447260220304628580303954587533525998345293971590104243599771460548451231141399009078571942428857391422197019874159261402942468288145891543305240521203421122258268539277911749191014029987963375628928915234019014085553517725260451269009241355351847538 * u ^ 5 * v ^ 4 + 21848937214763252709787204325692096047030401380998413544058178883564716326973143051851638430098593455720640258947222117517884724225166651125173663757024532074065236891376983267659360516330973665675991801360001174362141967999282459371302230313466655483089891925524129730865291047641896392543857022974395084948402435964900257437180624739531273751290012550064468558574387261106557275634635232262809542995506871154345185903207961216 * u ^ 6 * v ^ 3 + 7483921773839200363547275981856577375070419746813952429257062082488245303060311405759690663893652069265741962815356433630286523459986807400055755120925194037740763176287416499976711781693026878930781116429852847555064058362518518615248570507654659023678016633182062418716794936875142750264839299189858768372833395085380845490369205734061657118644933525726472611280971621570576887471670571954206733682885286206116501323596915260 * u ^ 7 * v ^ 2 + 1435653823677782872591266758056314316050057586823329550243855854844296167100938965839236776598971015702595711572916007825594745950693748351327128522643879939844112321257374076042280568987868600696453841176982163813932922349178759665531541569606513449362154331413217899276247688391568975245303825241643637897439525052137579285759775894445448485182115023006633839968442842880839382626126706313778729910550799063995866301174519940 * u ^ 8 * v + 115324261098920740331342573622350055755396967343869051407745631315607480185131284944048085352983620234694341147053319917254197219201277916543366675352913668764464737375683256122145755506293419710791905404981508991755008386774166463239635121411137865820239416051075398334034333606339968474403750480195747679711749391461296296292523222014394135096377392970086299184045119940397003587294559051110074656654541296175871431658904191 * u ^ 9
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pZimLower := by
    dsimp only [pZimLower]
    positivity
  have hid : (z.im + 3 / 10) * y = pZimLower / 3345740707209624456229821396670623553053696301237309762570104054197438951460081459365244013355941222743975741136282988698715802047271734818630421179072039520035599548868746445224875377737669666345875443154395356451079424151612097134160852451417774305579827963198087348661625630630586716149896569653052634048692224235070327239171006042708540325190357188336000339571696856417403968613507620736910480095096679687500000000000000000 := by
    dsimp only [u, v, z, pZimLower]
    norm_num [leftMiddleCellZetaApproxCenter, leftMiddleCellZetaPartialSumCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_im,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (z.im + 3 / 10) * y := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ z.im + 3 / 10 :=
    nonneg_of_mul_nonneg_left hscaled hyPos
  dsimp only [z] at hnonneg ⊢
  linarith

/-- The rational value-center imaginary part stays below `-1/4` on the complete cell. -/
theorem leftMiddleCellZetaApproxCenter_im_le_neg_oneQuarter
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (leftMiddleCellZetaApproxCenter y).im ≤ -(1 / 4 : ℝ) := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let z : ℂ := leftMiddleCellZetaApproxCenter y
  let pZimUpper : ℝ := 366559416266230959667044640510849811072852129232932713664330162549381832776428228423544359287915444152507697671593577140739782392087976221557179156437633996149889607623390393266551353374834437305847805461277073369521599585163450677064586682868204558682633477356917637451108829606558160079179279361524216240389695377182438853147731249539429877305839118293718300425848513006615224851287923952419724300775457997032635274759373788 * v ^ 9 + 4003639241283667000123777664388223474043196863969064716848372153849297436788566536407218898685304427417864007624108059101171133375554323959317872603176621968100024440072465334757228012863409041588080188842600849479735860382155666786868475160368923209059728725790756686980896171118524700731050919912137055558433638784294228582516953938138548570975690838478935236366691253699767744792789615261500516446462693817374742078007614361 * u * v ^ 8 + 18757470095652818194561654214003301394199220317843546337847466435943298000815325704639208141553447449405290206207168914739732702774883235717013557943333827825673248429925761060057139661532230052302042422730058599036419913886911738093718200023443289906504503190769023395316323080978559957512559429556283061144195512185312482449057221776027618132846380654699076195836174794687465560485606803139092874769292847811504246898106899200 * u ^ 2 * v ^ 7 + 49969196218452378123542622582226025788545267646589512533328685036967920717761683204729074267327197491165662717315385543266141231683838030528325038858745236970076330293872138724311492086689253934254568637383499805738508559048285259533571124337500537528775777001175591099166638552697003526712415398590837773047582091021535807372288524283468673135062560897358878920492354235085969976451812050286868006099780333760715935937674746900 * u ^ 3 * v ^ 6 + 83924132277093706990874521260217483120825498889606080598107594615649531315308564783307801832861365911198590002925656753938113023447655281014125413783723481068749343161371439836052276958968117233919393700819563276972916049114153500892597242776133614662018262566194510749117970977963346578091796524902273029496333072029870852137993137374119100125394665660747317798690052510801394379503616582807789042679845285817313770188941513896 * u ^ 4 * v ^ 5 + 92525948371502128694513113683420183819870582893506720641943064715538628871541179506750376815147131343740566344173122860596905050849893410841198008740295428655852719360519427349997373929304530675399069822168802821641845931224668337412461942993024522554540796935405782697138436300017507603854250068375289208337631576953726201788009867866864501322000715049497799400072647295679398043430207386059255970035813230371615758644648152462 * u ^ 5 * v ^ 4 + 67147765597012757825926044825746490464197920231914026140306588958087159781865023767263852325169443069269114455277905381867955610232261495050395539606291719158881711108531672175322324531491039459124294986546915307236570714433599324397376444894246141045333531895544993743533950727131710257043391729796804980746810728687970447124768135996515898898773488659673140474032749119596388289484667479339009227534064808533154814096792038784 * u ^ 6 * v ^ 3 + 30992096359071480883095670079855593485047087717415109840299134540782302638730625376940615489699671992289979060251897936404945200083638143014194088438403260442668631635703167620109355062290174284046786479845693751632349319381020598427601232683649745490490004943595942090891899815376604485458971251820246523187127183617927917760097363757086556621044174140137531293793542227229568751583667066520263787410726530200133498676403084740 * u ^ 7 * v ^ 2 + 8266994227230128050475215292288493987805661686764868761209445902328276792133297266319970862133258530254933937722304659400681079986394282622701092896665034668259126370461990615109858026451373431706584943970764369894197407690496322023534930539505032036819346761861235411842466640437132501589396226752209000843767925229566369707836141629409318457869920823167767144789478040729632126353045393823261662365229572029754133698825480060 * u ^ 8 * v + 972041468744207207943349380295602598987054330558256621427538186298560179039395189349656218987697277157097774722238651409828438446162035899511520207845499175247105116006659338575938742258449221851617613620196981854845804462499765105362641925299638783493204671988302989980993996348600714274312634657046358386113223484936560056438053741865881470590488693239113811176756358395259286212095417688385831374251879602261628568341095809 * u ^ 9
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pZimUpper := by
    dsimp only [pZimUpper]
    positivity
  have hid : (-(1 / 4 : ℝ) - z.im) * y = pZimUpper / 3345740707209624456229821396670623553053696301237309762570104054197438951460081459365244013355941222743975741136282988698715802047271734818630421179072039520035599548868746445224875377737669666345875443154395356451079424151612097134160852451417774305579827963198087348661625630630586716149896569653052634048692224235070327239171006042708540325190357188336000339571696856417403968613507620736910480095096679687500000000000000000 := by
    dsimp only [u, v, z, pZimUpper]
    norm_num [leftMiddleCellZetaApproxCenter, leftMiddleCellZetaPartialSumCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_im,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (-(1 / 4 : ℝ) - z.im) * y := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ -(1 / 4 : ℝ) - z.im :=
    nonneg_of_mul_nonneg_left hscaled hyPos
  dsimp only [z] at hnonneg ⊢
  linarith

/-- The rational derivative-center real part stays above `7/200` on the complete cell. -/
theorem sevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_re
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (7 / 200 : ℝ) ≤ (leftMiddleCellZetaDerivApproxCenter y).re := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let d : ℂ := leftMiddleCellZetaDerivApproxCenter y
  let pDreLower : ℝ := 283680174145349308023569799261612343334200408695444097660774351059101002162081617575162342162421077628091632479969112503404750994760582753024649148476792129981738333519811187090675936046238006491717870241000472427269088408968515152569576975313107333751574444724464460445108727149226293448498075872889004955986679745861360039220457030175884927602936782979323463503397186365126084698155724888681532554519085414192300113110508813263867354784571149367018384295085914354512437820146414060464 * v ^ 10 + 2652612024139404777752127946354125716674164504445714902985060627752758031220099803210808869440545531143527994309479970183434520189151177911627655645795173688826632308218959505500887970311606967276092830861718694517151512298805001449771256895210481427474194481554131339682362952641120789869253066293271285354847740781190849645997058478176622819366193066794420079477699160009459520064790660278828048496990879036823070918346515735085332439082883639855784497351333741122017763786291479242792 * u * v ^ 9 + 11041725993828245798777490208057375241701987912400181942008541992915552259502415207672825251551469159136556407719140604204352354363005447772046764973899877837314849882771023231794159031829667444446069518340756439448509941920532507032863762898130499575400927577134547978414349822030771909415955650188988542123038361512626568826512749110777504327705972590189898421140390956302105521779841005930484351465738833112207793714122768414072641578586018016764806871708298878460718323836108889477579 * u ^ 2 * v ^ 8 + 26872922541925071259912172941511274904663212202531324211312628920679958878506880979880251436589440576946466097815915596637157383292234975984742853612195143033912501895683189504466376254806098492784204170172549913527668362420116136219713562377034463501184241689394400677840023403519621940096127967131837098653388273224576769001247081142282478465481581191207448532835440503842874837920993572260621679986814657697816853503543272391459408631529398527921216936876654338267565526636990168204176 * u ^ 3 * v ^ 7 + 42188550507778276877164029462171427676292943675769632962514013078940213144839687902400285268982456784852707917859402329578707613508924177576408939557655969281895046393511048107485339826072120810933511348445317940746567224348322732399057373888026008972937022540139721969224698957710253622148663509312230772614795877301267748630746330679697941301450768894445590010643700126375445353363574717389214469571875229876198419668382671416208736250027275564590305038085215138420871231337549287646588 * u ^ 4 * v ^ 6 + 44394970160355513421625256753218365501536826415825460060391714789821447092612276106818945990813633526672963711050477983402523943601937717013629772344562449140810303580599040590228616862044072525889139228077389254235679442435341434109107166582245355686624102809110315181496647788161388526602868105773411825360352159625303004538123633868034129355464742091981709820923591939344192147888465923919716269334457682486432088118032484740172865356585429501744307531761345122223836666657632939759632 * u ^ 5 * v ^ 5 + 31434333821407423525912373473343472141456270100479565741347820576439182481467734840948560088954807229642053616197463481659963833883023458662201084462968912404186842923377308519766556315963467135207257962108274773937281237079267676640834905568098056377582872957221568176132236725957949020871328535066938512665470826404013481733863645326100544718113961047268487649381595093316263430730359094677964153772890535066184030772412905065338011968127608754779581732080752886889576527872639436137098 * u ^ 6 * v ^ 4 + 14565228308116740693531813042569318156934977939278267919578408139988160976357063930285566784218559766729020707146384010813979022365475107486580374777677843028658180596723122233047956715685486557170505816785307739727064093905660057484436067233561280715261206032303603678949604947350119816344242263192805903536062459470434169908199125536886103729135510429814071258768891526555158369373124794655210722813764988571538932291778967369041622284563821333721444071654713729715316520765063213382736 * u ^ 7 * v ^ 3 + 4102595145835297635577524003478042152725512132215461367386615244355510988826234724524225475865927968943142480484136395922653586156273403614562773781277234524871684922030613914989648717521693581582429474433529080821661872028584458978193302419152074376125571843322653802618027002116528177226107800275885683136887251899000742867796860542158142360820680586852376732307569225369658935952050292794205566995237388745336007888754006287147031766447296339511529357443900772702066632747230707612764 * u ^ 8 * v ^ 2 + 589936375693830820927596943869461906784366534809906808158600083322572479440970780652051386117045895573274880969823267339015832042468578285241128582824235079626066488895164465628730141075332625752099267003936507309675846495869957276047915019368618475632744128157016387317968303986839753850834356232016911279969687703193981397354389753175328161069329052528717859037695014747868605314111274677878941757878676954833578165040608486375250857139045418733577661783411729057681260777316028360552 * u ^ 9 * v + 24783764791763013437641992582417710760954153120031484696335275987583877473305212836978139735789220029318082593522389781921431818316368607196633712629479784356773523560635478719913703994993365364178406152489574977981181745792720499775960179486018004239923344529624215809376936497550553296784588621068961566931516922600170091674346382944797680461606439076516008648181596110509642402625834367533537117238013840290958627041146646200836403620619475807261226450457409059931483348968936115619 * u ^ 10
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pDreLower := by
    dsimp only [pDreLower]
    positivity
  have hid : (d.re - 7 / 200) * y ^ 2 = pDreLower / 245056858182635455039225216690685051969102491231491554324601823238578317631742295868895728994759618617877063150204317666736296856748666610784148899560717603847053128606918602098466886845591213865634762348594885176969967728638417607365174757041249090251793357747066798980678886182394246204642511584102630898543331958683377244599507991693280830945360506120262688061342854750240296035700975767716732753935592085833979739099939778051270276078388774301223520691756924438476562500000000000000 := by
    dsimp only [u, v, d, pDreLower]
    norm_num [leftMiddleCellZetaDerivApproxCenter,
      leftMiddleCellLogCpowSumCenter, leftMiddleCellLogCpowCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_re,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (d.re - 7 / 200) * y ^ 2 := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ d.re - 7 / 200 :=
    nonneg_of_mul_nonneg_left hscaled (pow_pos hyPos 2)
  dsimp only [d] at hnonneg ⊢
  linarith

/-- The rational derivative-center imaginary part stays above `27/200` on the complete cell. -/
theorem twentySevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_im
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (27 / 200 : ℝ) ≤ (leftMiddleCellZetaDerivApproxCenter y).im := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let d : ℂ := leftMiddleCellZetaDerivApproxCenter y
  let pDimLower : ℝ := 95790662109040128771318221978601921886829244776943444552299431348507740584923636495306223130144193702527748719372078009718164225777574910052632039523304685831155643701248407802799684421217451781011957322841735975238620769791447606325597688656278262065864533254007305708440435009079878489910361661315169373944644958368645035645657507410046428554388743174840048540560880023962819244925312343486657584782937771581577702485856083455182486628975683641016390455866162793802299960460656620368 * v ^ 10 + 3688039241683606348258094364988247490692702100154559396441917409585884333206808425561475815846377833210841062474556862843253513411889322568257724123827901239070017910608369087203135353389724508747050235905474597552534644700392448213460868492726267399220403729354820565312172194469289151829162908085303477488762866095093214836466917102741948672074509093032072968152960370840586635463275606583546992663646521681640352838908726514284047841347248774590738200623936047180387271064887743006168 * u * v ^ 9 + 29205839622615473328406748949225014883893236682069524615624245777068530134670865105654381958620651349513516177405937697722089308909958781097808713859431326979662486214406374158968391790008423994052672517130823505116592719782193312507796245424308349584678003351939173257783336350851505921705629789090020842156802806594423117264023404156904815427748016278270624330778995545999821820292157557713834487426607254572113764722911604969608940083225230732783950469478872493946278995179459330175589 * u ^ 2 * v ^ 8 + 112304956454245657286428756799409036802181710224870936302092383741525008443620976579157999681393293258875690782263409568123275556292346330758999123817945269580886471289600622935421089168630016540903606059012410443432741615263487970424657103982346621240576036755826921744406954322056968848400741572228187986964877135776929729700175937012771999725835861837499498423811217088091019935050322877782053383416567585724455100044378440621887350419692726918461236542976270630034981582273745396459080 * u ^ 3 * v ^ 7 + 258033910538482597906966478855230147040269557609756003166094484602468889497532581434150460600692412948602632886668394392326473663883865350343683756189760716327009973444581971911162738962828430663171899138904433028743378005135653208570510542944154301991362479549080938714205702356178985599931723653470449506044101976983390229181755996490821955289261368647616539633585656616861574618626499572383176161512913849707296923699267956663766642634942858100063538129552564403517540788111887335744556 * u ^ 4 * v ^ 6 + 384771797306048031766363969592882082680435448560489000846747867025181869012646612745180644215976944492938149410704993760801696947289088568063508217041534736626036257672370373913788532885707797568905055633477339716662425376068801120279426168476422041981208937384947985649379104613266579310011244631838692362475793423170124161398434653151858970507885558709833868167715674416794948408991719183919804198217055764621690993399689622097923750395294348446712016643602602747083561509675946369949096 * u ^ 5 * v ^ 5 + 384192021391738450765816211266939950799938208592915289441179792444150426142957689649105668373479367863994897370166843445390110528383487277360933957371806569142201729156760006896656258336031100112172045034313278394221507443724681926616706527994748772525910299838459263426301531078135558826079864612866467640549024035662673440588775254147269752584575321457722623301039887068268079402957785397188234247477909951760583693410370107335780044381970685696303733126303802017177938330827914304172702 * u ^ 6 * v ^ 4 + 256281462861738364820090109148838392308211858069174807469927069407259574174302267862988956880232250083438875766663347441433184793310562362062526178590229904277381781414440334657915730689569870194230782260091504775155281595273665806530553371106827949355787913173398723167143669618930333359944048010356079774925764970089287514086620532065367684168603482737042481332692356485341422986454014720074130884590755694384542289431529437438571175385187624991944135737852783694054515997892859296064056 * u ^ 7 * v ^ 3 + 110000981199480063490674859549395718923578380234678396295758708122730570360711250760722841677616912422839351745949690260705806669590152134774869561745055981735208744035145271155018915100689862738305557203024557536154532844151024270647875222767720333679774838685240894860911088878960372234830294797573903747448860601548960051759109577966612867605591929617147798867562169188685250900011173150477972627633320137805892669350649375469537409442507621174303685100711612119614768168915647184416540 * u ^ 8 * v ^ 2 + 27547711915700147109358075954181245282159361349142208991916984941364389012083923397799068998470468953342932231119768101315892378245114640968770037350394509054884787273562107788541006931727809251717864518507854453818647269385402949459340751151000170149827034508247300300063575990164086368827454915421260886114265619721648144220504423324026868849984037551368012133667049103493417759923790625697457880738168865645683430437970090852457157787486657910202762118875536203134405055305675992193664 * u ^ 9 * v + 3065424402192381645872493467971950588614360857729127919685971129947525306502724195005799289650488387592992665657487789379074240696770819096420503465077004600806841023181093315224656707312848867661080063868713307218659192082957822280204804507540678725436944163752426206221053727612290762786828562659144767905626376354179702670436352475135133444499699276105060371379417817685377572864908567030050022426109009488005260224268690077771340592322490455472998164786090624455292908799328891198181 * u ^ 10
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pDimLower := by
    dsimp only [pDimLower]
    positivity
  have hid : (d.im - 27 / 200) * y ^ 2 = pDimLower / 3920909730922167280627603467050960831505639859703864869193629171817253082107876733902331663916153897886033010403269082667780749707978665772546382392971481661552850057710697633575470189529459421850156197577518162831519483658214681717842796112659985444028693723953068783690862178918307939274280185345642094376693311338934035913592127867092493295125768097924203008981485676003844736571215612283467724062969473373343675825599036448820324417254220388819576331068110791015625000000000000000000 := by
    dsimp only [u, v, d, pDimLower]
    norm_num [leftMiddleCellZetaDerivApproxCenter,
      leftMiddleCellLogCpowSumCenter, leftMiddleCellLogCpowCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_im,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (d.im - 27 / 200) * y ^ 2 := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ d.im - 27 / 200 :=
    nonneg_of_mul_nonneg_left hscaled (pow_pos hyPos 2)
  dsimp only [d] at hnonneg ⊢
  linarith

/-- The rational derivative-center real part stays below `7/100` on the complete cell. -/
theorem leftMiddleCellZetaDerivApproxCenter_re_le_sevenHundredths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (leftMiddleCellZetaDerivApproxCenter y).re ≤ (7 / 100 : ℝ) := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let d : ℂ := leftMiddleCellZetaDerivApproxCenter y
  let pDreUpper : ℝ := 25091467164771365325853973768650822146868730256235260788223946221507678053913675219646276370976041830433467089288327756682983044742737176563378464969712050865548608524906251553392341379206922978981930318229082895713070929115891032710543218558866519965685186036839706270546669440590456769351488723080309976177918522079695288974923039357648919388217454732207523453894810620176688306827504578641550715439760613958514358155415307080733193074198706252523251776527810437968030929853585939536 * v ^ 10 + 486566329180155401300347079453549799050038408229691907913088727933430217642519006869745418982325183351477184644637339127457442545799241372517291757577618816454118269235667787380472850180416482342688474823781784599833774305053128100576631742487919418651278431185794355260133579355349504012217507099083416455492341609543212857322638895414304625043875016606144954588102809341118672152538839305623298080924055582710209539523712821751439797481276558942888802710072460934867001838708520757208 * u * v ^ 9 + 3318299574601463572202308458495905447372456695651183776970219096586088930820643652374628347880201042347767146553894655669311221071395479786640880354233722851117654637183648202923377453713420699062795511833968088315458954518017966736726271396040395551991348445146382608354707059649802925368339725499945500242977712101270983485462669817459135764653471367824844770894223653493538025542191547838006541998944443627556126522459827655009232511762466171319014911427792197478460142960766110522421 * u ^ 2 * v ^ 8 + 12049458243222918063967968225470231899589336479766479362063878664303435310942747872976457199648229648130947842331036178370568646465155741806103516105033633985114946520953692066833119382879154005494565133654775699130471611919523732358097144283827129503508097321572219004261204088830056184587242147771183766962249141773104038758492773178361315913570027995873874211947645116137791381429392408925826983320775433295194148457700162556423849318001090494342114854595097970295666895238009831795824 * u ^ 3 * v ^ 7 + 27036336075943499639591505874696739229198973559758258760871132958609582911363034546124724736102214080418294266126064346509295204069722909970951362334753343040839756641014353206300078704504713237900324493597508198469794109476100665417494017354771240286840824123040442740832376205523385016969776375523000916760217251047406072309945684353778494228149393676936815426364736197746184672281415422354246782423620500490613346931263816786604347687976377343890821204525739661582180526474950712353412 * u ^ 4 * v ^ 6 + 40019765777816921775736653640221914350259908738686435657803875261171625981993992551139565776011212298627148232300403323258128234642275470403185999087117943856384087630626210274630271649656732914406067358143090842675165341048734279099974581975753718432411155134021785063377808135087957463510337859602421440260869400182359954909068884030550318480283591451265178335567181236471082627529449198785666662413735723320798912609723770605148206644137151581798158640928162639098184817717367060240368 * u ^ 5 * v ^ 5 + 40042012646867316234016043541870363679001776273237654637394604712115051867976619950871929426269217631680694085480505362991178711067002003371738585444154492903892760730224157450798526737507236191017097259012266872842491675252021182943384028755015668898883325180259772749559825704076436755252264424947236098089909164315063867641586349381057908445796701174093831234190428708823199314742633759931394580399388447589227424680214279848321117631346241017594035606885718656391978647908610563862902 * u ^ 6 * v ^ 4 + 26930249487948920908260192899664381692993146900950196974206418589000305548225859029194547006464086453836102396077713099694478124387776609717499558384938468830763325670286404660285441233878473686697428491702264167289260541584683195970708974376233427737074963235007217392448750849914697893487874223343292586514279941093422098919835562696537139374842384071530009710658294068303030958352121432092263634410148819322728856930013835248379973563789749818704734687080486285451919807359936786617264 * u ^ 7 * v ^ 3 + 11704797491235602391727698599154597124541444064671901344321825363648983390009302070498893522941041230003017478019793115170171242588299336114068750984886854511282477138758670513371957818453167668820340870862583987518785896307236668784897295283793698190566358698151890065630664551078812674204357409456654522973650376095870506295094402462016937639309798860435167961089351620294591359830841149102362279297377978751384855181887609096050157391989171546788893844777879638201864031315269292387236 * u ^ 8 * v ^ 2 + 2978091479445341404443522211146912449885765737520610222807602463031127825277197047199070428046654151503015158497151597888664650191792007567776079394779813232387027063621570380924947731396475448131542872791605020867006883633105403087189029443151968278433367160640276205840716278828820470888760612432517394602821225615235991284014446605878840737495119916582306879135456950415630104965694932500076687139423543814909166836254514682051244362562295135092236799488569090766537489222683971639448 * u ^ 9 * v + 337594064245809165701612296598932809838356155788536651261169670126463809724633707179151419515211566001867624539842244967764867158600722143500426472595931372332056290366845404133194204927924642139628998670495111477463158032931339537115291992488729087969916083238850813183301966444664938278330525383922803874289435211302874008777176059771641348298845409348822441322529150351408195360166983548977581442644242956636038912152889300592479517130297924190673054772478142953465733447906063884381 * u ^ 10
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pDreUpper := by
    dsimp only [pDreUpper]
    positivity
  have hid : (7 / 100 - d.re) * y ^ 2 = pDreUpper / 245056858182635455039225216690685051969102491231491554324601823238578317631742295868895728994759618617877063150204317666736296856748666610784148899560717603847053128606918602098466886845591213865634762348594885176969967728638417607365174757041249090251793357747066798980678886182394246204642511584102630898543331958683377244599507991693280830945360506120262688061342854750240296035700975767716732753935592085833979739099939778051270276078388774301223520691756924438476562500000000000000 := by
    dsimp only [u, v, d, pDreUpper]
    norm_num [leftMiddleCellZetaDerivApproxCenter,
      leftMiddleCellLogCpowSumCenter, leftMiddleCellLogCpowCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_re,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (7 / 100 - d.re) * y ^ 2 := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ 7 / 100 - d.re :=
    nonneg_of_mul_nonneg_left hscaled (pow_pos hyPos 2)
  dsimp only [d] at hnonneg ⊢
  linarith

/-- The rational derivative-center imaginary part stays below `4/25` on the complete cell. -/
theorem leftMiddleCellZetaDerivApproxCenter_im_le_fourTwentyFifths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (leftMiddleCellZetaDerivApproxCenter y).im ≤ (4 / 25 : ℝ) := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let d : ℂ := leftMiddleCellZetaDerivApproxCenter y
  let pDimUpper : ℝ := 3433028095720910423793524898367262826468246628956534937721966823287020033312165424016792274394394314394901960643570096391284510511403224285239112114151028809566409408238379462415123486155296027884128620496924610573128914522601765939732918812737708637559959818303754599613335526017397266856941805149762715565079335246671987286587257572973197537058802544956942659542776228379497443669168738711634294071889588264427730540553276720483109488899822666296602307505433549120260200039539343379632 * v ^ 10 + 32188284796254224269484477358528044117583902616135804156679789512541981368080263689644858908986430332446360982715355243566940346416115469250541674771861155964138560117444514260012416880804829201181878971928816592355868630772271889504800715938112599413642143844815758805459216742633228492530500787827321686057980932656153213772901052881154364978326269002974384564027633564594592704163347245810182682512524159684454280965322456992421920576528867783108385228649277690612581478935112256993832 * u * v ^ 9 + 134908738302295490911362378668526764419814701695660369315561595245807369183306950437745087749169865238878753014285893843691208696054623248144335804176381252316708994013647013666374882330484011931762927827723171097900194668086954959144661289366216166156948008331271462019577313725497920761543460218783511070597666606135834623444267097880085357056359914670469297863902314280236104434816785913926061437884058765310902466552318064391326763806471731416745441337790739802501474911070540669824411 * u ^ 2 * v ^ 8 + 332522252518874220700772856537522469532133131858532533107924845801142353721517638882061527589894366456294754247987467860536450498077833301136387958664669324922284367757678023593716003833487154867996614556157025129803143805760967670464608114998928727384479266226648731765321359876225066862266345455234907620070979035625136644696850969508871364606182528872001332945138332854545165428954088335777359911527319168481384922369832244496778454717798576193119698216700898610687674667726254603540920 * u ^ 3 * v ^ 7 + 533107650418337705141668210708977474736780925081991330815450041540957351144784246548992510885989539797351677787451224762964987108443529935911862551152059995932816346949994043103527758529478244180643367627299294276586465810000614195047219642687814260977527196601549515115018013795062598847136160744646484086813190918430024867283295603891765879334740489311039522503653615658814197103030530596113523861292751640199123266010977622796954316656527460854006476071715490453660193586888112664255444 * u ^ 4 * v ^ 6 + 579968041987351227632057863475006829911527238919646950218344590700453251839996457631488061690592722081920272799019364029605756518359062145271529170749098326199042499027346778827455907248015693177325876780471004248032943578034921316395793815043567376522051153393704588577757534509583089148425394972456544958909595831774595375140908408546249004757809681784416282192178876163951049024355882218427429307476583158889520443488953296134317072470106578222344739615706057382310969740324053630050904 * u ^ 5 * v ^ 5 + 432680509674258575061937126049789601433868035678138657744447925139326537850692079400271354657652344836836504934724229064908661413902518003026947984423889491521565169741542461338373262275062652187534871778492911854690182982918619325774367007126550944919417678875613204295893468122257421472475483501581242196655318715412496266559224685363112569288689389643561021082640384956182923402447847226918722714490992707158404368905369148820324293897730454559394750747598729906039835106672085695827298 * u ^ 6 * v ^ 4 + 217952569093297767771818530190975320262395282962007648459042378924037186106645423102498057870426563865876816841612048107234896883869457263126958771839670802687435433065668544123037388734018246878545609836909317019316999953187399947242532818719397290099482592738724946220266110921239011895280140407199331539935291036354784129662347333459469379876858168706889872603618336027323597901834513585611290340825402110121375301674674021046247062881710331035783621504835216479285327752107140703935944 * u ^ 7 * v ^ 3 + 70654934652758793964241970194977301388043976301177177552337755968749365397409169753827089737319878422259619208380932723212191373204964890695205007011105035820838822373875122311970873881879980123440389600359591816307727365401217189501731608123088495653847224645896749347645386014700666067232164742226555750957283718392425652959647713509673760967327835494709854771259783333191895337507586185482802758567998347870917194313826228909859038082480583240558294353251592576430153706084352815583460 * u ^ 8 * v ^ 2 + 13229749285890392609169000103148747365499293191777985647696758445535043041837994634785180306257531584671811077074230358429027418717863483065712339536508900225264853326629147600643883039378568735523759936298334439629155360660029740406224328420663678468071380220864615050321390670586316199625059012173416895403344818203265829280853706493735061419323950667043699159740401926946567500416851742050606449516713657437090798148259888215274216151957234133520831724232816023428094944694324007806336 * u ^ 9 * v + 1076036501094157544290412694100626789663471244083079348399799682784448261473720605178538530360949167049129701580965179188769176182281646625831612937499122904208356850275831060239433680377642646668147419822540252272133262531031435284266648886456430899818363582173002696552419448870171998071629883112189694279755933747569372763295332584481312598476893277327379056857276427593683430138437923444362761115402496762588997366520292171295127073402279830217679334904601398554960997450671108801819 * u ^ 10
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ pDimUpper := by
    dsimp only [pDimUpper]
    positivity
  have hid : (4 / 25 - d.im) * y ^ 2 = pDimUpper / 3920909730922167280627603467050960831505639859703864869193629171817253082107876733902331663916153897886033010403269082667780749707978665772546382392971481661552850057710697633575470189529459421850156197577518162831519483658214681717842796112659985444028693723953068783690862178918307939274280185345642094376693311338934035913592127867092493295125768097924203008981485676003844736571215612283467724062969473373343675825599036448820324417254220388819576331068110791015625000000000000000000 := by
    dsimp only [u, v, d, pDimUpper]
    norm_num [leftMiddleCellZetaDerivApproxCenter,
      leftMiddleCellLogCpowSumCenter, leftMiddleCellLogCpowCenter,
      leftMiddleCellCpowCenter, leftMiddleCellRoundedCpowCenter,
      leftMiddleCellReflectedPoint, leftMiddleCellHeight, complexExpTaylor,
      heightTenBinaryIndex, binaryLogCenter, logAtanhPartial, Complex.div_im,
      Complex.normSq, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, pow_succ,
      Finset.sum_range_succ]
    field_simp
    ring
  have hscaled : 0 ≤ (4 / 25 - d.im) * y ^ 2 := by
    rw [hid]
    positivity
  have hnonneg : 0 ≤ 4 / 25 - d.im :=
    nonneg_of_mul_nonneg_left hscaled (pow_pos hyPos 2)
  dsimp only [d] at hnonneg ⊢
  linarith

/-- The finite rational quotient center has strictly negative imaginary part throughout the
complete cell. -/
theorem leftMiddleCellFiniteCenter_ratio_im_lt_neg_oneEighth
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (-leftMiddleCellZetaDerivApproxCenter y /
        leftMiddleCellZetaApproxCenter y).im < -(1 / 8 : ℝ) := by
  let z : ℂ := leftMiddleCellZetaApproxCenter y
  let d : ℂ := leftMiddleCellZetaDerivApproxCenter y
  have hzrLower : (7 / 8 : ℝ) ≤ z.re := by
    simpa only [z] using sevenEighths_le_leftMiddleCellZetaApproxCenter_re hy0 hy1
  have hzrUpper : z.re ≤ (19 / 20 : ℝ) := by
    simpa only [z] using leftMiddleCellZetaApproxCenter_re_le_nineteenTwentieths hy0 hy1
  have hziLower : -(3 / 10 : ℝ) ≤ z.im := by
    simpa only [z] using neg_threeTenths_le_leftMiddleCellZetaApproxCenter_im hy0 hy1
  have hziUpper : z.im ≤ -(1 / 4 : ℝ) := by
    simpa only [z] using leftMiddleCellZetaApproxCenter_im_le_neg_oneQuarter hy0 hy1
  have hdrLower : (7 / 200 : ℝ) ≤ d.re := by
    simpa only [d] using
      sevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_re hy0 hy1
  have hdiLower : (27 / 200 : ℝ) ≤ d.im := by
    simpa only [d] using
      twentySevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_im hy0 hy1
  have hzr0 : 0 ≤ z.re := by linarith
  have hdr0 : 0 ≤ d.re := by linarith
  have hdi0 : 0 ≤ d.im := by linarith
  have hnegZiLower : (1 / 4 : ℝ) ≤ -z.im := by linarith
  have hnegZiUpper : -z.im ≤ (3 / 10 : ℝ) := by linarith
  have hfirst : (189 / 1600 : ℝ) ≤ d.im * z.re := by
    calc
      (189 / 1600 : ℝ) = (27 / 200) * (7 / 8) := by norm_num
      _ ≤ d.im * z.re := mul_le_mul hdiLower hzrLower (by norm_num) hdi0
  have hsecond : (7 / 800 : ℝ) ≤ d.re * (-z.im) := by
    calc
      (7 / 800 : ℝ) = (7 / 200) * (1 / 4) := by norm_num
      _ ≤ d.re * (-z.im) :=
        mul_le_mul hdrLower hnegZiLower (by norm_num) hdr0
  have hcross : (203 / 1600 : ℝ) ≤ d.im * z.re - d.re * z.im := by
    nlinarith
  have hreSq : z.re ^ 2 ≤ (19 / 20 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzrUpper) (by linarith : 0 ≤ 19 / 20 + z.re)]
  have himSq : z.im ^ 2 ≤ (3 / 10 : ℝ) ^ 2 := by
    have hsq : (-z.im) ^ 2 ≤ (3 / 10 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnegZiUpper)
        (by linarith : 0 ≤ 3 / 10 + -z.im)]
    nlinarith
  have hnormUpper : Complex.normSq z ≤ (397 / 400 : ℝ) := by
    rw [Complex.normSq_apply]
    nlinarith
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at hzrLower
    norm_num at hzrLower
  have hzNorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hstrict : Complex.normSq z < 8 * (d.im * z.re - d.re * z.im) := by
    nlinarith
  change (-d / z).im < -(1 / 8 : ℝ)
  rw [Complex.div_im]
  norm_num only [Complex.neg_im, Complex.neg_re]
  rw [← sub_div]
  rw [div_lt_iff₀ hzNorm]
  nlinarith

/-- The exact second-corrected `N=4` finite quotient inherits a strict imaginary margin from
the rational cell centers. -/
theorem eulerMaclaurinTwoZetaFiniteRatio_leftMiddleCell_im_lt_neg_threeTwentyFifths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (-eulerMaclaurinTwoZetaDerivApprox (leftMiddleCellReflectedPoint y) 4 /
        eulerMaclaurinTwoZetaApprox (leftMiddleCellReflectedPoint y) 4).im <
      -(3 / 25 : ℝ) := by
  let z : ℂ := eulerMaclaurinTwoZetaApprox (leftMiddleCellReflectedPoint y) 4
  let d : ℂ := eulerMaclaurinTwoZetaDerivApprox (leftMiddleCellReflectedPoint y) 4
  let zc : ℂ := leftMiddleCellZetaApproxCenter y
  let dc : ℂ := leftMiddleCellZetaDerivApproxCenter y
  have hzBall : ‖z - zc‖ ≤ (1 / 50000 : ℝ) := by
    simpa only [z, zc] using
      norm_eulerMaclaurinTwoZetaApprox_leftMiddleCell_sub_center_le hy0 hy1
  have hdBall : ‖d - dc‖ ≤ (1 / 25000 : ℝ) := by
    simpa only [d, dc] using
      norm_eulerMaclaurinTwoZetaDerivApprox_leftMiddleCell_sub_center_le hy0 hy1
  have hzReAbs : |z.re - zc.re| ≤ (1 / 50000 : ℝ) := by
    have h := Complex.abs_re_le_norm (z - zc)
    rw [Complex.sub_re] at h
    exact h.trans hzBall
  have hzImAbs : |z.im - zc.im| ≤ (1 / 50000 : ℝ) := by
    have h := Complex.abs_im_le_norm (z - zc)
    rw [Complex.sub_im] at h
    exact h.trans hzBall
  have hdReAbs : |d.re - dc.re| ≤ (1 / 25000 : ℝ) := by
    have h := Complex.abs_re_le_norm (d - dc)
    rw [Complex.sub_re] at h
    exact h.trans hdBall
  have hdImAbs : |d.im - dc.im| ≤ (1 / 25000 : ℝ) := by
    have h := Complex.abs_im_le_norm (d - dc)
    rw [Complex.sub_im] at h
    exact h.trans hdBall
  have hzcReLower : (7 / 8 : ℝ) ≤ zc.re := by
    simpa only [zc] using sevenEighths_le_leftMiddleCellZetaApproxCenter_re hy0 hy1
  have hzcReUpper : zc.re ≤ (19 / 20 : ℝ) := by
    simpa only [zc] using leftMiddleCellZetaApproxCenter_re_le_nineteenTwentieths hy0 hy1
  have hzcImLower : -(3 / 10 : ℝ) ≤ zc.im := by
    simpa only [zc] using neg_threeTenths_le_leftMiddleCellZetaApproxCenter_im hy0 hy1
  have hzcImUpper : zc.im ≤ -(1 / 4 : ℝ) := by
    simpa only [zc] using leftMiddleCellZetaApproxCenter_im_le_neg_oneQuarter hy0 hy1
  have hdcReLower : (7 / 200 : ℝ) ≤ dc.re := by
    simpa only [dc] using
      sevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_re hy0 hy1
  have hdcImLower : (27 / 200 : ℝ) ≤ dc.im := by
    simpa only [dc] using
      twentySevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_im hy0 hy1
  have hzrLower : (437 / 500 : ℝ) ≤ z.re := by
    rcases abs_le.mp hzReAbs with ⟨hleft, _⟩
    linarith
  have hzrUpper : z.re ≤ (951 / 1000 : ℝ) := by
    rcases abs_le.mp hzReAbs with ⟨_, hright⟩
    linarith
  have hziLower : -(301 / 1000 : ℝ) ≤ z.im := by
    rcases abs_le.mp hzImAbs with ⟨hleft, _⟩
    linarith
  have hziUpper : z.im ≤ -(249 / 1000 : ℝ) := by
    rcases abs_le.mp hzImAbs with ⟨_, hright⟩
    linarith
  have hdrLower : (349 / 10000 : ℝ) ≤ d.re := by
    rcases abs_le.mp hdReAbs with ⟨hleft, _⟩
    linarith
  have hdiLower : (1349 / 10000 : ℝ) ≤ d.im := by
    rcases abs_le.mp hdImAbs with ⟨hleft, _⟩
    linarith
  have hzr0 : 0 ≤ z.re := by linarith
  have hdr0 : 0 ≤ d.re := by linarith
  have hdi0 : 0 ≤ d.im := by linarith
  have hnegZiLower : (249 / 1000 : ℝ) ≤ -z.im := by linarith
  have hnegZiUpper : -z.im ≤ (301 / 1000 : ℝ) := by linarith
  have hfirst : (589513 / 5000000 : ℝ) ≤ d.im * z.re := by
    calc
      (589513 / 5000000 : ℝ) = (1349 / 10000) * (437 / 500) := by norm_num
      _ ≤ d.im * z.re := mul_le_mul hdiLower hzrLower (by norm_num) hdi0
  have hsecond : (86901 / 10000000 : ℝ) ≤ d.re * (-z.im) := by
    calc
      (86901 / 10000000 : ℝ) = (349 / 10000) * (249 / 1000) := by norm_num
      _ ≤ d.re * (-z.im) :=
        mul_le_mul hdrLower hnegZiLower (by norm_num) hdr0
  have hcross : (1265927 / 10000000 : ℝ) ≤ d.im * z.re - d.re * z.im := by
    nlinarith
  have hreSq : z.re ^ 2 ≤ (951 / 1000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzrUpper)
      (by linarith : 0 ≤ 951 / 1000 + z.re)]
  have himSq : z.im ^ 2 ≤ (301 / 1000 : ℝ) ^ 2 := by
    have hsq : (-z.im) ^ 2 ≤ (301 / 1000 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hnegZiUpper)
        (by linarith : 0 ≤ 301 / 1000 + -z.im)]
    nlinarith
  have hnormUpper : Complex.normSq z ≤ (497501 / 500000 : ℝ) := by
    rw [Complex.normSq_apply]
    nlinarith
  have hz : z ≠ 0 := by
    intro hz
    rw [hz] at hzrLower
    norm_num at hzrLower
  have hzNorm : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hstrict : 3 * Complex.normSq z < 25 * (d.im * z.re - d.re * z.im) := by
    nlinarith
  change (-d / z).im < -(3 / 25 : ℝ)
  rw [Complex.div_im]
  norm_num only [Complex.neg_im, Complex.neg_re]
  rw [← sub_div]
  rw [div_lt_iff₀ hzNorm]
  nlinarith

/-- The rational part of the paired twice-shifted archimedean center on the imaginary axis. -/
def leftMiddleCellArchimedeanRationalImag (y : ℝ) : ℝ :=
  y / (2 * (y ^ 2 + 49)) - y / (2 * (y ^ 2 + 36)) +
    y / (y ^ 2 + 25) - y / (y ^ 2 + 16) +
    y / (y ^ 2 + 9) - y / (y ^ 2 + 4) +
    y / (y ^ 2 + 1) - 1 / y

private theorem arg_ofReal_add_ofReal_mul_I_eq_arctan_div
    {a b : ℝ} (ha : 0 < a) :
    Complex.arg ((a : ℂ) + (b : ℂ) * I) = Real.arctan (b / a) := by
  let z : ℂ := (a : ℂ) + (b : ℂ) * I
  have hzRe : z.re = a := by norm_num [z, Complex.mul_re]
  have hzRePos : 0 < z.re := by simpa only [hzRe] using ha
  have htan : Real.tan (Complex.arg z) = b / a := by
    rw [Complex.tan_arg]
    norm_num [z, Complex.mul_re, Complex.mul_im, hzRe, ha.ne']
  exact (Real.arctan_eq_of_tan_eq htan ⟨
    Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hzRePos),
    Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hzRePos)⟩).symm

/-- Exact angle-plus-rational formula for the imaginary part of the paired archimedean center. -/
theorem leftMiddleCellArchimedeanComplex_im_eq
    {y : ℝ} (hy : y ≠ 0) :
    (levinsonMontgomeryArchimedeanComplexShiftTwoApprox ((y : ℂ) * I) +
        levinsonMontgomeryArchimedeanComplexShiftTwoApprox (1 - (y : ℂ) * I)).im =
      -(Real.arctan (y / 6) - Real.arctan (y / 7)) / 2 +
        leftMiddleCellArchimedeanRationalImag y := by
  have hargPos :
      Complex.arg (((((y : ℂ) * I) / 2 + 1) + 2)) = Real.arctan (y / 6) := by
    have hW : ((((y : ℂ) * I) / 2 + 1) + 2) =
        (3 : ℂ) + ((y / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;>
        norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    rw [hW]
    have harg := arg_ofReal_add_ofReal_mul_I_eq_arctan_div
      (a := 3) (b := y / 2) (by norm_num)
    rw [show (y / 2) / 3 = y / 6 by ring] at harg
    simpa using harg
  have hargNeg :
      Complex.arg ((((1 - (y : ℂ) * I) / 2 + 1) + 2)) =
        -Real.arctan (y / 7) := by
    have hW : (((1 - (y : ℂ) * I) / 2 + 1) + 2) =
        ((7 / 2 : ℝ) : ℂ) + ((-y / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;>
        norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    rw [hW]
    have harg := arg_ofReal_add_ofReal_mul_I_eq_arctan_div
      (a := 7 / 2) (b := -y / 2) (by norm_num)
    rw [show (-y / 2) / (7 / 2) = -(y / 7) by ring] at harg
    simpa only [Real.arctan_neg] using harg
  unfold levinsonMontgomeryArchimedeanComplexShiftTwoApprox
    leftMiddleCellArchimedeanRationalImag
  norm_num [Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.div_im,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.log_im,
    hargPos, hargNeg]
  field_simp
  ring

/-- The rational archimedean correction is uniformly at most `-3/80` on the middle cell. -/
theorem leftMiddleCellArchimedeanRationalImag_le_neg_threeEightieths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    leftMiddleCellArchimedeanRationalImag y ≤ -(3 / 80 : ℝ) := by
  let u : ℝ := 2 * y - 12
  let v : ℝ := 13 - 2 * y
  let p : ℝ :=
    143723197366272000 * v ^ 15 +
    2140129219785523200 * u * v ^ 14 +
    14810645573192908800 * u ^ 2 * v ^ 13 +
    63152082383067414528 * u ^ 3 * v ^ 12 +
    185412066745812893696 * u ^ 4 * v ^ 11 +
    396670047507663597568 * u ^ 5 * v ^ 10 +
    638087274681120363520 * u ^ 6 * v ^ 9 +
    784695132762742722816 * u ^ 7 * v ^ 8 +
    742288998264960774144 * u ^ 8 * v ^ 7 +
    538625441048482917120 * u ^ 9 * v ^ 6 +
    296177973991655606912 * u ^ 10 * v ^ 5 +
    120476180056846006624 * u ^ 11 * v ^ 4 +
    34756382908778752192 * u ^ 12 * v ^ 3 +
    6600954626706326080 * u ^ 13 * v ^ 2 +
    713157338711531300 * u ^ 14 * v +
    30255096304594625 * u ^ 15
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hv : 0 ≤ v := by dsimp only [v]; linarith
  have hyPos : 0 < y := by linarith
  have hp : 0 ≤ p := by
    dsimp only [p]
    positivity
  let q : ℝ :=
    80 * y * (y ^ 2 + 1) * (y ^ 2 + 4) * (y ^ 2 + 9) *
      (y ^ 2 + 16) * (y ^ 2 + 25) * (y ^ 2 + 36) * (y ^ 2 + 49)
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hid :
      (-(3 / 80 : ℝ) - leftMiddleCellArchimedeanRationalImag y) * q =
        p / 32768 := by
    dsimp only [u, v, p, q, leftMiddleCellArchimedeanRationalImag]
    field_simp
    ring
  have hscaled :
      0 ≤ (-(3 / 80 : ℝ) - leftMiddleCellArchimedeanRationalImag y) * q := by
    rw [hid]
    positivity
  have hnonneg :
      0 ≤ -(3 / 80 : ℝ) - leftMiddleCellArchimedeanRationalImag y :=
    nonneg_of_mul_nonneg_left hscaled hq
  linarith

/-- The paired logarithmic angles retain a fixed positive gap on the middle cell. -/
theorem oneTwentieth_le_arctan_six_sub_arctan_seven
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (1 / 20 : ℝ) ≤ Real.arctan (y / 6) - Real.arctan (y / 7) := by
  let r : ℝ := y / (42 + y ^ 2)
  have hyPos : 0 < y := by linarith
  have hrDen : 0 < 42 + y ^ 2 := by positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hrLower : (1 / 13 : ℝ) ≤ r := by
    rw [show r = y / (42 + y ^ 2) by rfl, le_div_iff₀ hrDen]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ y - 6 by linarith) (show y - 7 ≤ 0 by linarith)]
  have hx0 : 0 ≤ y / 7 := by positivity
  have hx1 : y / 7 < (1 : ℝ) := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 7)]
    linarith
  have hr1 : r < (1 : ℝ) := by
    rw [show r = y / (42 + y ^ 2) by rfl, div_lt_one hrDen]
    nlinarith [sq_nonneg (y - 1 / 2)]
  have hprod : (y / 7) * r < (1 : ℝ) :=
    mul_lt_one_of_nonneg_of_lt_one_left hx0 hx1 hr1.le
  have hadd := Real.arctan_add (x := y / 7) (y := r) hprod
  have hratio : ((y / 7 + r) / (1 - (y / 7) * r)) = y / 6 := by
    have hsub : 1 - (y / 7) * r ≠ 0 := by linarith
    rw [div_eq_iff hsub]
    dsimp only [r]
    field_simp [hrDen.ne']
    ring
  rw [hratio] at hadd
  have hdiff :
      Real.arctan (y / 6) - Real.arctan (y / 7) = Real.arctan r := by
    linarith
  rw [hdiff]
  have hmono : Real.arctan (1 / 13) ≤ Real.arctan r :=
    Real.arctan_le_arctan_iff.mpr hrLower
  exact (show (1 / 20 : ℝ) ≤ 13 / 170 by norm_num).trans
    (arctan_one_div_thirteen_ge_thirteen_div_oneHundredSeventy.trans hmono)

/-- The paired archimedean center contributes a uniform negative imaginary margin. -/
theorem leftMiddleCellArchimedeanComplex_im_lt_neg_threeFiftieths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (levinsonMontgomeryArchimedeanComplexShiftTwoApprox ((y : ℂ) * I) +
        levinsonMontgomeryArchimedeanComplexShiftTwoApprox (1 - (y : ℂ) * I)).im <
      -(3 / 50 : ℝ) := by
  rw [leftMiddleCellArchimedeanComplex_im_eq (by linarith : y ≠ 0)]
  have hangle := oneTwentieth_le_arctan_six_sub_arctan_seven hy0 hy1
  have hrational := leftMiddleCellArchimedeanRationalImag_le_neg_threeEightieths hy0 hy1
  linarith

/-- The complete reflected finite phase center has a uniform negative imaginary margin on the
middle cell. -/
theorem leftLowMiddlePhaseCenter_four_im_lt_neg_nineFiftieths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (leftLowMiddlePhaseCenter y 4).im < -(9 / 50 : ℝ) := by
  have hfinite :=
    eulerMaclaurinTwoZetaFiniteRatio_leftMiddleCell_im_lt_neg_threeTwentyFifths
      hy0 hy1
  have harch := leftMiddleCellArchimedeanComplex_im_lt_neg_threeFiftieths hy0 hy1
  unfold leftLowMiddlePhaseCenter
  simp only [Complex.add_im, Complex.neg_im]
  norm_num [leftMiddleCellReflectedPoint] at hfinite
  rw [neg_div, Complex.neg_im] at hfinite
  rw [Complex.add_im] at harch
  linarith

/-- The second-corrected `N=4` value remainder has a uniform radius on the middle cell. -/
theorem eulerMaclaurinTwoZetaError_leftMiddleCell_four_le_sevenTwoHundredths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    eulerMaclaurinTwoZetaError (leftMiddleCellReflectedPoint y) 4 ≤
      (7 / 200 : ℝ) := by
  let s : ℂ := leftMiddleCellReflectedPoint y
  have hyNonneg : 0 ≤ y := by linarith
  have hySq : y ^ 2 ≤ (13 / 2 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hyNonneg hy1
  have hnormSq :
      ‖s * (s + 1) * (s + 2)‖ ^ 2 =
        (1 + y ^ 2) * (4 + y ^ 2) * (9 + y ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [s, leftMiddleCellReflectedPoint, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  have hpoly :
      (1 + y ^ 2) * (4 + y ^ 2) * (9 + y ^ 2) < (322 : ℝ) ^ 2 := by
    calc
      (1 + y ^ 2) * (4 + y ^ 2) * (9 + y ^ 2) ≤
          (173 / 4 : ℝ) * (185 / 4) * (205 / 4) := by
        gcongr <;> nlinarith
      _ < (322 : ℝ) ^ 2 := by norm_num
  have hnorm : ‖s * (s + 1) * (s + 2)‖ ≤ (322 : ℝ) := by
    nlinarith [norm_nonneg (s * (s + 1) * (s + 2))]
  rw [norm_mul, norm_mul] at hnorm
  dsimp only [s] at hnorm
  have hnorm' :
      ‖1 - (y : ℂ) * I‖ * ‖1 - (y : ℂ) * I + 1‖ *
          ‖1 - (y : ℂ) * I + 2‖ ≤ (322 : ℝ) := by
    simpa only [leftMiddleCellReflectedPoint] using hnorm
  unfold eulerMaclaurinTwoZetaError
  norm_num [leftMiddleCellReflectedPoint]
  nlinarith

/-- The second-corrected `N=4` derivative remainder has a uniform radius on the middle cell. -/
theorem eulerMaclaurinTwoZetaDerivError_leftMiddleCell_four_le_threeFortieths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    eulerMaclaurinTwoZetaDerivError (leftMiddleCellReflectedPoint y) 4 ≤
      (3 / 40 : ℝ) := by
  let s : ℂ := leftMiddleCellReflectedPoint y
  let P : ℂ := s * (s + 1) * (s + 2)
  let Q : ℂ := 3 * s ^ 2 + 6 * s + 2
  have hyNonneg : 0 ≤ y := by linarith
  have hySq : y ^ 2 ≤ (13 / 2 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hyNonneg hy1
  have hPSq : ‖P‖ ^ 2 = (1 + y ^ 2) * (4 + y ^ 2) * (9 + y ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [P, s, leftMiddleCellReflectedPoint, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  have hPPoly :
      (1 + y ^ 2) * (4 + y ^ 2) * (9 + y ^ 2) < (1601 / 5 : ℝ) ^ 2 := by
    calc
      (1 + y ^ 2) * (4 + y ^ 2) * (9 + y ^ 2) ≤
          (173 / 4 : ℝ) * (185 / 4) * (205 / 4) := by
        gcongr <;> nlinarith
      _ < (1601 / 5 : ℝ) ^ 2 := by norm_num
  have hP : ‖P‖ ≤ (1601 / 5 : ℝ) := by
    nlinarith [norm_nonneg P]
  have hQSq : ‖Q‖ ^ 2 = 9 * (y ^ 2) ^ 2 + 78 * y ^ 2 + 121 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [Q, s, leftMiddleCellReflectedPoint, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im, pow_succ]
    ring
  have hQPoly :
      9 * (y ^ 2) ^ 2 + 78 * y ^ 2 + 121 < (698 / 5 : ℝ) ^ 2 := by
    have hmono :
        0 ≤ ((13 / 2 : ℝ) ^ 2 - y ^ 2) *
          (9 * ((13 / 2 : ℝ) ^ 2 + y ^ 2) + 78) := by positivity
    nlinarith
  have hQ : ‖Q‖ ≤ (698 / 5 : ℝ) := by
    nlinarith [norm_nonneg Q]
  have hlogTwo : Real.log 2 ≤ (1387 / 2000 : ℝ) := by
    have h := abs_log_two_sub_logAtanhPartial_eight_le
    have hupper := (abs_le.mp h).2
    have hcert :
        logAtanhPartial 8 (1 / 3) + (1 / 10000000 : ℝ) ≤ 1387 / 2000 := by
      norm_num [logAtanhPartial, Finset.sum_range_succ]
    linarith
  have hlogFour : Real.log 4 ≤ (1387 / 1000 : ℝ) := by
    have hlogEq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul] <;> norm_num
      ring
    rw [hlogEq]
    linarith
  have hlogFour0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlogFactor :
      Real.log 4 / 3 + 1 / 3 ^ 2 ≤ (1387 / 1000 : ℝ) / 3 + 1 / 9 := by
    nlinarith
  have hP' :
      ‖leftMiddleCellReflectedPoint y * (leftMiddleCellReflectedPoint y + 1) *
          (leftMiddleCellReflectedPoint y + 2)‖ ≤ (1601 / 5 : ℝ) := by
    simpa only [P, s] using hP
  have hQ' :
      ‖3 * leftMiddleCellReflectedPoint y ^ 2 +
          6 * leftMiddleCellReflectedPoint y + 2‖ ≤ (698 / 5 : ℝ) := by
    simpa only [Q, s] using hQ
  unfold eulerMaclaurinTwoZetaDerivError
  norm_num [leftMiddleCellReflectedPoint]
  rw [show (1 / 48 : ℝ) * (1 / 64 * (Real.log 4 / 3 + 1 / 9)) =
      1 / 3072 * (Real.log 4 / 3 + 1 / 9) by ring]
  calc
    ‖3 * (1 - (y : ℂ) * I) ^ 2 + 6 * (1 - (y : ℂ) * I) + 2‖ * (1 / 9216) +
        ‖1 - (y : ℂ) * I‖ * ‖1 - (y : ℂ) * I + 1‖ *
          ‖1 - (y : ℂ) * I + 2‖ *
            (1 / 3072 * (Real.log 4 / 3 + 1 / 9)) ≤
        (698 / 5 : ℝ) * (1 / 9216) +
          (1601 / 5) * (1 / 3072 * ((1387 / 1000) / 3 + 1 / 9)) := by
      gcongr
      · exact hQ'
      · rw [← norm_mul, ← norm_mul]
        exact hP'
    _ ≤ 3 / 40 := by norm_num

/-- The exact `N=4` derivative center remains uniformly bounded on the middle cell. -/
theorem norm_eulerMaclaurinTwoZetaDerivApprox_leftMiddleCell_four_le_nineFiftieths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    ‖eulerMaclaurinTwoZetaDerivApprox (leftMiddleCellReflectedPoint y) 4‖ ≤
      (9 / 50 : ℝ) := by
  let d : ℂ := eulerMaclaurinTwoZetaDerivApprox (leftMiddleCellReflectedPoint y) 4
  let dc : ℂ := leftMiddleCellZetaDerivApproxCenter y
  have hdBall : ‖d - dc‖ ≤ (1 / 25000 : ℝ) := by
    simpa only [d, dc] using
      norm_eulerMaclaurinTwoZetaDerivApprox_leftMiddleCell_sub_center_le hy0 hy1
  have hdReAbs : |d.re - dc.re| ≤ (1 / 25000 : ℝ) := by
    have h := Complex.abs_re_le_norm (d - dc)
    rw [Complex.sub_re] at h
    exact h.trans hdBall
  have hdImAbs : |d.im - dc.im| ≤ (1 / 25000 : ℝ) := by
    have h := Complex.abs_im_le_norm (d - dc)
    rw [Complex.sub_im] at h
    exact h.trans hdBall
  have hdcReLower : (7 / 200 : ℝ) ≤ dc.re := by
    simpa only [dc] using
      sevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_re hy0 hy1
  have hdcReUpper : dc.re ≤ (7 / 100 : ℝ) := by
    simpa only [dc] using
      leftMiddleCellZetaDerivApproxCenter_re_le_sevenHundredths hy0 hy1
  have hdcImLower : (27 / 200 : ℝ) ≤ dc.im := by
    simpa only [dc] using
      twentySevenTwoHundredths_le_leftMiddleCellZetaDerivApproxCenter_im hy0 hy1
  have hdcImUpper : dc.im ≤ (4 / 25 : ℝ) := by
    simpa only [dc] using
      leftMiddleCellZetaDerivApproxCenter_im_le_fourTwentyFifths hy0 hy1
  have hdrLower : 0 ≤ d.re := by
    rcases abs_le.mp hdReAbs with ⟨hleft, _⟩
    linarith
  have hdrUpper : d.re ≤ (71 / 1000 : ℝ) := by
    rcases abs_le.mp hdReAbs with ⟨_, hright⟩
    linarith
  have hdiLower : 0 ≤ d.im := by
    rcases abs_le.mp hdImAbs with ⟨hleft, _⟩
    linarith
  have hdiUpper : d.im ≤ (161 / 1000 : ℝ) := by
    rcases abs_le.mp hdImAbs with ⟨_, hright⟩
    linarith
  have hreSq : d.re ^ 2 ≤ (71 / 1000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdrUpper)
      (by linarith : 0 ≤ 71 / 1000 + d.re)]
  have himSq : d.im ^ 2 ≤ (161 / 1000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiUpper)
      (by linarith : 0 ≤ 161 / 1000 + d.im)]
  have hnormSq : ‖d‖ ^ 2 ≤ (9 / 50 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hnorm : ‖d‖ ≤ (9 / 50 : ℝ) := by
    nlinarith [norm_nonneg d]
  simpa only [d] using hnorm

/-- The two twice-shifted Stirling radii have a uniform rational sum on the middle cell. -/
theorem leftMiddleCellArchimedeanShiftTwoErrors_le
    {y : ℝ} (hy0 : 6 ≤ y) (_hy1 : y ≤ 13 / 2) :
    levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) +
        levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I) ≤
      (471 / 21760 : ℝ) := by
  have hsSq :
      ‖((((y : ℂ) * I) / 2 + 1) + 2)‖ ^ 2 = 9 + y ^ 2 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    ring
  have hwSq :
      ‖(((1 - (y : ℂ) * I) / 2 + 1) + 2)‖ ^ 2 = 49 / 4 + y ^ 2 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
    ring
  have hfirst :
      levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) ≤
        (3 / 256 : ℝ) := by
    unfold levinsonMontgomeryArchimedeanShiftTwoError
    rw [hsSq]
    rw [div_le_iff₀ (by positivity : 0 < (128 : ℝ) * (9 + y ^ 2 / 4))]
    nlinarith [sq_nonneg y]
  have hsecond :
      levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I) ≤
        (27 / 2720 : ℝ) := by
    unfold levinsonMontgomeryArchimedeanShiftTwoError
    rw [hwSq]
    rw [div_le_iff₀ (by positivity : 0 < (128 : ℝ) * (49 / 4 + y ^ 2 / 4))]
    nlinarith [sq_nonneg y]
  calc
    levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I) +
        levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I) ≤
        (3 / 256 : ℝ) + 27 / 2720 := add_le_add hfirst hsecond
    _ = 471 / 21760 := by norm_num

/-- The exact `N=4` value center stays uniformly separated from zero on the middle cell. -/
theorem fourHundredThirtySevenFiveHundredths_le_norm_eulerMaclaurinTwoZetaApprox_leftMiddleCell
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (437 / 500 : ℝ) ≤
      ‖eulerMaclaurinTwoZetaApprox (leftMiddleCellReflectedPoint y) 4‖ := by
  let z : ℂ := eulerMaclaurinTwoZetaApprox (leftMiddleCellReflectedPoint y) 4
  let zc : ℂ := leftMiddleCellZetaApproxCenter y
  have hzBall : ‖z - zc‖ ≤ (1 / 50000 : ℝ) := by
    simpa only [z, zc] using
      norm_eulerMaclaurinTwoZetaApprox_leftMiddleCell_sub_center_le hy0 hy1
  have hzReAbs : |z.re - zc.re| ≤ (1 / 50000 : ℝ) := by
    have h := Complex.abs_re_le_norm (z - zc)
    rw [Complex.sub_re] at h
    exact h.trans hzBall
  have hzcRe : (7 / 8 : ℝ) ≤ zc.re := by
    simpa only [zc] using sevenEighths_le_leftMiddleCellZetaApproxCenter_re hy0 hy1
  have hzRe : (437 / 500 : ℝ) ≤ z.re := by
    rcases abs_le.mp hzReAbs with ⟨hleft, _⟩
    linarith
  have hreNorm := Complex.abs_re_le_norm z
  rw [abs_of_nonneg (by linarith : 0 ≤ z.re)] at hreNorm
  exact hzRe.trans hreNorm

/-- The complete reflected finite phase radius is at most `3/25` on the middle cell. -/
theorem leftLowMiddlePhaseError_four_le_threeTwentyFifths
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    leftLowMiddlePhaseError y 4 ≤ (3 / 25 : ℝ) := by
  let Z : ℂ := eulerMaclaurinTwoZetaApprox (leftMiddleCellReflectedPoint y) 4
  let D : ℂ := eulerMaclaurinTwoZetaDerivApprox (leftMiddleCellReflectedPoint y) 4
  let ez : ℝ := eulerMaclaurinTwoZetaError (leftMiddleCellReflectedPoint y) 4
  let ed : ℝ := eulerMaclaurinTwoZetaDerivError (leftMiddleCellReflectedPoint y) 4
  let a : ℝ := levinsonMontgomeryArchimedeanShiftTwoError ((y : ℂ) * I)
  let b : ℝ := levinsonMontgomeryArchimedeanShiftTwoError (1 - (y : ℂ) * I)
  have hZ : (437 / 500 : ℝ) ≤ ‖Z‖ := by
    simpa only [Z] using
      fourHundredThirtySevenFiveHundredths_le_norm_eulerMaclaurinTwoZetaApprox_leftMiddleCell
        hy0 hy1
  have hD : ‖D‖ ≤ (9 / 50 : ℝ) := by
    simpa only [D] using
      norm_eulerMaclaurinTwoZetaDerivApprox_leftMiddleCell_four_le_nineFiftieths
        hy0 hy1
  have hez : ez ≤ (7 / 200 : ℝ) := by
    simpa only [ez] using
      eulerMaclaurinTwoZetaError_leftMiddleCell_four_le_sevenTwoHundredths hy0 hy1
  have hed : ed ≤ (3 / 40 : ℝ) := by
    simpa only [ed] using
      eulerMaclaurinTwoZetaDerivError_leftMiddleCell_four_le_threeFortieths hy0 hy1
  have hez0 : 0 ≤ ez := by
    dsimp only [ez]
    unfold eulerMaclaurinTwoZetaError
    norm_num [leftMiddleCellReflectedPoint]
    positivity
  have hgap : (839 / 1000 : ℝ) ≤ ‖Z‖ - ez := by
    linarith
  have hgapPos : 0 < ‖Z‖ - ez := (by norm_num : (0 : ℝ) < 839 / 1000).trans_le hgap
  have hfirst :
      ed / (‖Z‖ - ez) ≤ (3 / 40 : ℝ) / (839 / 1000) :=
    div_le_div₀ (by norm_num) hed (by norm_num) hgap
  have hnum : ‖D‖ * ez ≤ (9 / 50 : ℝ) * (7 / 200) :=
    mul_le_mul hD hez hez0 (by norm_num)
  have hden :
      (839 / 1000 : ℝ) * (437 / 500) ≤ (‖Z‖ - ez) * ‖Z‖ :=
    mul_le_mul hgap hZ (by norm_num) hgapPos.le
  have hsecond :
      ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) ≤
        ((9 / 50 : ℝ) * (7 / 200)) / ((839 / 1000) * (437 / 500)) :=
    div_le_div₀ (by norm_num) hnum (by norm_num) hden
  have harch : a + b ≤ (471 / 21760 : ℝ) := by
    simpa only [a, b] using leftMiddleCellArchimedeanShiftTwoErrors_le hy0 hy1
  have htotal :
      ed / (‖Z‖ - ez) + ‖D‖ * ez / ((‖Z‖ - ez) * ‖Z‖) + a + b ≤
        (3 / 40 : ℝ) / (839 / 1000) +
          ((9 / 50) * (7 / 200)) / ((839 / 1000) * (437 / 500)) +
          471 / 21760 := by
    linarith
  have hnumeric :
      (3 / 40 : ℝ) / (839 / 1000) +
          ((9 / 50) * (7 / 200)) / ((839 / 1000) * (437 / 500)) +
          471 / 21760 ≤ 3 / 25 := by norm_num
  have hfinal := htotal.trans hnumeric
  simpa only [leftLowMiddlePhaseError, Z, D, ez, ed, a, b,
    leftMiddleCellReflectedPoint] using hfinal

/-- The middle-cell phase center dominates the complete certified error radius. -/
theorem leftLowMiddlePhaseCenter_four_im_lt_neg_error
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (leftLowMiddlePhaseCenter y 4).im < -leftLowMiddlePhaseError y 4 := by
  have hcenter := leftLowMiddlePhaseCenter_four_im_lt_neg_nineFiftieths hy0 hy1
  have herror := leftLowMiddlePhaseError_four_le_threeTwentyFifths hy0 hy1
  linarith

/-- The actual imaginary-axis zeta logarithmic derivative has negative imaginary part on the
complete middle cell `[6,13/2]`. -/
theorem speiserZetaDerivRatio_leftVertical_im_neg_six_thirteenHalves
    {y : ℝ} (hy0 : 6 ≤ y) (hy1 : y ≤ 13 / 2) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).im < 0 := by
  have hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) 4 <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) 4‖ := by
    have he := eulerMaclaurinTwoZetaError_leftMiddleCell_four_le_sevenTwoHundredths
      hy0 hy1
    have hz :=
      fourHundredThirtySevenFiveHundredths_le_norm_eulerMaclaurinTwoZetaApprox_leftMiddleCell
        hy0 hy1
    norm_num [leftMiddleCellReflectedPoint] at he hz ⊢
    linarith
  exact speiserZetaDerivRatio_leftVertical_im_neg_of_phaseMargin
    y (by linarith) (by norm_num) hzMargin
      (leftLowMiddlePhaseCenter_four_im_lt_neg_error hy0 hy1)

/-- A pointwise phase ball and a finite-center variation bound give one fixed-center ball. -/
theorem norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_at_le
    (y c : ℝ) (hy : 0 < y) {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    {variation : ℝ}
    (hvariation :
      ‖leftLowMiddlePhaseCenter y N - leftLowMiddlePhaseCenter c N‖ ≤ variation) :
    ‖speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter c N‖ ≤
      leftLowMiddlePhaseError y N + variation := by
  have hpoint := norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_le
    y hy hN hzMargin
  calc
    ‖speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter c N‖ =
        ‖(speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter y N) +
          (leftLowMiddlePhaseCenter y N - leftLowMiddlePhaseCenter c N)‖ := by
      congr 1
      ring
    _ ≤ ‖speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter y N‖ +
        ‖leftLowMiddlePhaseCenter y N - leftLowMiddlePhaseCenter c N‖ := norm_add_le _ _
    _ ≤ leftLowMiddlePhaseError y N + variation := add_le_add hpoint hvariation

/-- Uniform error and variation budgets reduce a complete cell to one fixed-center real margin. -/
theorem speiserZetaDerivRatio_leftVertical_re_pos_of_fixedCenterCell
    (c error variation : ℝ) {N : ℕ}
    (hcenter : error + variation < (leftLowMiddlePhaseCenter c N).re)
    {y : ℝ} (hy : 0 < y) (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    (herror : leftLowMiddlePhaseError y N ≤ error)
    (hvariation :
      ‖leftLowMiddlePhaseCenter y N - leftLowMiddlePhaseCenter c N‖ ≤ variation) :
    0 < (speiserZetaDerivRatio ((y : ℂ) * I)).re := by
  have hball := norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_at_le
    y c hy hN hzMargin hvariation
  have hre := Complex.abs_re_le_norm
    (speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter c N)
  rw [Complex.sub_re] at hre
  have habs :
      |(speiserZetaDerivRatio ((y : ℂ) * I)).re -
          (leftLowMiddlePhaseCenter c N).re| ≤ error + variation :=
    hre.trans (hball.trans (add_le_add herror le_rfl))
  linarith [neg_abs_le
    ((speiserZetaDerivRatio ((y : ℂ) * I)).re -
      (leftLowMiddlePhaseCenter c N).re)]

/-- Uniform error and variation budgets reduce a complete cell to one fixed-center imaginary
margin. -/
theorem speiserZetaDerivRatio_leftVertical_im_neg_of_fixedCenterCell
    (c error variation : ℝ) {N : ℕ}
    (hcenter : (leftLowMiddlePhaseCenter c N).im < -(error + variation))
    {y : ℝ} (hy : 0 < y) (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinTwoZetaError (1 - (y : ℂ) * I) N <
        ‖eulerMaclaurinTwoZetaApprox (1 - (y : ℂ) * I) N‖)
    (herror : leftLowMiddlePhaseError y N ≤ error)
    (hvariation :
      ‖leftLowMiddlePhaseCenter y N - leftLowMiddlePhaseCenter c N‖ ≤ variation) :
    (speiserZetaDerivRatio ((y : ℂ) * I)).im < 0 := by
  have hball := norm_speiserZetaDerivRatio_sub_leftLowMiddlePhaseCenter_at_le
    y c hy hN hzMargin hvariation
  have him := Complex.abs_im_le_norm
    (speiserZetaDerivRatio ((y : ℂ) * I) - leftLowMiddlePhaseCenter c N)
  rw [Complex.sub_im] at him
  have habs :
      |(speiserZetaDerivRatio ((y : ℂ) * I)).im -
          (leftLowMiddlePhaseCenter c N).im| ≤ error + variation :=
    him.trans (hball.trans (add_le_add herror le_rfl))
  linarith [le_abs_self
    ((speiserZetaDerivRatio ((y : ℂ) * I)).im -
      (leftLowMiddlePhaseCenter c N).im)]

end

end LeanLab.Riemann
