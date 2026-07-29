import LeanLab.Riemann.HardyLittlewoodSourceNormalization
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Hardy--Littlewood finite Dirichlet-polynomial mean square

This file reconstructs the finite core of Hardy--Littlewood 1921, Lemmas 6--8. The source
proves an `O(N / log N)` off-diagonal estimate. The finite mean-square step only needs `O(N)`;
we retain that weaker target and keep the later conditionally convergent series truncation
outside this module.
-/

noncomputable section

open Complex Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

/-- The squared norm of the unsigned Hardy--Littlewood logarithmic coefficient. -/
def hardyLittlewoodLogSquareCoeff (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n : ℝ) * Real.log n ^ 2) else 0

theorem hardyLittlewood_logSquareCoeff_nonneg (n : ℕ) :
    0 ≤ hardyLittlewoodLogSquareCoeff n := by
  unfold hardyLittlewoodLogSquareCoeff
  split_ifs
  · positivity
  · exact le_rfl

/-- A telescope that gives a truncation-independent diagonal bound. -/
theorem hardyLittlewood_logSquareCoeff_le_telescope
    {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodLogSquareCoeff n ≤
      6 * (1 / Real.log n - 1 / Real.log (n + 1)) := by
  rw [hardyLittlewoodLogSquareCoeff, if_pos hn]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hlogn : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))
  have hlogn1 : 0 < Real.log (n + 1) :=
    Real.log_pos (by
      exact_mod_cast (lt_trans (by omega : 1 < n) (Nat.lt_succ_self n)))
  have hratio : (0 : ℝ) < (n + 1 : ℝ) / n := div_pos hn1 hn0
  have hlogRatio :
      1 / ((n : ℝ) + 1) ≤ Real.log (((n : ℝ) + 1) / n) := by
    have h := Real.one_sub_inv_le_log_of_pos hratio
    convert h using 1
    field_simp
    ring
  have hlogn1_le : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    calc
      Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) ^ 2) := by
        apply Real.log_le_log hn1
        nlinarith
      _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num
  have hdiff :
      1 / Real.log n - 1 / Real.log (n + 1) =
        Real.log (((n : ℝ) + 1) / n) /
          (Real.log n * Real.log ((n : ℝ) + 1)) := by
    rw [Real.log_div hn1.ne' hn0.ne']
    field_simp
  rw [hdiff]
  have hleft :
      1 / ((n : ℝ) * Real.log n ^ 2) *
          (Real.log n * Real.log ((n : ℝ) + 1)) ≤
        2 / (n : ℝ) := by
    field_simp
    nlinarith
  have hmiddle : 2 / (n : ℝ) ≤ 6 / ((n : ℝ) + 1) := by
    apply (div_le_div_iff₀ hn0 hn1).2
    nlinarith
  have hright :
      6 / ((n : ℝ) + 1) ≤
        6 * Real.log (((n : ℝ) + 1) / n) := by
    calc
      6 / ((n : ℝ) + 1) =
          6 * (1 / ((n : ℝ) + 1)) := by ring
      _ ≤ 6 * Real.log (((n : ℝ) + 1) / n) :=
        mul_le_mul_of_nonneg_left hlogRatio (by norm_num)
  have hcross :
      1 / ((n : ℝ) * Real.log n ^ 2) *
          (Real.log n * Real.log ((n : ℝ) + 1)) ≤
        6 * Real.log (((n : ℝ) + 1) / n) := by
    calc
      1 / ((n : ℝ) * Real.log n ^ 2) *
            (Real.log n * Real.log ((n : ℝ) + 1))
          ≤ 2 / (n : ℝ) := hleft
      _ ≤ 6 / ((n : ℝ) + 1) := hmiddle
      _ ≤ 6 * Real.log (((n : ℝ) + 1) / n) := hright
  have hdiv :=
    (le_div_iff₀ (mul_pos hlogn hlogn1)).2 hcross
  simpa [mul_div_assoc] using hdiv

def hardyLittlewoodLogReciprocal (k : ℕ) : ℝ :=
  1 / Real.log ((k : ℝ) + 2)

def hardyLittlewoodLogSquareTelescope (k : ℕ) : ℝ :=
  6 * (hardyLittlewoodLogReciprocal k -
    hardyLittlewoodLogReciprocal (k + 1))

theorem hardyLittlewood_logSquareTelescope_nonneg (k : ℕ) :
    0 ≤ hardyLittlewoodLogSquareTelescope k := by
  have hcoeff :=
    hardyLittlewood_logSquareCoeff_le_telescope (n := k + 2) (by omega)
  have hcoeff0 := hardyLittlewood_logSquareCoeff_nonneg (k + 2)
  simpa [hardyLittlewoodLogSquareTelescope,
    hardyLittlewoodLogReciprocal, Nat.cast_add, Nat.cast_ofNat,
    add_assoc, add_comm, add_left_comm] using hcoeff0.trans hcoeff

theorem hardyLittlewood_logSquareCoeff_shift_le_telescope (k : ℕ) :
    hardyLittlewoodLogSquareCoeff (k + 2) ≤
      hardyLittlewoodLogSquareTelescope k := by
  simpa [hardyLittlewoodLogSquareTelescope,
    hardyLittlewoodLogReciprocal, Nat.cast_add, Nat.cast_ofNat,
    add_assoc, add_comm, add_left_comm] using
      hardyLittlewood_logSquareCoeff_le_telescope (n := k + 2) (by omega)

theorem hardyLittlewood_logSquareTelescope_hasSum :
    HasSum hardyLittlewoodLogSquareTelescope (6 / Real.log 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    hardyLittlewood_logSquareTelescope_nonneg]
  have hlog :
      Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 2)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hinv :
      Tendsto hardyLittlewoodLogReciprocal atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => 1 / Real.log ((n : ℝ) + 2))
      atTop (𝓝 0)
    simpa [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp hlog
  have hpartial :
      (fun n : ℕ => ∑ k ∈ range n, hardyLittlewoodLogSquareTelescope k) =
        fun n : ℕ => 6 * (hardyLittlewoodLogReciprocal 0 -
          hardyLittlewoodLogReciprocal n) := by
    funext n
    simp only [hardyLittlewoodLogSquareTelescope, ← mul_sum,
      sum_range_sub']
  rw [hpartial]
  simpa [hardyLittlewoodLogReciprocal, div_eq_mul_inv] using
    (tendsto_const_nhds.sub hinv).const_mul 6

theorem summable_hardyLittlewoodLogSquareCoeff :
    Summable hardyLittlewoodLogSquareCoeff := by
  rw [← summable_nat_add_iff 2]
  exact hardyLittlewood_logSquareTelescope_hasSum.summable.of_nonneg_of_le
    (fun k => hardyLittlewood_logSquareCoeff_nonneg (k + 2))
    hardyLittlewood_logSquareCoeff_shift_le_telescope

theorem tsum_hardyLittlewoodLogSquareCoeff_le :
    ∑' n, hardyLittlewoodLogSquareCoeff n ≤ 6 / Real.log 2 := by
  have hle :=
    Summable.tsum_le_tsum
      hardyLittlewood_logSquareCoeff_shift_le_telescope
      ((summable_nat_add_iff 2).mpr summable_hardyLittlewoodLogSquareCoeff)
      hardyLittlewood_logSquareTelescope_hasSum.summable
  rw [hardyLittlewood_logSquareTelescope_hasSum.tsum_eq] at hle
  have hzero0 : hardyLittlewoodLogSquareCoeff 0 = 0 := by
    simp [hardyLittlewoodLogSquareCoeff]
  have hzero1 : hardyLittlewoodLogSquareCoeff 1 = 0 := by
    simp [hardyLittlewoodLogSquareCoeff]
  have hshiftOne :
      (∑' n, hardyLittlewoodLogSquareCoeff n) =
        ∑' n, hardyLittlewoodLogSquareCoeff (n + 1) := by
    simpa [hzero0, add_comm] using
      Summable.tsum_eq_zero_add summable_hardyLittlewoodLogSquareCoeff
  have htailSummable :
      Summable (fun n => hardyLittlewoodLogSquareCoeff (n + 1)) :=
    (summable_nat_add_iff 1).mpr summable_hardyLittlewoodLogSquareCoeff
  have hshiftTwo :
      (∑' n, hardyLittlewoodLogSquareCoeff (n + 1)) =
        ∑' n, hardyLittlewoodLogSquareCoeff (n + 2) := by
    simpa [hzero1, add_assoc] using
      Summable.tsum_eq_zero_add htailSummable
  rw [hshiftOne, hshiftTwo]
  exact hle

/-- The literal real coefficient in Hardy--Littlewood's finite truncation. -/
def hardyLittlewoodThetaCoeff (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (-1 : ℝ) ^ (n - 1) / (Real.sqrt n * Real.log n)
  else 0

/-- One logarithmic-frequency term, with a real translation of the spectral variable. -/
def hardyLittlewoodThetaPhase (shift : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  -((t + shift) * Real.log (n : ℝ))

def hardyLittlewoodThetaTerm (shift : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (hardyLittlewoodThetaCoeff n : ℂ) *
    Complex.exp ((hardyLittlewoodThetaPhase shift n t : ℝ) * I)

/-- The source finite Dirichlet polynomial over `2, ..., N`. -/
def hardyLittlewoodThetaPolynomial (N : ℕ) (shift t : ℝ) : ℂ :=
  ∑ n ∈ Icc 2 N, hardyLittlewoodThetaTerm shift n t

theorem hardyLittlewoodThetaCoeff_sq
    {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodThetaCoeff n ^ 2 =
      hardyLittlewoodLogSquareCoeff n := by
  rw [hardyLittlewoodThetaCoeff, if_pos hn,
    hardyLittlewoodLogSquareCoeff, if_pos hn]
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn0).ne'
  have hlog0 : Real.log (n : ℝ) ≠ 0 := hlog.ne'
  rw [div_pow]
  rw [mul_pow, Real.sq_sqrt hn0.le]
  have hsign : ((-1 : ℝ) ^ (n - 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [hsign]

theorem norm_hardyLittlewoodThetaCoeff
    {n : ℕ} (hn : 2 ≤ n) :
    ‖(hardyLittlewoodThetaCoeff n : ℂ)‖ =
      1 / (Real.sqrt n * Real.log n) := by
  rw [norm_real, Real.norm_eq_abs, hardyLittlewoodThetaCoeff, if_pos hn,
    abs_div, abs_pow, abs_neg, abs_one, one_pow]
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hlog]

theorem norm_hardyLittlewoodThetaTerm
    (shift t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ‖hardyLittlewoodThetaTerm shift n t‖ =
      1 / (Real.sqrt n * Real.log n) := by
  rw [hardyLittlewoodThetaTerm, norm_mul,
    Complex.norm_exp]
  have him :
      (((hardyLittlewoodThetaPhase shift n t : ℝ) : ℂ) * I).re = 0 := by
    norm_num
  rw [him, Real.exp_zero, mul_one, norm_hardyLittlewoodThetaCoeff hn]

theorem continuous_hardyLittlewoodThetaTerm
    (shift : ℝ) (n : ℕ) :
    Continuous (hardyLittlewoodThetaTerm shift n) := by
  unfold hardyLittlewoodThetaTerm
  unfold hardyLittlewoodThetaPhase
  fun_prop

theorem continuous_hardyLittlewoodThetaPolynomial
    (N : ℕ) (shift : ℝ) :
    Continuous (hardyLittlewoodThetaPolynomial N shift) := by
  unfold hardyLittlewoodThetaPolynomial
  apply continuous_finsetSum
  intro n _
  exact continuous_hardyLittlewoodThetaTerm shift n

def hardyLittlewoodThetaAbsCoeff (n : ℕ) : ℝ :=
  |hardyLittlewoodThetaCoeff n|

theorem hardyLittlewoodThetaAbsCoeff_nonneg (n : ℕ) :
    0 ≤ hardyLittlewoodThetaAbsCoeff n :=
  abs_nonneg _

theorem hardyLittlewoodThetaAbsCoeff_sq
    {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodThetaAbsCoeff n ^ 2 =
      hardyLittlewoodLogSquareCoeff n := by
  rw [hardyLittlewoodThetaAbsCoeff, sq_abs,
    hardyLittlewoodThetaCoeff_sq hn]

theorem hardyLittlewoodThetaAbsCoeff_eq
    {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodThetaAbsCoeff n =
      1 / (Real.sqrt n * Real.log n) := by
  rw [hardyLittlewoodThetaAbsCoeff]
  simpa [norm_real, Real.norm_eq_abs] using
    norm_hardyLittlewoodThetaCoeff hn

theorem sum_hardyLittlewoodLogSquareCoeff_Icc_le (N : ℕ) :
    (∑ n ∈ Icc 2 N, hardyLittlewoodLogSquareCoeff n) ≤
      6 / Real.log 2 := by
  calc
    (∑ n ∈ Icc 2 N, hardyLittlewoodLogSquareCoeff n) ≤
        ∑' n, hardyLittlewoodLogSquareCoeff n :=
      summable_hardyLittlewoodLogSquareCoeff.sum_le_tsum
        (Icc 2 N) (fun n _ => hardyLittlewood_logSquareCoeff_nonneg n)
    _ ≤ 6 / Real.log 2 := tsum_hardyLittlewoodLogSquareCoeff_le

theorem sq_sum_hardyLittlewoodThetaAbsCoeff_le (N : ℕ) :
    (∑ n ∈ Icc 2 N, hardyLittlewoodThetaAbsCoeff n) ^ 2 ≤
      (N : ℝ) * (6 / Real.log 2) := by
  have hcauchy :
      (∑ n ∈ Icc 2 N, hardyLittlewoodThetaAbsCoeff n) ^ 2 ≤
        ((Finset.Icc 2 N).card : ℝ) *
          ∑ n ∈ Icc 2 N, hardyLittlewoodThetaAbsCoeff n ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : ((Finset.Icc 2 N).card : ℝ) ≤ N := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : N + 1 - 2 ≤ N)
  have hsq :
      (∑ n ∈ Icc 2 N, hardyLittlewoodThetaAbsCoeff n ^ 2) =
        ∑ n ∈ Icc 2 N, hardyLittlewoodLogSquareCoeff n := by
    apply sum_congr rfl
    intro n hn
    exact hardyLittlewoodThetaAbsCoeff_sq (mem_Icc.mp hn).1
  calc
    (∑ n ∈ Icc 2 N, hardyLittlewoodThetaAbsCoeff n) ^ 2 ≤
        ((Finset.Icc 2 N).card : ℝ) *
          ∑ n ∈ Icc 2 N, hardyLittlewoodThetaAbsCoeff n ^ 2 := hcauchy
    _ = ((Finset.Icc 2 N).card : ℝ) *
          ∑ n ∈ Icc 2 N, hardyLittlewoodLogSquareCoeff n := by rw [hsq]
    _ ≤ (N : ℝ) * (6 / Real.log 2) := by
      apply mul_le_mul hcard (sum_hardyLittlewoodLogSquareCoeff_Icc_le N)
      · exact sum_nonneg fun n _ => hardyLittlewood_logSquareCoeff_nonneg n
      · positivity

/-- The positive upper-triangular logarithmic kernel, with `m=n+r`. -/
def hardyLittlewoodUpperPairKernel (n r : ℕ) : ℝ :=
  hardyLittlewoodThetaAbsCoeff n *
      hardyLittlewoodThetaAbsCoeff (n + r) /
    Real.log (((n : ℝ) + r) / n)

theorem hardyLittlewood_log_ratio_pos
    {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    0 < Real.log (((n : ℝ) + r) / n) := by
  apply Real.log_pos
  apply (one_lt_div (by positivity : (0 : ℝ) < n)).2
  exact_mod_cast (Nat.lt_add_of_pos_right hr)

theorem hardyLittlewood_log_ratio_lower
    {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) :
    (r : ℝ) / (n + r) ≤
      Real.log (((n : ℝ) + r) / n) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hnr0 : (0 : ℝ) < n + r := by positivity
  have hratio : (0 : ℝ) < ((n : ℝ) + r) / n :=
    div_pos hnr0 hn0
  have h := Real.one_sub_inv_le_log_of_pos hratio
  have heq :
      1 - (((n : ℝ) + r) / n)⁻¹ =
        (r : ℝ) / (n + r) := by
    rw [inv_div]
    field_simp
    ring
  rw [← heq]
  exact h

theorem hardyLittlewoodUpperPairKernel_near_le
    {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n) :
    hardyLittlewoodUpperPairKernel n r ≤
      2 / ((r : ℝ) * Real.log n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hr0 : (0 : ℝ) < r := by positivity
  have hnr0 : (0 : ℝ) < n + r := by positivity
  have hlogn : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))
  have hlognr : 0 < Real.log (n + r) := by
    apply Real.log_pos
    exact_mod_cast (lt_trans (by omega : 1 < n) (Nat.lt_add_of_pos_right hr))
  have hlogRatio :=
    hardyLittlewood_log_ratio_pos (show 1 ≤ n by omega) hr
  have hlogLower :=
    hardyLittlewood_log_ratio_lower (show 1 ≤ n by omega) hr
  have hsqrtN : Real.sqrt (n : ℝ) ^ 2 = n :=
    Real.sq_sqrt (by positivity)
  have hsqrtMono :
      Real.sqrt (n : ℝ) ≤ Real.sqrt (n + r : ℝ) :=
    Real.sqrt_le_sqrt (by
      exact_mod_cast (Nat.le_add_right n r))
  have hsqrtProd :
      (n : ℝ) ≤ Real.sqrt n * Real.sqrt (n + r) := by
    calc
      (n : ℝ) = Real.sqrt n * Real.sqrt n := by
        nlinarith
      _ ≤ Real.sqrt n * Real.sqrt (n + r) :=
        mul_le_mul_of_nonneg_left hsqrtMono (Real.sqrt_nonneg _)
  have hlogMono : Real.log (n : ℝ) ≤ Real.log (n + r : ℝ) := by
    apply Real.log_le_log hn0
    exact_mod_cast (Nat.le_add_right n r)
  have hsize :
      (n + r : ℝ) ≤
        2 * (Real.sqrt n * Real.sqrt (n + r)) := by
    calc
      (n + r : ℝ) ≤ 2 * n := by exact_mod_cast (by omega : n + r ≤ 2 * n)
      _ ≤ 2 * (Real.sqrt n * Real.sqrt (n + r)) := by nlinarith
  have hsmall :
      ((r : ℝ) * Real.log n ^ 2) / 2 ≤
        (Real.sqrt n * Real.log n) *
          (Real.sqrt (n + r) * Real.log (n + r)) *
            ((r : ℝ) / (n + r)) := by
    have hhalf :
        (n + r : ℝ) / 2 ≤
          Real.sqrt n * Real.sqrt (n + r) := by linarith
    have hlogn0 : 0 ≤ Real.log (n : ℝ) := hlogn.le
    have hlognr0 : 0 ≤ Real.log (n + r : ℝ) := hlognr.le
    have hmul :
        ((n + r : ℝ) / 2) * Real.log n ≤
          (Real.sqrt n * Real.sqrt (n + r)) * Real.log (n + r) :=
      mul_le_mul hhalf hlogMono hlogn0 (by positivity)
    have hmul' :=
      mul_le_mul_of_nonneg_left hmul
        (mul_nonneg hr0.le hlogn0)
    rw [show
      (Real.sqrt n * Real.log n) *
            (Real.sqrt (n + r) * Real.log (n + r)) *
              ((r : ℝ) / (n + r)) =
          ((Real.sqrt n * Real.log n) *
            (Real.sqrt (n + r) * Real.log (n + r)) * r) /
              (n + r) by ring]
    apply (le_div_iff₀ hnr0).2
    nlinarith
  have hden :
      ((r : ℝ) * Real.log n ^ 2) / 2 ≤
        (Real.sqrt n * Real.log n) *
          (Real.sqrt (n + r) * Real.log (n + r)) *
            Real.log (((n : ℝ) + r) / n) := by
    exact hsmall.trans
      (mul_le_mul_of_nonneg_left hlogLower (by positivity))
  rw [hardyLittlewoodUpperPairKernel,
    hardyLittlewoodThetaAbsCoeff_eq hn,
    hardyLittlewoodThetaAbsCoeff_eq (by omega : 2 ≤ n + r)]
  simp only [Nat.cast_add]
  have hdenPos :
      0 < (Real.sqrt n * Real.log n) *
          (Real.sqrt (n + r) * Real.log (n + r)) *
            Real.log (((n : ℝ) + r) / n) := by positivity
  have hsmallPos :
      0 < ((r : ℝ) * Real.log n ^ 2) / 2 := by positivity
  calc
    (1 / (Real.sqrt n * Real.log n)) *
          (1 / (Real.sqrt (n + r) * Real.log (n + r))) /
          Real.log (((n : ℝ) + r) / n) =
        1 / ((Real.sqrt n * Real.log n) *
          (Real.sqrt (n + r) * Real.log (n + r)) *
            Real.log (((n : ℝ) + r) / n)) := by field_simp
    _ ≤ 1 / (((r : ℝ) * Real.log n ^ 2) / 2) :=
      one_div_le_one_div_of_le hsmallPos hden
    _ = 2 / ((r : ℝ) * Real.log n ^ 2) := by field_simp

theorem hardyLittlewoodUpperPairKernel_far_le
    {n r : ℕ} (hn : 2 ≤ n) (hr : n < r) :
    hardyLittlewoodUpperPairKernel n r ≤
      hardyLittlewoodThetaAbsCoeff n *
        hardyLittlewoodThetaAbsCoeff (n + r) / Real.log 2 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hr1 : 1 ≤ r := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio :
      (2 : ℝ) ≤ ((n : ℝ) + r) / n := by
    apply (le_div_iff₀ hn0).2
    exact_mod_cast (by omega : 2 * n ≤ n + r)
  have hlog :
      Real.log 2 ≤ Real.log (((n : ℝ) + r) / n) :=
    Real.log_le_log (by norm_num) hratio
  have habs :
      0 ≤ hardyLittlewoodThetaAbsCoeff n *
        hardyLittlewoodThetaAbsCoeff (n + r) :=
    mul_nonneg (hardyLittlewoodThetaAbsCoeff_nonneg n)
      (hardyLittlewoodThetaAbsCoeff_nonneg (n + r))
  unfold hardyLittlewoodUpperPairKernel
  exact div_le_div_of_nonneg_left habs hlog2 hlog

def hardyLittlewoodNearPairMajorant (n r : ℕ) : ℝ :=
  if r ≤ n then 2 / ((r : ℝ) * Real.log n ^ 2) else 0

def hardyLittlewoodFarPairMajorant (n r : ℕ) : ℝ :=
  if n < r then
    hardyLittlewoodThetaAbsCoeff n *
      hardyLittlewoodThetaAbsCoeff (n + r) / Real.log 2
  else 0

theorem hardyLittlewoodUpperPairKernel_le_majorants
    {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    hardyLittlewoodUpperPairKernel n r ≤
      hardyLittlewoodNearPairMajorant n r +
        hardyLittlewoodFarPairMajorant n r := by
  by_cases hnear : r ≤ n
  · rw [hardyLittlewoodNearPairMajorant, if_pos hnear,
      hardyLittlewoodFarPairMajorant, if_neg (not_lt_of_ge hnear), add_zero]
    exact hardyLittlewoodUpperPairKernel_near_le hn hr hnear
  · have hfar : n < r := lt_of_not_ge hnear
    rw [hardyLittlewoodNearPairMajorant, if_neg hnear, zero_add,
      hardyLittlewoodFarPairMajorant, if_pos hfar]
    exact hardyLittlewoodUpperPairKernel_far_le hn hfar

theorem sum_hardyLittlewoodNearPairMajorant_le
    {N n : ℕ} (hn : 2 ≤ n) :
    (∑ r ∈ Finset.Icc 1 (N - n), hardyLittlewoodNearPairMajorant n r) ≤
      2 * (1 / Real.log 2 ^ 2 + 1 / Real.log 2) := by
  let near : Finset ℕ := (Finset.Icc 1 (N - n)).filter fun r => r ≤ n
  have hsubset : near ⊆ Finset.Icc 1 n := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr'.1).1, hr'.2⟩
  have htermNonneg :
      ∀ r ∈ Finset.Icc 1 n,
        r ∉ near →
        0 ≤ 2 / ((r : ℝ) * Real.log n ^ 2) := by
    intro r hr _
    have hr0 : (0 : ℝ) < r := by
      exact_mod_cast
        (lt_of_lt_of_le (by omega : 0 < 1) (Finset.mem_Icc.mp hr).1)
    have hlog : 0 < Real.log n :=
      Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))
    positivity
  have hnearSum :
      (∑ r ∈ Finset.Icc 1 (N - n), hardyLittlewoodNearPairMajorant n r) =
        ∑ r ∈ near, 2 / ((r : ℝ) * Real.log n ^ 2) := by
    simpa [hardyLittlewoodNearPairMajorant, near] using
      (Finset.sum_filter (s := Finset.Icc 1 (N - n))
        (fun r => r ≤ n)
        (fun r => 2 / ((r : ℝ) * Real.log n ^ 2))).symm
  have htoHarmonic :
      (∑ r ∈ near, 2 / ((r : ℝ) * Real.log n ^ 2)) ≤
        2 * (harmonic n : ℝ) / Real.log n ^ 2 := by
    calc
      (∑ r ∈ near, 2 / ((r : ℝ) * Real.log n ^ 2)) ≤
          ∑ r ∈ Finset.Icc 1 n, 2 / ((r : ℝ) * Real.log n ^ 2) :=
        sum_le_sum_of_subset_of_nonneg hsubset htermNonneg
      _ = 2 * (harmonic n : ℝ) / Real.log n ^ 2 := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rw [mul_sum, div_eq_mul_inv, sum_mul]
        apply sum_congr rfl
        intro r _
        ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0 < Real.log n :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn))
  have hlogLower : Real.log 2 ≤ Real.log n := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hinv : 1 / Real.log n ≤ 1 / Real.log 2 :=
    one_div_le_one_div_of_le hlog2 hlogLower
  have hinvSq : 1 / Real.log n ^ 2 ≤ 1 / Real.log 2 ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hlog2)
    nlinarith
  have hharmonic : (harmonic n : ℝ) ≤ 1 + Real.log n :=
    harmonic_le_one_add_log n
  rw [hnearSum]
  calc
    (∑ r ∈ near, 2 / ((r : ℝ) * Real.log n ^ 2)) ≤
        2 * (harmonic n : ℝ) / Real.log n ^ 2 := htoHarmonic
    _ ≤ 2 * (1 + Real.log n) / Real.log n ^ 2 := by
      gcongr
    _ = 2 * (1 / Real.log n ^ 2 + 1 / Real.log n) := by
      field_simp
    _ ≤ 2 * (1 / Real.log 2 ^ 2 + 1 / Real.log 2) := by
      gcongr

theorem sum_hardyLittlewoodFarShift_le
    {N n : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) :
    (∑ r ∈ Finset.Icc 1 (N - n),
        if n < r then hardyLittlewoodThetaAbsCoeff (n + r) else 0) ≤
      ∑ m ∈ Finset.Icc 2 N, hardyLittlewoodThetaAbsCoeff m := by
  let far : Finset ℕ := (Finset.Icc 1 (N - n)).filter fun r => n < r
  let shifted : Finset ℕ := far.image fun r => n + r
  have hinj : Set.InjOn (fun r : ℕ => n + r) (far : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.add_left_cancel hab
  have hsubset : shifted ⊆ Finset.Icc 2 N := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hm
    have hr' := Finset.mem_filter.mp hr
    have hrange := Finset.mem_Icc.mp hr'.1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsumFilter :
      (∑ r ∈ Finset.Icc 1 (N - n),
          if n < r then hardyLittlewoodThetaAbsCoeff (n + r) else 0) =
        ∑ r ∈ far, hardyLittlewoodThetaAbsCoeff (n + r) := by
    simpa [far] using
      (Finset.sum_filter (s := Finset.Icc 1 (N - n))
        (fun r => n < r)
        (fun r => hardyLittlewoodThetaAbsCoeff (n + r))).symm
  have hsumImage :
      (∑ r ∈ far, hardyLittlewoodThetaAbsCoeff (n + r)) =
        ∑ m ∈ shifted, hardyLittlewoodThetaAbsCoeff m := by
    exact (Finset.sum_image hinj).symm
  rw [hsumFilter, hsumImage]
  exact sum_le_sum_of_subset_of_nonneg hsubset
    (fun m _ _ => hardyLittlewoodThetaAbsCoeff_nonneg m)

theorem sum_hardyLittlewoodFarPairMajorant_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n),
          hardyLittlewoodFarPairMajorant n r) ≤
      ((N : ℝ) * (6 / Real.log 2)) / Real.log 2 := by
  let total : ℝ :=
    ∑ m ∈ Finset.Icc 2 N, hardyLittlewoodThetaAbsCoeff m
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinner :
      ∀ n ∈ Finset.Icc 2 N,
        (∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodFarPairMajorant n r) ≤
          (hardyLittlewoodThetaAbsCoeff n / Real.log 2) * total := by
    intro n hn
    have hnRange := Finset.mem_Icc.mp hn
    have hshift := sum_hardyLittlewoodFarShift_le hnRange.1 hnRange.2
    have hfactor :
        (∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodFarPairMajorant n r) =
            (hardyLittlewoodThetaAbsCoeff n / Real.log 2) *
            (∑ r ∈ Finset.Icc 1 (N - n),
              if n < r then hardyLittlewoodThetaAbsCoeff (n + r) else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [hardyLittlewoodFarPairMajorant]
      split_ifs
      · ring
      · ring
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left hshift
      (div_nonneg (hardyLittlewoodThetaAbsCoeff_nonneg n) hlog2.le)
  calc
    (∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n),
          hardyLittlewoodFarPairMajorant n r) ≤
        ∑ n ∈ Finset.Icc 2 N,
          (hardyLittlewoodThetaAbsCoeff n / Real.log 2) * total :=
      sum_le_sum hinner
    _ = total ^ 2 / Real.log 2 := by
      rw [← sum_mul]
      unfold total
      rw [← Finset.sum_div]
      ring
    _ ≤ ((N : ℝ) * (6 / Real.log 2)) / Real.log 2 := by
      exact div_le_div_of_nonneg_right
        (sq_sum_hardyLittlewoodThetaAbsCoeff_le N) hlog2.le

def hardyLittlewoodUpperPairSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ∑ r ∈ Finset.Icc 1 (N - n),
      hardyLittlewoodUpperPairKernel n r

def hardyLittlewoodNearPairConstant : ℝ :=
  2 * (1 / Real.log 2 ^ 2 + 1 / Real.log 2)

def hardyLittlewoodFarPairConstant : ℝ :=
  (6 / Real.log 2) / Real.log 2

theorem hardyLittlewoodNearPairConstant_pos :
    0 < hardyLittlewoodNearPairConstant := by
  unfold hardyLittlewoodNearPairConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem hardyLittlewoodFarPairConstant_pos :
    0 < hardyLittlewoodFarPairConstant := by
  unfold hardyLittlewoodFarPairConstant
  positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

theorem hardyLittlewoodUpperPairSum_le (N : ℕ) :
    hardyLittlewoodUpperPairSum N ≤
      (N : ℝ) *
        (hardyLittlewoodNearPairConstant + hardyLittlewoodFarPairConstant) := by
  have hnear :
      (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodNearPairMajorant n r) ≤
        (N : ℝ) * hardyLittlewoodNearPairConstant := by
    calc
      (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodNearPairMajorant n r) ≤
          ∑ _n ∈ Finset.Icc 2 N, hardyLittlewoodNearPairConstant := by
        apply sum_le_sum
        intro n hn
        simpa [hardyLittlewoodNearPairConstant] using
          sum_hardyLittlewoodNearPairMajorant_le
            (N := N) (Finset.mem_Icc.mp hn).1
      _ = ((Finset.Icc 2 N).card : ℝ) *
          hardyLittlewoodNearPairConstant := by simp
      _ ≤ (N : ℝ) * hardyLittlewoodNearPairConstant := by
        apply mul_le_mul_of_nonneg_right
        · rw [Nat.card_Icc]
          exact_mod_cast (by omega : N + 1 - 2 ≤ N)
        · exact hardyLittlewoodNearPairConstant_pos.le
  have hfar :
      (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodFarPairMajorant n r) ≤
        (N : ℝ) * hardyLittlewoodFarPairConstant := by
    simpa [hardyLittlewoodFarPairConstant, mul_div_assoc] using
      sum_hardyLittlewoodFarPairMajorant_le N
  unfold hardyLittlewoodUpperPairSum
  calc
    (∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n),
          hardyLittlewoodUpperPairKernel n r) ≤
        (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodNearPairMajorant n r) +
        (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodFarPairMajorant n r) := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro n hn
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro r hr
      exact hardyLittlewoodUpperPairKernel_le_majorants
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hr).1
    _ ≤ (N : ℝ) * hardyLittlewoodNearPairConstant +
          (N : ℝ) * hardyLittlewoodFarPairConstant :=
      add_le_add hnear hfar
    _ = (N : ℝ) *
        (hardyLittlewoodNearPairConstant + hardyLittlewoodFarPairConstant) := by ring

theorem normSq_finset_sum_eq_sum_mul_conj_re
    {α : Type*} (s : Finset α) (a : α → ℂ) :
    Complex.normSq (∑ i ∈ s, a i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re := by
  classical
  have hconj : conj (∑ j ∈ s, a j) = ∑ j ∈ s, conj (a j) := by
    simp
  have hmul :
      (∑ i ∈ s, a i) * (∑ j ∈ s, conj (a j)) =
        ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    Complex.normSq (∑ i ∈ s, a i) =
        ((∑ i ∈ s, a i) * conj (∑ j ∈ s, a j)).re := by
      rw [Complex.mul_conj]
      simp
    _ = (∑ i ∈ s, ∑ j ∈ s, a i * conj (a j)).re := by
      rw [hconj, hmul]
    _ = ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re := by
      simp

theorem hardyLittlewoodThetaTerm_mul_conj
    (shift t : ℝ) (n m : ℕ) :
    hardyLittlewoodThetaTerm shift n t *
        conj (hardyLittlewoodThetaTerm shift m t) =
      ((hardyLittlewoodThetaCoeff n * hardyLittlewoodThetaCoeff m : ℝ) : ℂ) *
        Complex.exp
          (((((Real.log m - Real.log n) * (t + shift) : ℝ) : ℂ) * I)) := by
  simp only [hardyLittlewoodThetaTerm, hardyLittlewoodThetaPhase,
    map_mul, conj_ofReal, ← Complex.exp_conj, conj_I]
  push_cast
  rw [mul_mul_mul_comm]
  rw [← Complex.exp_add]
  congr 1
  ring_nf

theorem hardyLittlewoodThetaTerm_mul_conj_re
    (shift t : ℝ) (n m : ℕ) :
    (hardyLittlewoodThetaTerm shift n t *
        conj (hardyLittlewoodThetaTerm shift m t)).re =
      hardyLittlewoodThetaCoeff n * hardyLittlewoodThetaCoeff m *
        Real.cos ((Real.log m - Real.log n) * (t + shift)) := by
  rw [hardyLittlewoodThetaTerm_mul_conj, Complex.mul_re]
  simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
  rw [Complex.exp_ofReal_mul_I_re]

theorem abs_intervalIntegral_cos_mul_add_le
    (omega shift A B : ℝ) (homega : omega ≠ 0) :
    |∫ t in A..B, Real.cos (omega * (t + shift))| ≤
      2 / |omega| := by
  have harg :
      (fun t : ℝ => Real.cos (omega * (t + shift))) =
        fun t : ℝ => Real.cos (omega * t + omega * shift) := by
    funext t
    congr 1
    ring
  rw [harg, intervalIntegral.integral_comp_mul_add
    (f := Real.cos) homega (omega * shift), integral_cos]
  simp only [smul_eq_mul, abs_mul, abs_inv]
  have hsin :
      |Real.sin (omega * B + omega * shift) -
          Real.sin (omega * A + omega * shift)| ≤ 2 := by
    calc
      |Real.sin (omega * B + omega * shift) -
          Real.sin (omega * A + omega * shift)| ≤
          |Real.sin (omega * B + omega * shift)| +
            |Real.sin (omega * A + omega * shift)| := abs_sub _ _
      _ ≤ 1 + 1 :=
        add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  calc
    |omega|⁻¹ *
          |Real.sin (omega * B + omega * shift) -
            Real.sin (omega * A + omega * shift)| ≤
        |omega|⁻¹ * 2 :=
      mul_le_mul_of_nonneg_left hsin (inv_nonneg.mpr (abs_nonneg omega))
    _ = 2 / |omega| := by ring

theorem abs_intervalIntegral_hardyLittlewoodUpperPair_le
    (shift A B : ℝ) {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    |∫ t in A..B,
        (hardyLittlewoodThetaTerm shift n t *
          conj (hardyLittlewoodThetaTerm shift (n + r) t)).re| ≤
      2 * hardyLittlewoodUpperPairKernel n r := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hnr0 : (0 : ℝ) < (n : ℝ) + r := by positivity
  have hfreq :
      Real.log ((n : ℝ) + r) - Real.log n =
        Real.log (((n : ℝ) + r) / n) := by
    exact (Real.log_div hnr0.ne' hn0.ne').symm
  have hfreqPos :
      0 < Real.log ((n : ℝ) + r) - Real.log n := by
    rw [hfreq]
    exact hardyLittlewood_log_ratio_pos (show 1 ≤ n by omega) hr
  simp_rw [hardyLittlewoodThetaTerm_mul_conj_re]
  push_cast
  rw [intervalIntegral.integral_const_mul, abs_mul]
  have hcos :=
    abs_intervalIntegral_cos_mul_add_le
      (Real.log ((n : ℝ) + r) - Real.log n) shift A B hfreqPos.ne'
  calc
    |hardyLittlewoodThetaCoeff n *
          hardyLittlewoodThetaCoeff (n + r)| *
        |∫ t in A..B,
          Real.cos
            ((Real.log (n + r : ℝ) - Real.log n) * (t + shift))| ≤
        |hardyLittlewoodThetaCoeff n *
          hardyLittlewoodThetaCoeff (n + r)| *
          (2 / |Real.log ((n : ℝ) + r) - Real.log n|) :=
      mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = 2 * hardyLittlewoodUpperPairKernel n r := by
      rw [abs_mul, abs_of_pos hfreqPos, hfreq]
      unfold hardyLittlewoodUpperPairKernel
      rw [hardyLittlewoodThetaAbsCoeff, hardyLittlewoodThetaAbsCoeff]
      ring

theorem sum_Icc_filter_lt_eq_sum_upperShift
    {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ n ∈ Finset.Icc 2 N,
        ∑ m ∈ (Finset.Icc 2 N).filter (fun m => n < m), f n m) =
      ∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n), f n (n + r) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnRange := Finset.mem_Icc.mp hn
  refine Finset.sum_bij (fun m _ => m - n) ?_ ?_ ?_ ?_
  · intro m hm
    have hm' := Finset.mem_filter.mp hm
    have hmRange := Finset.mem_Icc.mp hm'.1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    have hlt₁ := (Finset.mem_filter.mp hm₁).2
    have hlt₂ := (Finset.mem_filter.mp hm₂).2
    omega
  · intro r hr
    refine ⟨n + r, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      have hrRange := Finset.mem_Icc.mp hr
      exact
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · omega
  · intro m hm
    have hlt := (Finset.mem_filter.mp hm).2
    congr 2
    omega

theorem sum_row_eq_diag_add_upper_add_lower
    {R : Type*} [AddCommMonoid R] (s : Finset ℕ)
    (f : ℕ → R) {n : ℕ} (hn : n ∈ s) :
    (∑ m ∈ s, f m) =
      f n +
        (∑ m ∈ s.filter (fun m => n < m), f m) +
        (∑ m ∈ s.filter (fun m => m < n), f m) := by
  calc
    (∑ m ∈ s, f m) =
        ∑ m ∈ s,
          (((if m = n then f m else 0) +
              (if n < m then f m else 0)) +
            (if m < n then f m else 0)) := by
      apply Finset.sum_congr rfl
      intro m _
      rcases lt_trichotomy m n with hlt | heq | hgt
      · simp [hlt, ne_of_lt hlt, not_lt_of_ge hlt.le]
      · subst m
        simp
      · simp [hgt, ne_of_gt hgt, not_lt_of_ge hgt.le]
    _ =
        (∑ m ∈ s, if m = n then f m else 0) +
          (∑ m ∈ s, if n < m then f m else 0) +
          (∑ m ∈ s, if m < n then f m else 0) := by
      rw [sum_add_distrib, sum_add_distrib]
    _ =
        f n +
          (∑ m ∈ s.filter (fun m => n < m), f m) +
          (∑ m ∈ s.filter (fun m => m < n), f m) := by
      rw [Finset.sum_filter, Finset.sum_filter]
      simp [hn]

theorem sum_lower_eq_sum_upper_of_symmetric
    {R : Type*} [AddCommMonoid R] (s : Finset ℕ)
    (f : ℕ → ℕ → R) (hsymm : ∀ n m, f n m = f m n) :
    (∑ n ∈ s, ∑ m ∈ s.filter (fun m => m < n), f n m) =
      ∑ n ∈ s, ∑ m ∈ s.filter (fun m => n < m), f n m := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  split_ifs
  · exact hsymm m n
  · rfl

theorem sum_pair_eq_diag_add_two_upper_of_symmetric
    {R : Type*} [CommSemiring R] (s : Finset ℕ)
    (f : ℕ → ℕ → R) (hsymm : ∀ n m, f n m = f m n) :
    (∑ n ∈ s, ∑ m ∈ s, f n m) =
      (∑ n ∈ s, f n n) +
        2 * (∑ n ∈ s, ∑ m ∈ s.filter (fun m => n < m), f n m) := by
  have hlower := sum_lower_eq_sum_upper_of_symmetric s f hsymm
  calc
    (∑ n ∈ s, ∑ m ∈ s, f n m) =
        ∑ n ∈ s,
          (f n n +
            (∑ m ∈ s.filter (fun m => n < m), f n m) +
            (∑ m ∈ s.filter (fun m => m < n), f n m)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact sum_row_eq_diag_add_upper_add_lower s (f n) hn
    _ =
        (∑ n ∈ s, f n n) +
          (∑ n ∈ s, ∑ m ∈ s.filter (fun m => n < m), f n m) +
          (∑ n ∈ s, ∑ m ∈ s.filter (fun m => m < n), f n m) := by
      rw [sum_add_distrib, sum_add_distrib]
    _ =
        (∑ n ∈ s, f n n) +
          2 * (∑ n ∈ s, ∑ m ∈ s.filter (fun m => n < m), f n m) := by
      rw [hlower]
      ring

/-- The real integrated cross term in the finite Hardy--Littlewood polynomial. -/
def hardyLittlewoodPairIntegral
    (shift A L : ℝ) (n m : ℕ) : ℝ :=
  ∫ t in A..A + L,
    (hardyLittlewoodThetaTerm shift n t *
      conj (hardyLittlewoodThetaTerm shift m t)).re

theorem hardyLittlewoodPairIntegral_comm
    (shift A L : ℝ) (n m : ℕ) :
    hardyLittlewoodPairIntegral shift A L n m =
      hardyLittlewoodPairIntegral shift A L m n := by
  unfold hardyLittlewoodPairIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change
    (hardyLittlewoodThetaTerm shift n t *
        conj (hardyLittlewoodThetaTerm shift m t)).re =
      (hardyLittlewoodThetaTerm shift m t *
        conj (hardyLittlewoodThetaTerm shift n t)).re
  rw [hardyLittlewoodThetaTerm_mul_conj_re,
    hardyLittlewoodThetaTerm_mul_conj_re]
  rw [mul_comm (hardyLittlewoodThetaCoeff m)]
  have harg :
      (Real.log n - Real.log m) * (t + shift) =
        -((Real.log m - Real.log n) * (t + shift)) := by ring
  rw [harg, Real.cos_neg]

theorem hardyLittlewoodPairIntegral_diag
    (shift A L : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodPairIntegral shift A L n n =
      L * hardyLittlewoodLogSquareCoeff n := by
  unfold hardyLittlewoodPairIntegral
  simp_rw [hardyLittlewoodThetaTerm_mul_conj_re]
  simp only [sub_self, zero_mul, Real.cos_zero]
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul]
  rw [← pow_two]
  rw [hardyLittlewoodThetaCoeff_sq hn]
  ring

theorem continuous_hardyLittlewoodCrossRe
    (shift : ℝ) (n m : ℕ) :
    Continuous fun t : ℝ =>
      (hardyLittlewoodThetaTerm shift n t *
        conj (hardyLittlewoodThetaTerm shift m t)).re := by
  exact Complex.continuous_re.comp
    ((continuous_hardyLittlewoodThetaTerm shift n).mul
      (Complex.continuous_conj.comp
        (continuous_hardyLittlewoodThetaTerm shift m)))

/-- The finite mean square isolated from Hardy--Littlewood 1921, Lemma 7. -/
def hardyLittlewoodFiniteMeanSquare
    (N : ℕ) (shift A L : ℝ) : ℝ :=
  ∫ t in A..A + L, Complex.normSq (hardyLittlewoodThetaPolynomial N shift t)

theorem hardyLittlewoodFiniteMeanSquare_eq_pairSum
    (N : ℕ) (shift A L : ℝ) :
    hardyLittlewoodFiniteMeanSquare N shift A L =
      ∑ n ∈ Finset.Icc 2 N,
        ∑ m ∈ Finset.Icc 2 N,
          hardyLittlewoodPairIntegral shift A L n m := by
  have hpoint :
      ∀ t : ℝ,
        Complex.normSq (hardyLittlewoodThetaPolynomial N shift t) =
          ∑ n ∈ Finset.Icc 2 N,
            ∑ m ∈ Finset.Icc 2 N,
              (hardyLittlewoodThetaTerm shift n t *
                conj (hardyLittlewoodThetaTerm shift m t)).re := by
    intro t
    unfold hardyLittlewoodThetaPolynomial
    exact normSq_finset_sum_eq_sum_mul_conj_re
      (Finset.Icc 2 N) (hardyLittlewoodThetaTerm shift · t)
  rw [hardyLittlewoodFiniteMeanSquare]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_finsetSum]
    · rfl
    · intro m _
      apply Continuous.intervalIntegrable
      exact continuous_hardyLittlewoodCrossRe shift n m
  · intro n _
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro m _
    exact continuous_hardyLittlewoodCrossRe shift n m

theorem hardyLittlewoodFiniteMeanSquare_eq_diag_add_upper
    (N : ℕ) (shift A L : ℝ) :
    hardyLittlewoodFiniteMeanSquare N shift A L =
      (∑ n ∈ Finset.Icc 2 N,
        L * hardyLittlewoodLogSquareCoeff n) +
      2 * (∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n),
          hardyLittlewoodPairIntegral shift A L n (n + r)) := by
  rw [hardyLittlewoodFiniteMeanSquare_eq_pairSum]
  rw [sum_pair_eq_diag_add_two_upper_of_symmetric
    (Finset.Icc 2 N) (hardyLittlewoodPairIntegral shift A L)
    (hardyLittlewoodPairIntegral_comm shift A L)]
  rw [sum_Icc_filter_lt_eq_sum_upperShift]
  have hdiag :
      (∑ n ∈ Finset.Icc 2 N,
          hardyLittlewoodPairIntegral shift A L n n) =
        ∑ n ∈ Finset.Icc 2 N,
          L * hardyLittlewoodLogSquareCoeff n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hardyLittlewoodPairIntegral_diag shift A L (Finset.mem_Icc.mp hn).1
  rw [hdiag]

theorem sum_hardyLittlewoodUpperPairIntegral_le
    (N : ℕ) (shift A L : ℝ) :
    (∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n),
          hardyLittlewoodPairIntegral shift A L n (n + r)) ≤
      2 * hardyLittlewoodUpperPairSum N := by
  unfold hardyLittlewoodUpperPairSum
  rw [mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  calc
    hardyLittlewoodPairIntegral shift A L n (n + r) ≤
        |hardyLittlewoodPairIntegral shift A L n (n + r)| :=
      le_abs_self _
    _ ≤ 2 * hardyLittlewoodUpperPairKernel n r := by
      exact abs_intervalIntegral_hardyLittlewoodUpperPair_le
        shift A (A + L) (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hr).1

def hardyLittlewoodFiniteMeanSquareConstant : ℝ :=
  6 / Real.log 2 +
    4 * (hardyLittlewoodNearPairConstant + hardyLittlewoodFarPairConstant)

theorem hardyLittlewoodFiniteMeanSquare_le_length_add_truncation
    (N : ℕ) (shift A L : ℝ) (hL : 0 ≤ L) :
    hardyLittlewoodFiniteMeanSquare N shift A L ≤
      L * (6 / Real.log 2) +
        4 * (N : ℝ) *
          (hardyLittlewoodNearPairConstant +
            hardyLittlewoodFarPairConstant) := by
  have hdiag :
      (∑ n ∈ Finset.Icc 2 N,
          L * hardyLittlewoodLogSquareCoeff n) ≤
        L * (6 / Real.log 2) := by
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left
      (sum_hardyLittlewoodLogSquareCoeff_Icc_le N) hL
  have hupper :
      2 * (∑ n ∈ Finset.Icc 2 N,
        ∑ r ∈ Finset.Icc 1 (N - n),
          hardyLittlewoodPairIntegral shift A L n (n + r)) ≤
        4 * (N : ℝ) *
          (hardyLittlewoodNearPairConstant +
            hardyLittlewoodFarPairConstant) := by
    calc
      2 * (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodPairIntegral shift A L n (n + r)) ≤
          2 * (2 * hardyLittlewoodUpperPairSum N) :=
        mul_le_mul_of_nonneg_left
          (sum_hardyLittlewoodUpperPairIntegral_le N shift A L) (by norm_num)
      _ = 4 * hardyLittlewoodUpperPairSum N := by ring
      _ ≤ 4 * ((N : ℝ) *
          (hardyLittlewoodNearPairConstant +
            hardyLittlewoodFarPairConstant)) :=
        mul_le_mul_of_nonneg_left (hardyLittlewoodUpperPairSum_le N) (by norm_num)
      _ = 4 * (N : ℝ) *
          (hardyLittlewoodNearPairConstant +
            hardyLittlewoodFarPairConstant) := by ring
  rw [hardyLittlewoodFiniteMeanSquare_eq_diag_add_upper]
  exact add_le_add hdiag hupper

theorem hardyLittlewoodFiniteMeanSquare_le_length
    (N : ℕ) (shift A L : ℝ) (hL : 0 ≤ L) (hNL : (N : ℝ) ≤ L) :
    hardyLittlewoodFiniteMeanSquare N shift A L ≤
      L * hardyLittlewoodFiniteMeanSquareConstant := by
  have hpairConstant :
      0 ≤ hardyLittlewoodNearPairConstant +
        hardyLittlewoodFarPairConstant :=
    add_nonneg hardyLittlewoodNearPairConstant_pos.le
      hardyLittlewoodFarPairConstant_pos.le
  calc
    hardyLittlewoodFiniteMeanSquare N shift A L ≤
        L * (6 / Real.log 2) +
          4 * (N : ℝ) *
            (hardyLittlewoodNearPairConstant +
              hardyLittlewoodFarPairConstant) :=
      hardyLittlewoodFiniteMeanSquare_le_length_add_truncation
        N shift A L hL
    _ ≤ L * (6 / Real.log 2) +
          4 * L *
            (hardyLittlewoodNearPairConstant +
              hardyLittlewoodFarPairConstant) := by
      gcongr
    _ = L * hardyLittlewoodFiniteMeanSquareConstant := by
      unfold hardyLittlewoodFiniteMeanSquareConstant
      ring

structure HardyLittlewoodFiniteMeanSquareCertificate : Prop where
  diagonalSummable : Summable hardyLittlewoodLogSquareCoeff
  diagonalBound :
    ∑' n, hardyLittlewoodLogSquareCoeff n ≤ 6 / Real.log 2
  upperPairBound :
    ∀ N : ℕ,
      hardyLittlewoodUpperPairSum N ≤
        (N : ℝ) *
          (hardyLittlewoodNearPairConstant + hardyLittlewoodFarPairConstant)
  exactExpansion :
    ∀ (N : ℕ) (shift A L : ℝ),
      hardyLittlewoodFiniteMeanSquare N shift A L =
        (∑ n ∈ Finset.Icc 2 N,
          L * hardyLittlewoodLogSquareCoeff n) +
        2 * (∑ n ∈ Finset.Icc 2 N,
          ∑ r ∈ Finset.Icc 1 (N - n),
            hardyLittlewoodPairIntegral shift A L n (n + r))
  lengthAddTruncation :
    ∀ (N : ℕ) (shift A L : ℝ), 0 ≤ L →
      hardyLittlewoodFiniteMeanSquare N shift A L ≤
        L * (6 / Real.log 2) +
          4 * (N : ℝ) *
            (hardyLittlewoodNearPairConstant +
              hardyLittlewoodFarPairConstant)
  lengthDominates :
    ∀ (N : ℕ) (shift A L : ℝ), 0 ≤ L → (N : ℝ) ≤ L →
      hardyLittlewoodFiniteMeanSquare N shift A L ≤
        L * hardyLittlewoodFiniteMeanSquareConstant

theorem hardyLittlewoodFiniteMeanSquare_endpoint :
    HardyLittlewoodFiniteMeanSquareCertificate where
  diagonalSummable := summable_hardyLittlewoodLogSquareCoeff
  diagonalBound := tsum_hardyLittlewoodLogSquareCoeff_le
  upperPairBound := hardyLittlewoodUpperPairSum_le
  exactExpansion := hardyLittlewoodFiniteMeanSquare_eq_diag_add_upper
  lengthAddTruncation :=
    hardyLittlewoodFiniteMeanSquare_le_length_add_truncation
  lengthDominates := hardyLittlewoodFiniteMeanSquare_le_length

end LeanLab.Riemann
