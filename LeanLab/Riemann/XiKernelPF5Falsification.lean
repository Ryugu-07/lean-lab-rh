import LeanLab.Riemann.XiKernelStrictLogConcavity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block

set_option linter.style.header false

/-!
# Order-five Pólya-frequency obstruction for the Riemann Xi kernel

This file independently certifies a negative order-five Toeplitz minor of the exact infinite
theta kernel. External interval computations are used only to choose the rational configuration.
-/

open Finset Real

namespace LeanLab.Riemann

noncomputable section

/-- The even physical-space kernel whose cosine transform is the time-zero heat family. -/
def deBruijnNewmanEvenKernel (u : Real) : Real :=
  deBruijnNewmanPhi |u|

/-- The rational Taylor polynomial used by the transcendental certificate. -/
def pf5ExpTaylor (n : Nat) (x : Real) : Real :=
  ∑ m ∈ Finset.range n, x ^ m / m.factorial

/-- The explicit Mathlib remainder bound for `pf5ExpTaylor`. -/
def pf5ExpTaylorError (n : Nat) (x : Real) : Real :=
  |x| ^ n * (n.succ / (n.factorial * n))

theorem pf5ExpTaylor_sub_error_le_exp
    {n : Nat} (hn : 0 < n) {x : Real} (hx : |x| ≤ 1) :
    pf5ExpTaylor n x - pf5ExpTaylorError n x ≤ Real.exp x := by
  have h := Real.exp_bound (x := x) (n := n) hx hn
  have hl := (abs_le.mp h).1
  simp only [pf5ExpTaylor, pf5ExpTaylorError] at hl ⊢
  linarith

theorem pf5Exp_le_taylor_add_error
    {n : Nat} (hn : 0 < n) {x : Real} (hx : |x| ≤ 1) :
    Real.exp x ≤ pf5ExpTaylor n x + pf5ExpTaylorError n x := by
  have h := Real.exp_bound (x := x) (n := n) hx hn
  have hu := (abs_le.mp h).2
  simp only [pf5ExpTaylor, pf5ExpTaylorError] at hu ⊢
  linarith

theorem pf5Exp_between_of_taylor
    {n : Nat} (hn : 0 < n) {x lo hi : Real} (hx : |x| ≤ 1)
    (hlo : lo < pf5ExpTaylor n x - pf5ExpTaylorError n x)
    (hhi : pf5ExpTaylor n x + pf5ExpTaylorError n x < hi) :
    lo < Real.exp x ∧ Real.exp x < hi :=
  ⟨hlo.trans_le (pf5ExpTaylor_sub_error_le_exp hn hx),
    (pf5Exp_le_taylor_add_error hn hx).trans_lt hhi⟩

/-- The nine absolute kernel arguments in diagonal order `i-j=-4,...,4`. -/
def pf5KernelArgument : Fin 9 → Real :=
  ![19 / 100, 14 / 100, 9 / 100, 4 / 100, 1 / 100,
    6 / 100, 11 / 100, 16 / 100, 21 / 100]

def pf5ExpFourLower : Fin 9 → Real :=
  ![21382762204968 / 10000000000000,
    17506725002961 / 10000000000000,
    14333294145603 / 10000000000000,
    11735108709918 / 10000000000000,
    10408107741923 / 10000000000000,
    12712491503214 / 10000000000000,
    15527072185113 / 10000000000000,
    18964808793049 / 10000000000000,
    23163669767810 / 10000000000000]

def pf5ExpFourUpper : Fin 9 → Real :=
  ![21382762204969 / 10000000000000,
    17506725002962 / 10000000000000,
    14333294145604 / 10000000000000,
    11735108709919 / 10000000000000,
    10408107741924 / 10000000000000,
    12712491503215 / 10000000000000,
    15527072185114 / 10000000000000,
    18964808793050 / 10000000000000,
    23163669767811 / 10000000000000]

def pf5ExpFiveHalfLower : Fin 9 → Real :=
  ![16080141974857 / 10000000000000,
    14190675485932 / 10000000000000,
    12523227161918 / 10000000000000,
    11051709180756 / 10000000000000,
    10253151205244 / 10000000000000,
    11618342427282 / 10000000000000,
    13165306748676 / 10000000000000,
    14918246976412 / 10000000000000,
    16904588483790 / 10000000000000]

def pf5ExpFiveHalfUpper : Fin 9 → Real :=
  ![16080141974858 / 10000000000000,
    14190675485933 / 10000000000000,
    12523227161919 / 10000000000000,
    11051709180757 / 10000000000000,
    10253151205245 / 10000000000000,
    11618342427283 / 10000000000000,
    13165306748677 / 10000000000000,
    14918246976413 / 10000000000000,
    16904588483791 / 10000000000000]

theorem pf5_exp_four_bounds (k : Fin 9) :
    pf5ExpFourLower k < Real.exp (4 * pf5KernelArgument k) ∧
      Real.exp (4 * pf5KernelArgument k) < pf5ExpFourUpper k := by
  fin_cases k <;>
    apply pf5Exp_between_of_taylor (n := 24) (by norm_num)
      (by norm_num [pf5KernelArgument]) <;>
    norm_num [pf5KernelArgument, pf5ExpFourLower, pf5ExpFourUpper, pf5ExpTaylor,
      pf5ExpTaylorError, Finset.sum_range_succ, Nat.factorial]

theorem pf5_exp_five_half_bounds (k : Fin 9) :
    pf5ExpFiveHalfLower k < Real.exp (5 * pf5KernelArgument k / 2) ∧
      Real.exp (5 * pf5KernelArgument k / 2) < pf5ExpFiveHalfUpper k := by
  fin_cases k <;>
    apply pf5Exp_between_of_taylor (n := 24) (by norm_num)
      (by norm_num [pf5KernelArgument]) <;>
    norm_num [pf5KernelArgument, pf5ExpFiveHalfLower, pf5ExpFiveHalfUpper, pf5ExpTaylor,
      pf5ExpTaylorError, Finset.sum_range_succ, Nat.factorial]

def pf5GaussianArgLower : Fin 9 → Real :=
  ![8396991082072 / 10000000000000,
    6874874832213 / 10000000000000,
    5628671448695 / 10000000000000,
    4608366414018 / 10000000000000,
    4087254352473 / 10000000000000,
    4992183739413 / 10000000000000,
    6097466988562 / 10000000000000,
    7447462997621 / 10000000000000,
    9096351846590 / 10000000000000]

def pf5GaussianArgUpper : Fin 9 → Real :=
  ![8396991082075 / 10000000000000,
    6874874832216 / 10000000000000,
    5628671448698 / 10000000000000,
    4608366414021 / 10000000000000,
    4087254352476 / 10000000000000,
    4992183739416 / 10000000000000,
    6097466988565 / 10000000000000,
    7447462997624 / 10000000000000,
    9096351846593 / 10000000000000]

def pf5GaussianBaseLower : Fin 9 → Real :=
  ![4318404411268 / 10000000000000,
    5028378718417 / 10000000000000,
    5695736702872 / 10000000000000,
    6307557083504 / 10000000000000,
    6644966546371 / 10000000000000,
    6070049252064 / 10000000000000,
    5434885179034 / 10000000000000,
    4748547554237 / 10000000000000,
    4026710978347 / 10000000000000]

def pf5GaussianBaseUpper : Fin 9 → Real :=
  ![4318404411271 / 10000000000000,
    5028378718420 / 10000000000000,
    5695736702875 / 10000000000000,
    6307557083507 / 10000000000000,
    6644966546374 / 10000000000000,
    6070049252067 / 10000000000000,
    5434885179037 / 10000000000000,
    4748547554240 / 10000000000000,
    4026710978350 / 10000000000000]

theorem pf5_gaussian_arg_bounds (k : Fin 9) :
    pf5GaussianArgLower k <
        Real.pi * Real.exp (4 * pf5KernelArgument k) / 8 ∧
      Real.pi * Real.exp (4 * pf5KernelArgument k) / 8 <
        pf5GaussianArgUpper k := by
  have he := pf5_exp_four_bounds k
  constructor
  · calc
      pf5GaussianArgLower k <
          (3.14159265358979323846 : Real) * pf5ExpFourLower k / 8 := by
        fin_cases k <;>
          norm_num [pf5GaussianArgLower, pf5ExpFourLower]
      _ < Real.pi * pf5ExpFourLower k / 8 := by
        apply div_lt_div_of_pos_right _ (by norm_num)
        exact mul_lt_mul_of_pos_right Real.pi_gt_d20 (by
          fin_cases k <;> norm_num [pf5ExpFourLower])
      _ < Real.pi * Real.exp (4 * pf5KernelArgument k) / 8 := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left he.1 Real.pi_pos) (by norm_num)
  · calc
      Real.pi * Real.exp (4 * pf5KernelArgument k) / 8 <
          (3.14159265358979323847 : Real) *
            Real.exp (4 * pf5KernelArgument k) / 8 := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_right Real.pi_lt_d20 (Real.exp_pos _)) (by norm_num)
      _ < (3.14159265358979323847 : Real) * pf5ExpFourUpper k / 8 := by
        apply div_lt_div_of_pos_right _ (by norm_num)
        exact mul_lt_mul_of_pos_left he.2 (by norm_num)
      _ < pf5GaussianArgUpper k := by
        fin_cases k <;>
          norm_num [pf5GaussianArgUpper, pf5ExpFourUpper]

private theorem pf5_gaussian_base_lower_vs_arg_upper (k : Fin 9) :
    pf5GaussianBaseLower k < Real.exp (-pf5GaussianArgUpper k) := by
  have h := pf5ExpTaylor_sub_error_le_exp (n := 24) (by norm_num)
    (x := -pf5GaussianArgUpper k) (by
      fin_cases k <;> norm_num [pf5GaussianArgUpper])
  apply lt_of_lt_of_le _ h
  fin_cases k <;>
    norm_num [pf5GaussianBaseLower, pf5GaussianArgUpper, pf5ExpTaylor,
      pf5ExpTaylorError, Finset.sum_range_succ, Nat.factorial]

private theorem pf5_gaussian_base_upper_vs_arg_lower (k : Fin 9) :
    Real.exp (-pf5GaussianArgLower k) < pf5GaussianBaseUpper k := by
  have h := pf5Exp_le_taylor_add_error (n := 24) (by norm_num)
    (x := -pf5GaussianArgLower k) (by
      fin_cases k <;> norm_num [pf5GaussianArgLower])
  apply lt_of_le_of_lt h
  fin_cases k <;>
    norm_num [pf5GaussianBaseUpper, pf5GaussianArgLower, pf5ExpTaylor,
      pf5ExpTaylorError, Finset.sum_range_succ, Nat.factorial]

theorem pf5_gaussian_base_bounds (k : Fin 9) :
    pf5GaussianBaseLower k <
        Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ∧
      Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) <
        pf5GaussianBaseUpper k := by
  have ha := pf5_gaussian_arg_bounds k
  constructor
  · exact (pf5_gaussian_base_lower_vs_arg_upper k).trans_le
      (Real.exp_le_exp.mpr (neg_le_neg ha.2.le))
  · exact (Real.exp_le_exp.mpr (neg_le_neg ha.1.le)).trans_lt
      (pf5_gaussian_base_upper_vs_arg_lower k)

/-- A kernel summand expressed through the three transcendental quantities certified above. -/
theorem deBruijnNewmanPhiTerm_eq_pf5_factors
    (n : Nat) (u : Real) :
    deBruijnNewmanPhiTerm n u =
      Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (5 * u / 2) ^ 2 *
        (2 * Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u) - 3) *
          Real.exp (-(Real.pi * Real.exp (4 * u) / 8)) ^
            (8 * (n + 1) ^ 2) := by
  have h5 : Real.exp (5 * u) = Real.exp (5 * u / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hGaussian :
      Real.exp (-Real.pi * ((n : Real) + 1) ^ 2 * Real.exp (4 * u)) =
        Real.exp (-(Real.pi * Real.exp (4 * u) / 8)) ^
          (8 * (n + 1) ^ 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [deBruijnNewmanPhiTerm_eq, h9, h5, hGaussian]
  ring

/-- Rational lower endpoints for the first three summands at the nine witness arguments. -/
def pf5PhiTermLower : Fin 3 → Fin 9 → Real :=
  fun r k => if r.1 = 0 then
    ![102521818405 / 1000000000000,
      206851637009 / 1000000000000,
      327761447354 / 1000000000000,
      420451709048 / 1000000000000,
      444387698705 / 1000000000000,
      389814797882 / 1000000000000,
      280040645436 / 1000000000000,
      161153212363 / 1000000000000,
      71697041786 / 1000000000000] k
  else if r.1 = 1 then
    ![3527 / 1000000000000,
      289525 / 1000000000000,
      9796307 / 1000000000000,
      160238511 / 1000000000000,
      638856363 / 1000000000000,
      56662703 / 1000000000000,
      2634833 / 1000000000000,
      55788 / 1000000000000,
      452 / 1000000000000] k
  else
    ![0,
      0,
      0,
      8 / 1000000000000,
      275 / 1000000000000,
      0,
      0,
      0,
      0] k

/-- Rational upper endpoints for the first three summands at the nine witness arguments. -/
def pf5PhiTermUpper : Fin 3 → Fin 9 → Real :=
  fun r k => if r.1 = 0 then
    ![102521818407 / 1000000000000,
      206851637011 / 1000000000000,
      327761447356 / 1000000000000,
      420451709051 / 1000000000000,
      444387698708 / 1000000000000,
      389814797885 / 1000000000000,
      280040645439 / 1000000000000,
      161153212365 / 1000000000000,
      71697041788 / 1000000000000] k
  else if r.1 = 1 then
    ![3528 / 1000000000000,
      289526 / 1000000000000,
      9796308 / 1000000000000,
      160238512 / 1000000000000,
      638856364 / 1000000000000,
      56662704 / 1000000000000,
      2634834 / 1000000000000,
      55789 / 1000000000000,
      453 / 1000000000000] k
  else
    ![1 / 1000000000000,
      1 / 1000000000000,
      1 / 1000000000000,
      9 / 1000000000000,
      276 / 1000000000000,
      1 / 1000000000000,
      1 / 1000000000000,
      1 / 1000000000000,
      1 / 1000000000000] k

private theorem pf5_term_lower_lt_rational_factors (r : Fin 3) (k : Fin 9) :
    pf5PhiTermLower r k <
      (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 *
        pf5ExpFiveHalfLower k ^ 2 *
          (2 * (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 *
            pf5ExpFourLower k - 3) *
            pf5GaussianBaseLower k ^ (8 * ((r : Nat) + 1) ^ 2) := by
  fin_cases r <;> fin_cases k <;>
    norm_num [pf5PhiTermLower, pf5ExpFourLower, pf5ExpFiveHalfLower,
      pf5GaussianBaseLower, pow_succ]

private theorem pf5_rational_factors_lt_term_upper (r : Fin 3) (k : Fin 9) :
    (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
          pf5ExpFiveHalfUpper k ^ 2 *
            (2 * (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
              pf5ExpFourUpper k - 3) *
              pf5GaussianBaseUpper k ^ (8 * ((r : Nat) + 1) ^ 2) <
      pf5PhiTermUpper r k := by
  fin_cases r <;> fin_cases k <;>
    norm_num [pf5PhiTermUpper, pf5ExpFourUpper, pf5ExpFiveHalfUpper,
      pf5GaussianBaseUpper, pow_succ]

theorem pf5_first_three_term_bounds (r : Fin 3) (k : Fin 9) :
    pf5PhiTermLower r k <
        deBruijnNewmanPhiTerm r (pf5KernelArgument k) ∧
      deBruijnNewmanPhiTerm r (pf5KernelArgument k) <
        pf5PhiTermUpper r k := by
  have he4 := pf5_exp_four_bounds k
  have he25 := pf5_exp_five_half_bounds k
  have hq := pf5_gaussian_base_bounds k
  have he4Lower : 0 < pf5ExpFourLower k := by
    fin_cases k <;> norm_num [pf5ExpFourLower]
  have he4Upper : 0 < pf5ExpFourUpper k := by
    fin_cases k <;> norm_num [pf5ExpFourUpper]
  have he25Lower : 0 < pf5ExpFiveHalfLower k := by
    fin_cases k <;> norm_num [pf5ExpFiveHalfLower]
  have he25Upper : 0 < pf5ExpFiveHalfUpper k := by
    fin_cases k <;> norm_num [pf5ExpFiveHalfUpper]
  have hqLower : 0 < pf5GaussianBaseLower k := by
    fin_cases k <;> norm_num [pf5GaussianBaseLower]
  have hqUpper : 0 < pf5GaussianBaseUpper k := by
    fin_cases k <;> norm_num [pf5GaussianBaseUpper]
  have hmSq : 0 ≤ ((r : Real) + 1) ^ 2 := sq_nonneg _
  have hcoreLower :
      0 < 2 * (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 *
          pf5ExpFourLower k - 3 := by
    fin_cases r <;> fin_cases k <;> norm_num [pf5ExpFourLower]
  have hpiFactorLower :
      (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 ≤
        Real.pi * ((r : Real) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right Real.pi_gt_d20.le hmSq
  have hpiFactorUpper :
      Real.pi * ((r : Real) + 1) ^ 2 ≤
        (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right Real.pi_lt_d20.le hmSq
  have hcoreLowerLe :
      2 * (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 *
          pf5ExpFourLower k - 3 ≤
        2 * Real.pi * ((r : Real) + 1) ^ 2 *
          Real.exp (4 * pf5KernelArgument k) - 3 := by
    have hmul := mul_le_mul hpiFactorLower he4.1.le he4Lower.le
      (mul_nonneg Real.pi_pos.le hmSq)
    nlinarith
  have hcoreUpperLe :
      2 * Real.pi * ((r : Real) + 1) ^ 2 *
          Real.exp (4 * pf5KernelArgument k) - 3 ≤
        2 * (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
          pf5ExpFourUpper k - 3 := by
    have hmul := mul_le_mul hpiFactorUpper he4.2.le (Real.exp_pos _).le
      (mul_nonneg (by norm_num) hmSq)
    nlinarith
  have hcoreActual :
      0 < 2 * Real.pi * ((r : Real) + 1) ^ 2 *
          Real.exp (4 * pf5KernelArgument k) - 3 :=
    hcoreLower.trans_le hcoreLowerLe
  have hcoreUpper :
      0 < 2 * (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
          pf5ExpFourUpper k - 3 :=
    hcoreActual.trans_le hcoreUpperLe
  have he25SqLower :
      pf5ExpFiveHalfLower k ^ 2 ≤
        Real.exp (5 * pf5KernelArgument k / 2) ^ 2 :=
    pow_le_pow_left₀ he25Lower.le he25.1.le 2
  have he25SqUpper :
      Real.exp (5 * pf5KernelArgument k / 2) ^ 2 ≤
        pf5ExpFiveHalfUpper k ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le he25.2.le 2
  have hqPowLower :
      pf5GaussianBaseLower k ^ (8 * ((r : Nat) + 1) ^ 2) ≤
        Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
          (8 * ((r : Nat) + 1) ^ 2) :=
    pow_le_pow_left₀ hqLower.le hq.1.le _
  have hqPowUpper :
      Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
          (8 * ((r : Nat) + 1) ^ 2) ≤
        pf5GaussianBaseUpper k ^ (8 * ((r : Nat) + 1) ^ 2) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hq.2.le _
  have hqPowLowerNonneg :
      0 ≤ pf5GaussianBaseLower k ^ (8 * ((r : Nat) + 1) ^ 2) :=
    pow_nonneg hqLower.le _
  have hqPowActualNonneg :
      0 ≤ Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
          (8 * ((r : Nat) + 1) ^ 2) :=
    pow_nonneg (Real.exp_pos _).le _
  have hprefixActualNonneg :
      0 ≤ Real.pi * ((r : Real) + 1) ^ 2 *
          Real.exp (5 * pf5KernelArgument k / 2) ^ 2 *
            (2 * Real.pi * ((r : Real) + 1) ^ 2 *
              Real.exp (4 * pf5KernelArgument k) - 3) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg Real.pi_pos.le hmSq) (sq_nonneg _))
      hcoreActual.le
  have hprefixUpperNonneg :
      0 ≤ (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
          pf5ExpFiveHalfUpper k ^ 2 *
            (2 * (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
              pf5ExpFourUpper k - 3) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hmSq) (sq_nonneg _))
      hcoreUpper.le
  rw [deBruijnNewmanPhiTerm_eq_pf5_factors]
  constructor
  · calc
      pf5PhiTermLower r k <
          (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 *
            pf5ExpFiveHalfLower k ^ 2 *
              (2 * (3.14159265358979323846 : Real) * ((r : Real) + 1) ^ 2 *
                pf5ExpFourLower k - 3) *
                pf5GaussianBaseLower k ^ (8 * ((r : Nat) + 1) ^ 2) := by
        exact pf5_term_lower_lt_rational_factors r k
      _ ≤ Real.pi * ((r : Real) + 1) ^ 2 *
            Real.exp (5 * pf5KernelArgument k / 2) ^ 2 *
              (2 * Real.pi * ((r : Real) + 1) ^ 2 *
                Real.exp (4 * pf5KernelArgument k) - 3) *
                Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
                  (8 * ((r : Nat) + 1) ^ 2) := by
        have hfirst := mul_le_mul hpiFactorLower he25SqLower
          (sq_nonneg _) (mul_nonneg Real.pi_pos.le hmSq)
        have hsecond := mul_le_mul hfirst hcoreLowerLe hcoreLower.le
          (mul_nonneg (mul_nonneg Real.pi_pos.le hmSq) (sq_nonneg _))
        exact mul_le_mul hsecond hqPowLower hqPowLowerNonneg hprefixActualNonneg
  · calc
      Real.pi * ((r : Real) + 1) ^ 2 *
            Real.exp (5 * pf5KernelArgument k / 2) ^ 2 *
              (2 * Real.pi * ((r : Real) + 1) ^ 2 *
                Real.exp (4 * pf5KernelArgument k) - 3) *
                Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
                  (8 * ((r : Nat) + 1) ^ 2) ≤
          (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
            pf5ExpFiveHalfUpper k ^ 2 *
              (2 * (3.14159265358979323847 : Real) * ((r : Real) + 1) ^ 2 *
                pf5ExpFourUpper k - 3) *
                pf5GaussianBaseUpper k ^ (8 * ((r : Nat) + 1) ^ 2) := by
        have hfirst := mul_le_mul hpiFactorUpper he25SqUpper (sq_nonneg _)
          (mul_nonneg (by norm_num) hmSq)
        have hsecond := mul_le_mul hfirst hcoreUpperLe hcoreActual.le
          (mul_nonneg (mul_nonneg (by norm_num) hmSq) (sq_nonneg _))
        exact mul_le_mul hsecond hqPowUpper hqPowActualNonneg hprefixUpperNonneg
      _ < pf5PhiTermUpper r k := by
        exact pf5_rational_factors_lt_term_upper r k

private theorem pf5_nat_succ_le_two_pow (n : Nat) :
    n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n.succ + 1 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ n.succ := by rw [pow_succ]; ring

/-- Each summand after the first three is bounded by a rapidly decaying geometric sequence. -/
theorem pf5_phi_tail_term_le_geometric
    (n : Nat) (hn : 3 ≤ n) (k : Fin 9) :
    deBruijnNewmanPhiTerm n (pf5KernelArgument k) ≤
      384 * (16 * (2 / 3 : Real) ^ 40) ^ n := by
  have hu : 0 ≤ pf5KernelArgument k := by
    fin_cases k <;> norm_num [pf5KernelArgument]
  have he4 := pf5_exp_four_bounds k
  have he25 := pf5_exp_five_half_bounds k
  have hq := pf5_gaussian_base_bounds k
  have he4Three : Real.exp (4 * pf5KernelArgument k) ≤ 3 := by
    exact he4.2.le.trans (by
      fin_cases k <;> norm_num [pf5ExpFourUpper])
  have he25Two : Real.exp (5 * pf5KernelArgument k / 2) ≤ 2 := by
    exact he25.2.le.trans (by
      fin_cases k <;> norm_num [pf5ExpFiveHalfUpper])
  have hqTwoThirds :
      Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ≤ 2 / 3 := by
    exact hq.2.le.trans (by
      fin_cases k <;> norm_num [pf5GaussianBaseUpper])
  have hmOne : 1 ≤ (n : Real) + 1 := by
    have hn0 : 0 ≤ (n : Real) := by positivity
    linarith
  have hmSqOne : 1 ≤ ((n : Real) + 1) ^ 2 := by nlinarith
  have hmSq : 0 ≤ ((n : Real) + 1) ^ 2 := sq_nonneg _
  have he4One : 1 ≤ Real.exp (4 * pf5KernelArgument k) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpiExp : Real.pi ≤
      Real.pi * ((n : Real) + 1) ^ 2 *
        Real.exp (4 * pf5KernelArgument k) := by
    calc
      Real.pi ≤ Real.pi * ((n : Real) + 1) ^ 2 :=
        le_mul_of_one_le_right Real.pi_pos.le hmSqOne
      _ ≤ Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (4 * pf5KernelArgument k) :=
        le_mul_of_one_le_right (by positivity) he4One
  have hcorePos :
      0 < 2 * Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (4 * pf5KernelArgument k) - 3 := by
    nlinarith [Real.pi_gt_three]
  have hpiFour : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
  have he25SqFour : Real.exp (5 * pf5KernelArgument k / 2) ^ 2 ≤ 4 := by
    simpa only [show (4 : Real) = 2 ^ 2 by norm_num] using
      pow_le_pow_left₀ (Real.exp_pos _).le he25Two 2
  have hfirstFactor :
      Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (5 * pf5KernelArgument k / 2) ^ 2 ≤
        16 * ((n : Real) + 1) ^ 2 := by
    have hpiExp25 :
        Real.pi * Real.exp (5 * pf5KernelArgument k / 2) ^ 2 ≤ 4 * 4 :=
      mul_le_mul hpiFour he25SqFour (sq_nonneg _) (by norm_num)
    calc
      Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (5 * pf5KernelArgument k / 2) ^ 2 =
          (Real.pi * Real.exp (5 * pf5KernelArgument k / 2) ^ 2) *
            ((n : Real) + 1) ^ 2 := by ring
      _ ≤ (4 * 4) * ((n : Real) + 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hpiExp25 hmSq
      _ = 16 * ((n : Real) + 1) ^ 2 := by ring
  have hcoreUpper :
      2 * Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (4 * pf5KernelArgument k) - 3 ≤
        24 * ((n : Real) + 1) ^ 2 := by
    have hpiExp4 :
        Real.pi * Real.exp (4 * pf5KernelArgument k) ≤ 4 * 3 :=
      mul_le_mul hpiFour he4Three (Real.exp_pos _).le (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hpiExp4 hmSq
    nlinarith
  have houter :
      Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (5 * pf5KernelArgument k / 2) ^ 2 *
            (2 * Real.pi * ((n : Real) + 1) ^ 2 *
              Real.exp (4 * pf5KernelArgument k) - 3) ≤
        384 * ((n : Real) + 1) ^ 4 := by
    calc
      Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (5 * pf5KernelArgument k / 2) ^ 2 *
            (2 * Real.pi * ((n : Real) + 1) ^ 2 *
              Real.exp (4 * pf5KernelArgument k) - 3) ≤
          (16 * ((n : Real) + 1) ^ 2) *
            (24 * ((n : Real) + 1) ^ 2) :=
        mul_le_mul hfirstFactor hcoreUpper hcorePos.le (by positivity)
      _ = 384 * ((n : Real) + 1) ^ 4 := by ring
  have hqPow :
      Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
          (8 * (n + 1) ^ 2) ≤
        (2 / 3 : Real) ^ (8 * (n + 1) ^ 2) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hqTwoThirds _
  have hmPow : ((n : Real) + 1) ^ 4 ≤ (16 : Real) ^ n := by
    have hm : (n : Real) + 1 ≤ (2 : Real) ^ n := by
      exact_mod_cast pf5_nat_succ_le_two_pow n
    calc
      ((n : Real) + 1) ^ 4 ≤ ((2 : Real) ^ n) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hm 4
      _ = (16 : Real) ^ n := by
        rw [show (16 : Real) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_mul]
        congr 1
        omega
  have hnReal : (3 : Real) ≤ n := by exact_mod_cast hn
  have hdegreeReal :
      40 * (n : Real) ≤ 8 * ((n : Real) + 1) ^ 2 := by
    nlinarith [mul_nonneg (by positivity : (0 : Real) ≤ n) (sub_nonneg.mpr hnReal)]
  have hdegree : 40 * n ≤ 8 * (n + 1) ^ 2 := by
    exact_mod_cast hdegreeReal
  have hqDegree :
      (2 / 3 : Real) ^ (8 * (n + 1) ^ 2) ≤
        (2 / 3 : Real) ^ (40 * n) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hdegree
  rw [deBruijnNewmanPhiTerm_eq_pf5_factors]
  calc
    Real.pi * ((n : Real) + 1) ^ 2 *
          Real.exp (5 * pf5KernelArgument k / 2) ^ 2 *
            (2 * Real.pi * ((n : Real) + 1) ^ 2 *
              Real.exp (4 * pf5KernelArgument k) - 3) *
              Real.exp (-(Real.pi * Real.exp (4 * pf5KernelArgument k) / 8)) ^
                (8 * (n + 1) ^ 2) ≤
        (384 * ((n : Real) + 1) ^ 4) *
          (2 / 3 : Real) ^ (40 * n) := by
      exact mul_le_mul houter (hqPow.trans hqDegree) (by positivity) (by positivity)
    _ ≤ (384 * (16 : Real) ^ n) * (2 / 3 : Real) ^ (40 * n) := by
      gcongr
    _ = 384 * (16 * (2 / 3 : Real) ^ 40) ^ n := by
      rw [pow_mul, mul_pow]
      ring

private theorem pf5_geometric_ratio_lt_one :
    16 * (2 / 3 : Real) ^ 40 < 1 := by
  norm_num [pow_succ]

private theorem pf5_geometric_tail_numeric :
    384 * (16 * (2 / 3 : Real) ^ 40) ^ 3 *
        (1 - 16 * (2 / 3 : Real) ^ 40)⁻¹ <
      (1 / 1000000000000 : Real) := by
  norm_num [pow_succ]

/-- The complete Xi-kernel tail after the first three summands is below `10^-12`. -/
theorem pf5_phi_tail_tsum_lt (k : Fin 9) :
    (∑' j : Nat, deBruijnNewmanPhiTerm (j + 3) (pf5KernelArgument k)) <
      (1 / 1000000000000 : Real) := by
  let rho : Real := 16 * (2 / 3 : Real) ^ 40
  let tail : Nat → Real := fun j =>
    deBruijnNewmanPhiTerm (j + 3) (pf5KernelArgument k)
  let major : Nat → Real := fun j => (384 * rho ^ 3) * rho ^ j
  have hrho0 : 0 ≤ rho := by dsimp only [rho]; positivity
  have hrho1 : rho < 1 := by
    simpa only [rho] using pf5_geometric_ratio_lt_one
  have hmajor : Summable major := by
    have hgeo := summable_geometric_of_lt_one hrho0 hrho1
    exact hgeo.mul_left (384 * rho ^ 3)
  have htail : Summable tail := by
    exact (summable_deBruijnNewmanPhiTerm (pf5KernelArgument k)).comp_injective
      (fun _ _ h => by omega)
  have hpoint : ∀ j : Nat, tail j ≤ major j := by
    intro j
    have h := pf5_phi_tail_term_le_geometric (j + 3) (by omega) k
    simpa only [tail, major, rho, pow_add, mul_assoc, mul_comm, mul_left_comm] using h
  calc
    (∑' j : Nat, deBruijnNewmanPhiTerm (j + 3) (pf5KernelArgument k)) =
        ∑' j : Nat, tail j := by rfl
    _ ≤ ∑' j : Nat, major j := htail.tsum_le_tsum hpoint hmajor
    _ = 384 * rho ^ 3 * (1 - rho)⁻¹ := by
      simp only [major, tsum_mul_left,
        tsum_geometric_of_lt_one hrho0 hrho1]
    _ < (1 / 1000000000000 : Real) := by
      simpa only [rho] using pf5_geometric_tail_numeric

def pf5PhiLower : Fin 9 → Real :=
  ![102521821932 / 1000000000000,
    206851926534 / 1000000000000,
    327771243661 / 1000000000000,
    420611947567 / 1000000000000,
    445026555343 / 1000000000000,
    389871460585 / 1000000000000,
    280043280269 / 1000000000000,
    161153268151 / 1000000000000,
    71697042238 / 1000000000000]

def pf5PhiUpper : Fin 9 → Real :=
  ![102521821937 / 1000000000000,
    206851926539 / 1000000000000,
    327771243666 / 1000000000000,
    420611947573 / 1000000000000,
    445026555349 / 1000000000000,
    389871460591 / 1000000000000,
    280043280275 / 1000000000000,
    161153268156 / 1000000000000,
    71697042243 / 1000000000000]

/-- Rational centers used by the determinant perturbation certificate. -/
def pf5PhiCenter : Fin 9 → Real :=
  ![102521821934 / 1000000000000,
    206851926536 / 1000000000000,
    327771243663 / 1000000000000,
    420611947570 / 1000000000000,
    445026555346 / 1000000000000,
    389871460588 / 1000000000000,
    280043280272 / 1000000000000,
    161153268153 / 1000000000000,
    71697042240 / 1000000000000]

theorem pf5_phi_bounds (k : Fin 9) :
    pf5PhiLower k < deBruijnNewmanPhi (pf5KernelArgument k) ∧
      deBruijnNewmanPhi (pf5KernelArgument k) < pf5PhiUpper k := by
  have hu : 0 ≤ pf5KernelArgument k := by
    fin_cases k <;> norm_num [pf5KernelArgument]
  have h0 := pf5_first_three_term_bounds (0 : Fin 3) k
  have h1 := pf5_first_three_term_bounds (1 : Fin 3) k
  have h2 := pf5_first_three_term_bounds (2 : Fin 3) k
  have htail := pf5_phi_tail_tsum_lt k
  have htail0 :
      0 ≤ ∑' j : Nat, deBruijnNewmanPhiTerm (j + 3) (pf5KernelArgument k) :=
    tsum_nonneg fun j => (deBruijnNewmanPhiTerm_pos (j + 3) hu).le
  have hsplit :=
    (summable_deBruijnNewmanPhiTerm (pf5KernelArgument k)).sum_add_tsum_nat_add 3
  have hphi :
      deBruijnNewmanPhi (pf5KernelArgument k) =
        deBruijnNewmanPhiTerm 0 (pf5KernelArgument k) +
          deBruijnNewmanPhiTerm 1 (pf5KernelArgument k) +
            deBruijnNewmanPhiTerm 2 (pf5KernelArgument k) +
              ∑' j : Nat, deBruijnNewmanPhiTerm (j + 3) (pf5KernelArgument k) := by
    rw [deBruijnNewmanPhi]
    calc
      (∑' n : Nat, deBruijnNewmanPhiTerm n (pf5KernelArgument k)) =
          (∑ n ∈ Finset.range 3,
              deBruijnNewmanPhiTerm n (pf5KernelArgument k)) +
            ∑' j : Nat, deBruijnNewmanPhiTerm (j + 3) (pf5KernelArgument k) :=
        hsplit.symm
      _ = _ := by norm_num [Finset.sum_range_succ]
  have hlNumeric :
      pf5PhiLower k =
        pf5PhiTermLower (0 : Fin 3) k +
          pf5PhiTermLower (1 : Fin 3) k +
            pf5PhiTermLower (2 : Fin 3) k := by
    fin_cases k <;>
      norm_num [pf5PhiLower, pf5PhiTermLower]
  have huNumeric :
      pf5PhiUpper k =
        pf5PhiTermUpper (0 : Fin 3) k +
          pf5PhiTermUpper (1 : Fin 3) k +
            pf5PhiTermUpper (2 : Fin 3) k + 1 / 1000000000000 := by
    fin_cases k <;>
      norm_num [pf5PhiUpper, pf5PhiTermUpper]
  change pf5PhiTermLower (0 : Fin 3) k <
      deBruijnNewmanPhiTerm 0 (pf5KernelArgument k) ∧
    deBruijnNewmanPhiTerm 0 (pf5KernelArgument k) <
      pf5PhiTermUpper (0 : Fin 3) k at h0
  change pf5PhiTermLower (1 : Fin 3) k <
      deBruijnNewmanPhiTerm 1 (pf5KernelArgument k) ∧
    deBruijnNewmanPhiTerm 1 (pf5KernelArgument k) <
      pf5PhiTermUpper (1 : Fin 3) k at h1
  change pf5PhiTermLower (2 : Fin 3) k <
      deBruijnNewmanPhiTerm 2 (pf5KernelArgument k) ∧
    deBruijnNewmanPhiTerm 2 (pf5KernelArgument k) <
      pf5PhiTermUpper (2 : Fin 3) k at h2
  constructor
  · rw [hphi, hlNumeric]
    linarith
  · rw [hphi, huNumeric]
    linarith

theorem pf5_phi_center_error (k : Fin 9) :
    |deBruijnNewmanPhi (pf5KernelArgument k) - pf5PhiCenter k| <
      (3 / 1000000000000 : Real) := by
  have h := pf5_phi_bounds k
  rw [abs_lt]
  constructor
  · fin_cases k <;>
      norm_num [pf5PhiLower, pf5PhiCenter] at h ⊢ <;>
      linarith
  · fin_cases k <;>
      norm_num [pf5PhiUpper, pf5PhiCenter] at h ⊢ <;>
      linarith

/-- The diagonal number `i-j=-4,...,4`, shifted to `Fin 9`. -/
def pf5DiagonalIndex (i j : Fin 5) : Fin 9 :=
  ⟨i.1 + 4 - j.1, by omega⟩

def xiKernelPF5PhiMatrix : Matrix (Fin 5) (Fin 5) Real :=
  fun i j => deBruijnNewmanPhi (pf5KernelArgument (pf5DiagonalIndex i j))

def xiKernelPF5CenterMatrix : Matrix (Fin 5) (Fin 5) Real :=
  fun i j => pf5PhiCenter (pf5DiagonalIndex i j)

private theorem abs_mul_five_le_eps_half
    {eps x0 x1 x2 x3 x4 : Real} (heps : 0 ≤ eps)
    (h0 : |x0| ≤ eps) (h1 : |x1| ≤ 1 / 2) (h2 : |x2| ≤ 1 / 2)
    (h3 : |x3| ≤ 1 / 2) (h4 : |x4| ≤ 1 / 2) :
    |x0 * x1 * x2 * x3 * x4| ≤ eps * (1 / 2 : Real) ^ 4 := by
  have hhalf : (0 : Real) ≤ 1 / 2 := by norm_num
  have h01 : |x0| * |x1| ≤ eps * (1 / 2 : Real) :=
    mul_le_mul h0 h1 (abs_nonneg _) heps
  have h012 : |x0| * |x1| * |x2| ≤
      eps * (1 / 2 : Real) * (1 / 2 : Real) :=
    mul_le_mul h01 h2 (abs_nonneg _) (mul_nonneg heps hhalf)
  have h0123 : |x0| * |x1| * |x2| * |x3| ≤
      eps * (1 / 2 : Real) * (1 / 2 : Real) * (1 / 2 : Real) :=
    mul_le_mul h012 h3 (abs_nonneg _)
      (mul_nonneg (mul_nonneg heps hhalf) hhalf)
  have h01234 : |x0| * |x1| * |x2| * |x3| * |x4| ≤
      eps * (1 / 2 : Real) * (1 / 2 : Real) * (1 / 2 : Real) * (1 / 2 : Real) :=
    mul_le_mul h0123 h4 (abs_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg heps hhalf) hhalf) hhalf)
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  exact h01234.trans_eq (by ring)

theorem abs_prod_fin_five_sub_prod_fin_five_le
    (a b : Fin 5 → Real) {eps : Real} (heps : 0 ≤ eps)
    (ha : ∀ i, |a i| ≤ 1 / 2) (hb : ∀ i, |b i| ≤ 1 / 2)
    (hab : ∀ i, |a i - b i| ≤ eps) :
    |(∏ i, a i) - ∏ i, b i| ≤ 5 * eps * (1 / 2 : Real) ^ 4 := by
  let t : Fin 5 → Real :=
    ![(a 0 - b 0) * a 1 * a 2 * a 3 * a 4,
      b 0 * (a 1 - b 1) * a 2 * a 3 * a 4,
      b 0 * b 1 * (a 2 - b 2) * a 3 * a 4,
      b 0 * b 1 * b 2 * (a 3 - b 3) * a 4,
      b 0 * b 1 * b 2 * b 3 * (a 4 - b 4)]
  have htel : (∏ i, a i) - ∏ i, b i = ∑ i, t i := by
    rw [Fin.prod_univ_five, Fin.prod_univ_five, Fin.sum_univ_five]
    change a 0 * a 1 * a 2 * a 3 * a 4 - b 0 * b 1 * b 2 * b 3 * b 4 =
      (a 0 - b 0) * a 1 * a 2 * a 3 * a 4 +
        b 0 * (a 1 - b 1) * a 2 * a 3 * a 4 +
          b 0 * b 1 * (a 2 - b 2) * a 3 * a 4 +
            b 0 * b 1 * b 2 * (a 3 - b 3) * a 4 +
              b 0 * b 1 * b 2 * b 3 * (a 4 - b 4)
    ring
  rw [htel]
  calc
    |∑ i, t i| ≤ ∑ i, |t i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, eps * (1 / 2 : Real) ^ 4 := by
      apply Finset.sum_le_sum
      intro i _hi
      fin_cases i
      · change |(a 0 - b 0) * a 1 * a 2 * a 3 * a 4| ≤
          eps * (1 / 2 : Real) ^ 4
        exact abs_mul_five_le_eps_half heps (hab 0) (ha 1) (ha 2) (ha 3) (ha 4)
      · change |b 0 * (a 1 - b 1) * a 2 * a 3 * a 4| ≤
          eps * (1 / 2 : Real) ^ 4
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          abs_mul_five_le_eps_half heps (hab 1) (hb 0) (ha 2) (ha 3) (ha 4)
      · change |b 0 * b 1 * (a 2 - b 2) * a 3 * a 4| ≤
          eps * (1 / 2 : Real) ^ 4
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          abs_mul_five_le_eps_half heps (hab 2) (hb 0) (hb 1) (ha 3) (ha 4)
      · change |b 0 * b 1 * b 2 * (a 3 - b 3) * a 4| ≤
          eps * (1 / 2 : Real) ^ 4
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          abs_mul_five_le_eps_half heps (hab 3) (hb 0) (hb 1) (hb 2) (ha 4)
      · change |b 0 * b 1 * b 2 * b 3 * (a 4 - b 4)| ≤
          eps * (1 / 2 : Real) ^ 4
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          abs_mul_five_le_eps_half heps (hab 4) (hb 0) (hb 1) (hb 2) (hb 3)
    _ = 5 * eps * (1 / 2 : Real) ^ 4 := by
      simp only [Fin.sum_univ_five]
      ring

theorem xiKernelPF5CenterMatrix_abs_le (i j : Fin 5) :
    |xiKernelPF5CenterMatrix i j| ≤ (9 / 20 : Real) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [xiKernelPF5CenterMatrix, pf5DiagonalIndex, pf5PhiCenter, abs_of_nonneg]

theorem xiKernelPF5PhiMatrix_abs_le (i j : Fin 5) :
    |xiKernelPF5PhiMatrix i j| ≤ (1 / 2 : Real) := by
  have herr := pf5_phi_center_error (pf5DiagonalIndex i j)
  have hcenter := xiKernelPF5CenterMatrix_abs_le i j
  have htriangle :
      |xiKernelPF5PhiMatrix i j| ≤
        |xiKernelPF5PhiMatrix i j - xiKernelPF5CenterMatrix i j| +
          |xiKernelPF5CenterMatrix i j| := by
    calc
      |xiKernelPF5PhiMatrix i j| =
          |(xiKernelPF5PhiMatrix i j - xiKernelPF5CenterMatrix i j) +
            xiKernelPF5CenterMatrix i j| := by congr 1; ring
      _ ≤ |xiKernelPF5PhiMatrix i j - xiKernelPF5CenterMatrix i j| +
          |xiKernelPF5CenterMatrix i j| := abs_add_le _ _
  have herr' :
      |xiKernelPF5PhiMatrix i j - xiKernelPF5CenterMatrix i j| <
        (3 / 1000000000000 : Real) := by
    simpa only [xiKernelPF5PhiMatrix, xiKernelPF5CenterMatrix] using herr
  linarith

private def pf5CenterLower : Matrix (Fin 5) (Fin 5) Real :=
  ![![1, 0, 0, 0, 0],
    ![194935730294 / 222513277673, 1, 0, 0, 0],
    ![140021640136 / 222513277673,
      13928400903523540091102 / 8516010155811805952139, 1, 0, 0],
    ![161153268153 / 445026555346,
      28421853196069405597951 / 17032020311623611904278,
      825440033731579883994315251178731 / 348848532188969808135256467109916,
      1, 0],
    ![35848521120 / 222513277673,
      6926808539550813056523 / 5677340103874537301426,
      274218551261253486489508098818898 / 87212133047242452033814116777479,
      3170822508191136147612052817061918955153901 /
        956867843400246331163866810302241146414445,
      1]]

private def pf5CenterUpper : Matrix (Fin 5) (Fin 5) Real :=
  ![![222513277673 / 500000000000, 42061194757 / 100000000000,
      327771243663 / 1000000000000, 25856490817 / 125000000000,
      51260910967 / 500000000000],
    ![0, 8516010155811805952139 / 111256638836500000000000,
      3712177041175650372211 / 27814159709125000000000,
      6522124478478732590923 / 44502655534600000000000,
      6510533484181061890533 / 55628319418250000000000],
    ![0, 0,
      87212133047242452033814116777479 / 4258005077905902976069500000000000,
      108037212377055863863141963443073 / 2129002538952951488034750000000000,
      203923553369866741470923940835519 / 2838670051937268650713000000000000],
    ![0, 0, 0,
      191373568680049266232773362060448229282889 /
        34884853218896980813525646710991600000000000,
      6350203983822738976456413546479786626668127 /
        348848532188969808135256467109916000000000000],
    ![0, 0, 0, 0,
      -(1847235982628972102465848504505468385696544265663373 : Real) /
        3827471373600985324655467241208964585657780000000000000]]

private theorem pf5CenterLower_blockTriangular :
    pf5CenterLower.BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  fin_cases i <;> fin_cases j <;> norm_num [pf5CenterLower] at *

private theorem pf5CenterUpper_blockTriangular :
    pf5CenterUpper.BlockTriangular (id : Fin 5 → Fin 5) := by
  intro i j hij
  change j < i at hij
  fin_cases i <;> fin_cases j <;> norm_num [pf5CenterUpper] at *

private theorem xiKernelPF5CenterMatrix_eq_lower_mul_upper :
    xiKernelPF5CenterMatrix = pf5CenterLower * pf5CenterUpper := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xiKernelPF5CenterMatrix, pf5DiagonalIndex, pf5PhiCenter,
      pf5CenterLower, pf5CenterUpper, Matrix.mul_apply, Fin.sum_univ_five] <;>
    norm_num

theorem xiKernelPF5CenterMatrix_det_lt :
    Matrix.det xiKernelPF5CenterMatrix < -(9 / 5000000000 : Real) := by
  have hLower : Matrix.det pf5CenterLower = 1 := by
    rw [Matrix.det_of_lowerTriangular pf5CenterLower
      pf5CenterLower_blockTriangular, Fin.prod_univ_five]
    change (1 : Real) * 1 * 1 * 1 * 1 = 1
    norm_num
  have hUpper :
      Matrix.det pf5CenterUpper < -(9 / 5000000000 : Real) := by
    rw [Matrix.det_of_upperTriangular pf5CenterUpper_blockTriangular,
      Fin.prod_univ_five]
    change
      (222513277673 / 500000000000 : Real) *
        (8516010155811805952139 / 111256638836500000000000) *
        (87212133047242452033814116777479 /
          4258005077905902976069500000000000) *
        (191373568680049266232773362060448229282889 /
          34884853218896980813525646710991600000000000) *
        (-(1847235982628972102465848504505468385696544265663373 : Real) /
          3827471373600985324655467241208964585657780000000000000) <
        -(9 / 5000000000 : Real)
    norm_num
  rw [xiKernelPF5CenterMatrix_eq_lower_mul_upper, Matrix.det_mul, hLower, one_mul]
  exact hUpper

/-- The exact infinite kernel determinant stays within `2 * 10^-10` of its rational center. -/
theorem xiKernelPF5_det_center_error :
    |Matrix.det xiKernelPF5PhiMatrix - Matrix.det xiKernelPF5CenterMatrix| <
      (1 / 5000000000 : Real) := by
  have hprod (sigma : Equiv.Perm (Fin 5)) :
      |(∏ i, xiKernelPF5PhiMatrix (sigma i) i) -
          ∏ i, xiKernelPF5CenterMatrix (sigma i) i| ≤
        5 * (3 / 1000000000000 : Real) * (1 / 2 : Real) ^ 4 := by
    apply abs_prod_fin_five_sub_prod_fin_five_le
    · norm_num
    · exact fun i ↦ xiKernelPF5PhiMatrix_abs_le (sigma i) i
    · exact fun i ↦ (xiKernelPF5CenterMatrix_abs_le (sigma i) i).trans (by norm_num)
    · intro i
      exact (pf5_phi_center_error (pf5DiagonalIndex (sigma i) i)).le
  have hdet :
      Matrix.det xiKernelPF5PhiMatrix - Matrix.det xiKernelPF5CenterMatrix =
        ∑ sigma : Equiv.Perm (Fin 5),
          ((Equiv.Perm.sign sigma : Int) : Real) *
            ((∏ i, xiKernelPF5PhiMatrix (sigma i) i) -
              ∏ i, xiKernelPF5CenterMatrix (sigma i) i) := by
    rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro sigma _hsigma
    ring
  rw [hdet]
  calc
    |∑ sigma : Equiv.Perm (Fin 5),
        ((Equiv.Perm.sign sigma : Int) : Real) *
          ((∏ i, xiKernelPF5PhiMatrix (sigma i) i) -
            ∏ i, xiKernelPF5CenterMatrix (sigma i) i)| ≤
        ∑ sigma : Equiv.Perm (Fin 5),
          |((Equiv.Perm.sign sigma : Int) : Real) *
            ((∏ i, xiKernelPF5PhiMatrix (sigma i) i) -
              ∏ i, xiKernelPF5CenterMatrix (sigma i) i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _sigma : Equiv.Perm (Fin 5),
        5 * (3 / 1000000000000 : Real) * (1 / 2 : Real) ^ 4 := by
      apply Finset.sum_le_sum
      intro sigma _hsigma
      calc
        |((Equiv.Perm.sign sigma : Int) : Real) *
            ((∏ i, xiKernelPF5PhiMatrix (sigma i) i) -
              ∏ i, xiKernelPF5CenterMatrix (sigma i) i)| =
            |(∏ i, xiKernelPF5PhiMatrix (sigma i) i) -
              ∏ i, xiKernelPF5CenterMatrix (sigma i) i| := by
          rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs]
          norm_num
        _ ≤ 5 * (3 / 1000000000000 : Real) * (1 / 2 : Real) ^ 4 :=
          hprod sigma
    _ < (1 / 5000000000 : Real) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, Nat.factorial]
      norm_num

theorem xiKernelPF5PhiMatrix_det_neg :
    Matrix.det xiKernelPF5PhiMatrix < 0 := by
  have hcenter := xiKernelPF5CenterMatrix_det_lt
  have herr := xiKernelPF5_det_center_error
  rw [abs_lt] at herr
  linarith

/-- Source-faithful Pólya-frequency order-five condition for a translation kernel. -/
def IsPolyaFrequencyFive (K : Real → Real) : Prop :=
  ∀ (r : Nat), r ≤ 5 → ∀ x y : Fin r → Real,
    StrictMono x → StrictMono y →
      0 ≤ Matrix.det (fun i j ↦ K (x i - y j))

/-- The Toeplitz minor in the coordinates used by the source certificate. -/
def xiKernelPF5ToeplitzMatrix : Matrix (Fin 5) (Fin 5) Real :=
  fun i j ↦ deBruijnNewmanEvenKernel
    (1 / 100 + ((i.1 : Real) - (j.1 : Real)) / 20)

private theorem xiKernelPF5ToeplitzMatrix_eq_phiMatrix :
    xiKernelPF5ToeplitzMatrix = xiKernelPF5PhiMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [xiKernelPF5ToeplitzMatrix, xiKernelPF5PhiMatrix,
      deBruijnNewmanEvenKernel, pf5KernelArgument, pf5DiagonalIndex,
      abs_of_nonneg, abs_of_nonpos]

theorem xiKernelPF5ToeplitzMatrix_det_neg :
    Matrix.det xiKernelPF5ToeplitzMatrix < 0 := by
  rw [xiKernelPF5ToeplitzMatrix_eq_phiMatrix]
  exact xiKernelPF5PhiMatrix_det_neg

private def pf5WitnessX (i : Fin 5) : Real :=
  1 / 200 + (i.1 : Real) / 20

private def pf5WitnessY (j : Fin 5) : Real :=
  -(1 / 200 : Real) + (j.1 : Real) / 20

private theorem pf5WitnessX_strictMono : StrictMono pf5WitnessX := by
  intro i j hij
  have hijReal : (i.1 : Real) < (j.1 : Real) := by exact_mod_cast hij
  dsimp only [pf5WitnessX]
  linarith

private theorem pf5WitnessY_strictMono : StrictMono pf5WitnessY := by
  intro i j hij
  have hijReal : (i.1 : Real) < (j.1 : Real) := by exact_mod_cast hij
  dsimp only [pf5WitnessY]
  linarith

private theorem pf5WitnessMatrix_eq_toeplitz :
    (fun i j ↦ deBruijnNewmanEvenKernel (pf5WitnessX i - pf5WitnessY j)) =
      xiKernelPF5ToeplitzMatrix := by
  ext i j
  simp only [pf5WitnessX, pf5WitnessY, xiKernelPF5ToeplitzMatrix]
  congr 1
  ring

/-- The exact de Bruijn--Newman Xi kernel fails the source's order-five PF condition. -/
theorem not_isPolyaFrequencyFive_deBruijnNewmanEvenKernel :
    ¬ IsPolyaFrequencyFive deBruijnNewmanEvenKernel := by
  intro hpf5
  have hnonneg := hpf5 5 (by norm_num) pf5WitnessX pf5WitnessY
    pf5WitnessX_strictMono pf5WitnessY_strictMono
  rw [pf5WitnessMatrix_eq_toeplitz] at hnonneg
  linarith [xiKernelPF5ToeplitzMatrix_det_neg]

end


end LeanLab.Riemann
