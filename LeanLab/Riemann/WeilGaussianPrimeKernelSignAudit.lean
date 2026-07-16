import LeanLab.Riemann.WeilSymmetricGaussianFamily
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Sign audit for one Gaussian prime-power kernel

This module gives an exact two-dimensional counterexample to assigning either semidefinite sign
to every individual symmetric Gaussian von-Mangoldt translation kernel. It uses the actual prime
`2` term from the compiled Weil arithmetic formula.
-/

open Complex Matrix
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- The real translation-kernel matrix contributed by one symmetric Gaussian prime-power term. -/
def symmetricGaussianPrimeKernelMatrix
    (a : ℝ) (b : Fin 2 → ℝ) (n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => (symmetricGaussianVonMangoldtWeight a (b i - b j) n).re

/-- A real formula for the symmetric Gaussian prime-power kernel. -/
def symmetricGaussianPrimeKernelReal (a d : ℝ) (n : ℕ) : ℝ :=
  ((Real.pi / a) ^ (1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt n *
      Real.exp (-(Real.log n) / 2 - (Real.log n - d) ^ 2 / (4 * a)) +
    (Real.pi / a) ^ (1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt n *
      Real.exp (-(Real.log n) / 2 - (Real.log n + d) ^ 2 / (4 * a))) / 2

theorem symmetricGaussianVonMangoldtWeight_eq_ofReal_kernel
    {a : ℝ} (ha : 0 < a) (d : ℝ) (n : ℕ) :
    symmetricGaussianVonMangoldtWeight a d n =
      (symmetricGaussianPrimeKernelReal a d n : ℝ) := by
  have hpa : 0 ≤ Real.pi / a := (div_pos Real.pi_pos ha).le
  have hpow : ((Real.pi / a : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (((Real.pi / a) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow hpa (1 / 2 : ℝ)).symm
  rw [symmetricGaussianVonMangoldtWeight, shiftedGaussianVonMangoldtWeight,
    shiftedGaussianVonMangoldtWeight, hpow]
  have hp : -(Real.log n : ℂ) / 2 - ((Real.log n : ℂ) - d) ^ 2 / (4 * a) =
      (-(Real.log n) / 2 - (Real.log n - d) ^ 2 / (4 * a) : ℝ) := by
    push_cast
    ring
  have hm : -(Real.log n : ℂ) / 2 - ((Real.log n : ℂ) - (-d : ℝ)) ^ 2 / (4 * a) =
      (-(Real.log n) / 2 - (Real.log n + d) ^ 2 / (4 * a) : ℝ) := by
    push_cast
    ring
  rw [hp, hm, ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  norm_cast

def gaussianPrimeAuditLogTwo : ℝ :=
  Real.log 2

def gaussianPrimeAuditWidth : ℝ :=
  gaussianPrimeAuditLogTwo ^ 2 / 16

def gaussianPrimeAuditCommonFactor : ℝ :=
  (Real.pi / gaussianPrimeAuditWidth) ^ (1 / 2 : ℝ) * gaussianPrimeAuditLogTwo *
    Real.exp (-gaussianPrimeAuditLogTwo / 2)

def gaussianPrimeAuditShifts : Fin 2 → ℝ :=
  ![0, gaussianPrimeAuditLogTwo]

def gaussianPrimeAuditNegativeVector : Fin 2 → ℝ :=
  ![1, -1]

def gaussianPrimeAuditPositiveVector : Fin 2 → ℝ :=
  ![1, 0]

theorem gaussianPrimeAuditLogTwo_pos :
    0 < gaussianPrimeAuditLogTwo := by
  simpa [gaussianPrimeAuditLogTwo] using Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem gaussianPrimeAuditWidth_pos :
    0 < gaussianPrimeAuditWidth := by
  unfold gaussianPrimeAuditWidth
  exact div_pos (sq_pos_of_pos gaussianPrimeAuditLogTwo_pos) (by norm_num)

theorem gaussianPrimeAuditCommonFactor_pos :
    0 < gaussianPrimeAuditCommonFactor := by
  unfold gaussianPrimeAuditCommonFactor
  have hdiv : 0 < Real.pi / gaussianPrimeAuditWidth :=
    div_pos Real.pi_pos gaussianPrimeAuditWidth_pos
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hdiv _) gaussianPrimeAuditLogTwo_pos)
    (Real.exp_pos _)

theorem symmetricGaussianPrimeKernelReal_audit_zero :
    symmetricGaussianPrimeKernelReal gaussianPrimeAuditWidth 0 2 =
      gaussianPrimeAuditCommonFactor * Real.exp (-4) := by
  have hL0 : gaussianPrimeAuditLogTwo ≠ 0 := gaussianPrimeAuditLogTwo_pos.ne'
  rw [symmetricGaussianPrimeKernelReal, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  change
    (((Real.pi / gaussianPrimeAuditWidth) ^ (1 / 2 : ℝ) * gaussianPrimeAuditLogTwo *
          Real.exp (-gaussianPrimeAuditLogTwo / 2 -
            (gaussianPrimeAuditLogTwo - 0) ^ 2 / (4 * gaussianPrimeAuditWidth)) +
        (Real.pi / gaussianPrimeAuditWidth) ^ (1 / 2 : ℝ) * gaussianPrimeAuditLogTwo *
          Real.exp (-gaussianPrimeAuditLogTwo / 2 -
            (gaussianPrimeAuditLogTwo + 0) ^ 2 / (4 * gaussianPrimeAuditWidth))) / 2) = _
  have hratio : gaussianPrimeAuditLogTwo ^ 2 / (4 * gaussianPrimeAuditWidth) = 4 := by
    rw [gaussianPrimeAuditWidth]
    field_simp
    norm_num
  rw [sub_zero, add_zero, hratio]
  rw [show -gaussianPrimeAuditLogTwo / 2 - 4 =
      -gaussianPrimeAuditLogTwo / 2 + (-4) by ring, Real.exp_add]
  unfold gaussianPrimeAuditCommonFactor
  ring

theorem symmetricGaussianPrimeKernelReal_audit_logTwo :
    symmetricGaussianPrimeKernelReal gaussianPrimeAuditWidth gaussianPrimeAuditLogTwo 2 =
      gaussianPrimeAuditCommonFactor * (1 + Real.exp (-16)) / 2 := by
  have hL0 : gaussianPrimeAuditLogTwo ≠ 0 := gaussianPrimeAuditLogTwo_pos.ne'
  rw [symmetricGaussianPrimeKernelReal, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  change
    (((Real.pi / gaussianPrimeAuditWidth) ^ (1 / 2 : ℝ) * gaussianPrimeAuditLogTwo *
          Real.exp (-gaussianPrimeAuditLogTwo / 2 -
            (gaussianPrimeAuditLogTwo - gaussianPrimeAuditLogTwo) ^ 2 /
              (4 * gaussianPrimeAuditWidth)) +
        (Real.pi / gaussianPrimeAuditWidth) ^ (1 / 2 : ℝ) * gaussianPrimeAuditLogTwo *
          Real.exp (-gaussianPrimeAuditLogTwo / 2 -
            (gaussianPrimeAuditLogTwo + gaussianPrimeAuditLogTwo) ^ 2 /
              (4 * gaussianPrimeAuditWidth))) / 2) = _
  have hratio : (gaussianPrimeAuditLogTwo + gaussianPrimeAuditLogTwo) ^ 2 /
      (4 * gaussianPrimeAuditWidth) = 16 := by
    rw [gaussianPrimeAuditWidth]
    field_simp
    ring
  rw [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero, hratio]
  rw [show -gaussianPrimeAuditLogTwo / 2 - 16 =
      -gaussianPrimeAuditLogTwo / 2 + (-16) by ring, Real.exp_add]
  unfold gaussianPrimeAuditCommonFactor
  ring

theorem symmetricGaussianPrimeKernelReal_neg (a d : ℝ) (n : ℕ) :
    symmetricGaussianPrimeKernelReal a (-d) n =
      symmetricGaussianPrimeKernelReal a d n := by
  unfold symmetricGaussianPrimeKernelReal
  rw [show Real.log n - -d = Real.log n + d by ring,
    show Real.log n + -d = Real.log n - d by ring]
  ring

theorem symmetricGaussianVonMangoldtWeight_audit_zero_re :
    (symmetricGaussianVonMangoldtWeight gaussianPrimeAuditWidth 0 2).re =
      gaussianPrimeAuditCommonFactor * Real.exp (-4) := by
  rw [symmetricGaussianVonMangoldtWeight_eq_ofReal_kernel gaussianPrimeAuditWidth_pos]
  simpa using symmetricGaussianPrimeKernelReal_audit_zero

theorem symmetricGaussianVonMangoldtWeight_audit_logTwo_re :
    (symmetricGaussianVonMangoldtWeight
      gaussianPrimeAuditWidth gaussianPrimeAuditLogTwo 2).re =
      gaussianPrimeAuditCommonFactor * (1 + Real.exp (-16)) / 2 := by
  rw [symmetricGaussianVonMangoldtWeight_eq_ofReal_kernel gaussianPrimeAuditWidth_pos]
  simpa using symmetricGaussianPrimeKernelReal_audit_logTwo

theorem symmetricGaussianVonMangoldtWeight_audit_negLogTwo_re :
    (symmetricGaussianVonMangoldtWeight
      gaussianPrimeAuditWidth (-gaussianPrimeAuditLogTwo) 2).re =
      gaussianPrimeAuditCommonFactor * (1 + Real.exp (-16)) / 2 := by
  rw [symmetricGaussianVonMangoldtWeight_eq_ofReal_kernel gaussianPrimeAuditWidth_pos,
    symmetricGaussianPrimeKernelReal_neg]
  simpa using symmetricGaussianPrimeKernelReal_audit_logTwo

theorem exp_neg_four_lt_half :
    Real.exp (-4) < (1 / 2 : ℝ) := by
  have hlog : Real.log 2 < (4 : ℝ) := Real.log_two_lt_d9.trans (by norm_num)
  calc
    Real.exp (-4) < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr (neg_lt_neg hlog)
    _ = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

theorem symmetricGaussianVonMangoldtWeight_audit_offDiag_gt_diag :
    (symmetricGaussianVonMangoldtWeight gaussianPrimeAuditWidth 0 2).re <
      (symmetricGaussianVonMangoldtWeight
        gaussianPrimeAuditWidth gaussianPrimeAuditLogTwo 2).re := by
  rw [symmetricGaussianVonMangoldtWeight_audit_zero_re,
    symmetricGaussianVonMangoldtWeight_audit_logTwo_re]
  have hright : (1 / 2 : ℝ) < (1 + Real.exp (-16)) / 2 := by
    nlinarith [Real.exp_pos (-16)]
  calc
    gaussianPrimeAuditCommonFactor * Real.exp (-4) <
        gaussianPrimeAuditCommonFactor * (1 / 2) :=
      mul_lt_mul_of_pos_left exp_neg_four_lt_half gaussianPrimeAuditCommonFactor_pos
    _ < gaussianPrimeAuditCommonFactor * ((1 + Real.exp (-16)) / 2) :=
      mul_lt_mul_of_pos_left hright gaussianPrimeAuditCommonFactor_pos
    _ = gaussianPrimeAuditCommonFactor * (1 + Real.exp (-16)) / 2 := by ring

theorem symmetricGaussianPrimeKernelMatrix_audit_diag_pos :
    0 < symmetricGaussianPrimeKernelMatrix
      gaussianPrimeAuditWidth gaussianPrimeAuditShifts 2 0 0 := by
  rw [symmetricGaussianPrimeKernelMatrix]
  simp only [gaussianPrimeAuditShifts, Matrix.cons_val_zero, sub_self]
  rw [symmetricGaussianVonMangoldtWeight_audit_zero_re]
  exact mul_pos gaussianPrimeAuditCommonFactor_pos (Real.exp_pos _)

theorem symmetricGaussianPrimeKernelMatrix_audit_negative_quadratic :
    gaussianPrimeAuditNegativeVector ⬝ᵥ
        (symmetricGaussianPrimeKernelMatrix
          gaussianPrimeAuditWidth gaussianPrimeAuditShifts 2 *ᵥ
            gaussianPrimeAuditNegativeVector) < 0 := by
  have hcompare := symmetricGaussianVonMangoldtWeight_audit_offDiag_gt_diag
  rw [show gaussianPrimeAuditNegativeVector ⬝ᵥ
        (symmetricGaussianPrimeKernelMatrix
          gaussianPrimeAuditWidth gaussianPrimeAuditShifts 2 *ᵥ
            gaussianPrimeAuditNegativeVector) =
      2 * ((symmetricGaussianVonMangoldtWeight gaussianPrimeAuditWidth 0 2).re -
        (symmetricGaussianVonMangoldtWeight
          gaussianPrimeAuditWidth gaussianPrimeAuditLogTwo 2).re) by
    simp [dotProduct, mulVec, symmetricGaussianPrimeKernelMatrix,
      gaussianPrimeAuditNegativeVector, gaussianPrimeAuditShifts,
      symmetricGaussianVonMangoldtWeight_audit_negLogTwo_re,
      symmetricGaussianVonMangoldtWeight_audit_logTwo_re,
      symmetricGaussianVonMangoldtWeight_audit_zero_re]
    ring]
  linarith

theorem not_posSemidef_symmetricGaussianPrimeKernelMatrix_audit :
    ¬(symmetricGaussianPrimeKernelMatrix
      gaussianPrimeAuditWidth gaussianPrimeAuditShifts 2).PosSemidef := by
  intro hpos
  have hnonneg := hpos.dotProduct_mulVec_nonneg gaussianPrimeAuditNegativeVector
  have hneg := symmetricGaussianPrimeKernelMatrix_audit_negative_quadratic
  simpa using (not_lt_of_ge hnonneg hneg)

theorem not_neg_posSemidef_symmetricGaussianPrimeKernelMatrix_audit :
    ¬(-symmetricGaussianPrimeKernelMatrix
      gaussianPrimeAuditWidth gaussianPrimeAuditShifts 2).PosSemidef := by
  intro hpos
  have hdiag := hpos.diag_nonneg (i := (0 : Fin 2))
  have hpositive := symmetricGaussianPrimeKernelMatrix_audit_diag_pos
  change 0 ≤ -symmetricGaussianPrimeKernelMatrix
    gaussianPrimeAuditWidth gaussianPrimeAuditShifts 2 0 0 at hdiag
  linarith

theorem exists_pos_symmetricGaussianPrimeKernelMatrix_indefinite :
    ∃ a : ℝ, ∃ b : Fin 2 → ℝ,
      0 < a ∧
      ¬(symmetricGaussianPrimeKernelMatrix a b 2).PosSemidef ∧
      ¬(-symmetricGaussianPrimeKernelMatrix a b 2).PosSemidef := by
  exact ⟨gaussianPrimeAuditWidth, gaussianPrimeAuditShifts,
    gaussianPrimeAuditWidth_pos,
    not_posSemidef_symmetricGaussianPrimeKernelMatrix_audit,
    not_neg_posSemidef_symmetricGaussianPrimeKernelMatrix_audit⟩

end

end LeanLab.Riemann
