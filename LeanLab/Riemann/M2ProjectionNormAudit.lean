import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

noncomputable section

/-!
# A projection-norm counterexample for the M2 literature audit

This file checks that a Euclidean orthogonal-projection matrix need not be nonexpansive for the
coordinate maximum norm.
-/

namespace LeanLab.Riemann

/-- A rank-one Euclidean orthogonal-projection matrix used in the audit. -/
def m2AuditProjectionMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(4 : ℝ) / 5, 2 / 5; 2 / 5, 1 / 5]

/-- The coordinate maximum norm on real two-vectors. -/
def finTwoMaxNorm (x : Fin 2 → ℝ) : ℝ :=
  max |x 0| |x 1|

/-- The maximum-norm test vector. -/
def m2AuditTestVector : Fin 2 → ℝ :=
  ![1, 1]

theorem m2AuditProjectionMatrix_transpose :
    m2AuditProjectionMatrix.transpose = m2AuditProjectionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [m2AuditProjectionMatrix, Matrix.transpose]

theorem m2AuditProjectionMatrix_idempotent :
    m2AuditProjectionMatrix * m2AuditProjectionMatrix = m2AuditProjectionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [m2AuditProjectionMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem finTwoMaxNorm_m2AuditTestVector :
    finTwoMaxNorm m2AuditTestVector = 1 := by
  norm_num [finTwoMaxNorm, m2AuditTestVector]

theorem finTwoMaxNorm_m2AuditProjectionMatrix_mulVec_testVector :
    finTwoMaxNorm (Matrix.mulVec m2AuditProjectionMatrix m2AuditTestVector) = 6 / 5 := by
  norm_num [finTwoMaxNorm, m2AuditProjectionMatrix, m2AuditTestVector,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem not_m2AuditProjectionMatrix_maxNorm_nonexpansive :
    ¬ ∀ x : Fin 2 → ℝ,
      finTwoMaxNorm (Matrix.mulVec m2AuditProjectionMatrix x) ≤ finTwoMaxNorm x := by
  intro h
  have htest := h m2AuditTestVector
  rw [finTwoMaxNorm_m2AuditProjectionMatrix_mulVec_testVector,
    finTwoMaxNorm_m2AuditTestVector] at htest
  norm_num at htest

/-- A symmetric idempotent real matrix can increase the coordinate maximum norm. -/
theorem exists_symmetric_idempotent_not_maxNorm_nonexpansive :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
      P.transpose = P ∧ P * P = P ∧
        ¬ ∀ x : Fin 2 → ℝ, finTwoMaxNorm (Matrix.mulVec P x) ≤ finTwoMaxNorm x :=
  ⟨m2AuditProjectionMatrix, m2AuditProjectionMatrix_transpose,
    m2AuditProjectionMatrix_idempotent,
    not_m2AuditProjectionMatrix_maxNorm_nonexpansive⟩

/-- The `n = 3` remainder matrix from the audited source, with rows indexed by `1 <= i < 6`. -/
def m2AuditWongAThree : Matrix (Fin 5) (Fin 2) ℝ :=
  !![1, 1; 0, 2; 1, 0; 0, 1; 1, 2]

/-- The exact Gram matrix of `m2AuditWongAThree`. -/
def m2AuditWongGramThree : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3, 3; 3, 10]

/-- The exact inverse of the `n = 3` Gram matrix. -/
def m2AuditWongGramInvThree : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(10 : ℝ) / 21, -3 / 21; -3 / 21, 3 / 21]

/-- The source's Euclidean projection `A_3 (A_3^T A_3)⁻¹ A_3^T`. -/
def m2AuditWongPThree : Matrix (Fin 5) (Fin 5) ℝ :=
  m2AuditWongAThree * m2AuditWongGramInvThree * m2AuditWongAThree.transpose

/-- Coordinate maximum norm on real five-vectors. -/
def finFiveMaxNorm (x : Fin 5 → ℝ) : ℝ :=
  max |x 0| (max |x 1| (max |x 2| (max |x 3| |x 4|)))

/-- A sign vector exposing the second absolute row sum of `m2AuditWongPThree`. -/
def m2AuditWongTestVector : Fin 5 → ℝ :=
  ![1, 1, -1, 1, 1]

theorem m2AuditWong_gram_three :
    m2AuditWongAThree.transpose * m2AuditWongAThree = m2AuditWongGramThree := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [m2AuditWongAThree, m2AuditWongGramThree, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem m2AuditWong_gramInv_three_mul :
    m2AuditWongGramInvThree * m2AuditWongGramThree = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [m2AuditWongGramInvThree, m2AuditWongGramThree, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem m2AuditWong_gram_three_mul_inv :
    m2AuditWongGramThree * m2AuditWongGramInvThree = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [m2AuditWongGramInvThree, m2AuditWongGramThree, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem m2AuditWongPThree_transpose :
    m2AuditWongPThree.transpose = m2AuditWongPThree := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [m2AuditWongPThree, m2AuditWongAThree, m2AuditWongGramInvThree,
      Matrix.mul_apply, Matrix.transpose, Fin.sum_univ_two]

theorem m2AuditWongPThree_idempotent :
    m2AuditWongPThree * m2AuditWongPThree = m2AuditWongPThree := by
  unfold m2AuditWongPThree
  calc
    (m2AuditWongAThree * m2AuditWongGramInvThree * m2AuditWongAThree.transpose) *
        (m2AuditWongAThree * m2AuditWongGramInvThree * m2AuditWongAThree.transpose) =
        m2AuditWongAThree * m2AuditWongGramInvThree *
          (m2AuditWongAThree.transpose * m2AuditWongAThree) *
            m2AuditWongGramInvThree * m2AuditWongAThree.transpose := by
      simp only [Matrix.mul_assoc]
    _ = m2AuditWongAThree * m2AuditWongGramInvThree * m2AuditWongGramThree *
          m2AuditWongGramInvThree * m2AuditWongAThree.transpose := by
      rw [m2AuditWong_gram_three]
    _ = m2AuditWongAThree *
          (m2AuditWongGramInvThree * m2AuditWongGramThree) *
            m2AuditWongGramInvThree * m2AuditWongAThree.transpose := by
      simp only [Matrix.mul_assoc]
    _ = m2AuditWongAThree * m2AuditWongGramInvThree *
          m2AuditWongAThree.transpose := by
      rw [m2AuditWong_gramInv_three_mul]
      simp

theorem finFiveMaxNorm_m2AuditWongTestVector :
    finFiveMaxNorm m2AuditWongTestVector = 1 := by
  simp [finFiveMaxNorm, m2AuditWongTestVector]

theorem m2AuditWongPThree_mulVec_testVector :
    Matrix.mulVec m2AuditWongPThree m2AuditWongTestVector =
      ![(1 : ℝ) / 3, 10 / 7, -8 / 21, 5 / 7, 22 / 21] := by
  ext i
  fin_cases i <;>
    simp [m2AuditWongPThree, m2AuditWongAThree, m2AuditWongGramInvThree,
      m2AuditWongTestVector, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose,
      dotProduct, Fin.sum_univ_succ] <;>
    norm_num

theorem finFiveMaxNorm_m2AuditWongPThree_mulVec_testVector :
    finFiveMaxNorm (Matrix.mulVec m2AuditWongPThree m2AuditWongTestVector) = 10 / 7 := by
  rw [m2AuditWongPThree_mulVec_testVector]
  change max |(1 : ℝ) / 3| (max |10 / 7| (max |-8 / 21| (max |5 / 7| |22 / 21|))) =
    10 / 7
  norm_num

/-- The audited source's own `n = 3` projection is not a maximum-norm contraction. -/
theorem not_m2AuditWongPThree_maxNorm_nonexpansive :
    ¬ ∀ x : Fin 5 → ℝ,
      finFiveMaxNorm (Matrix.mulVec m2AuditWongPThree x) ≤ finFiveMaxNorm x := by
  intro h
  have htest := h m2AuditWongTestVector
  rw [finFiveMaxNorm_m2AuditWongPThree_mulVec_testVector,
    finFiveMaxNorm_m2AuditWongTestVector] at htest
  norm_num at htest

end LeanLab.Riemann
