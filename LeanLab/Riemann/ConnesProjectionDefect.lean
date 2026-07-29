import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NoncommRing

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Connes nested-projection trace positivity

This module isolates the finite algebraic core of Connes' 1998 trace-formula argument,
Theorem 5 equations (23)--(25). Nested orthogonal projections have an orthogonal-projection
defect. Its trace against a convolution-square image is exactly a Frobenius norm square.

The finite theorem does not construct the source adele-class projections, prove trace-class
properties, or identify a distributional limit with the Weil distribution.
-/

open Matrix
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

variable {n : Type*} [Fintype n]

/-- The finite matrix form of the source containment `Q'_Lambda <= S_Lambda`. -/
structure ConnesNestedOrthogonalProjections (P Q : Matrix n n ℂ) : Prop where
  left_selfAdjoint : Pᴴ = P
  left_idempotent : P * P = P
  right_selfAdjoint : Qᴴ = Q
  right_idempotent : Q * Q = Q
  left_mul_right : P * Q = Q
  right_mul_left : Q * P = Q

/-- The finite cutoff defect corresponding to `S_Lambda - Q'_Lambda`. -/
def connesProjectionDefect (P Q : Matrix n n ℂ) : Matrix n n ℂ :=
  P - Q

/-- The trace distribution evaluated on a finite convolution-square image. -/
def connesFiniteDefectTrace (P Q A : Matrix n n ℂ) : ℂ :=
  (connesProjectionDefect P Q * (A * Aᴴ)).trace

theorem connesProjectionDefect_selfAdjoint {P Q : Matrix n n ℂ}
    (h : ConnesNestedOrthogonalProjections P Q) :
    (connesProjectionDefect P Q)ᴴ = connesProjectionDefect P Q := by
  rw [connesProjectionDefect, conjTranspose_sub, h.left_selfAdjoint, h.right_selfAdjoint]

theorem connesProjectionDefect_idempotent {P Q : Matrix n n ℂ}
    (h : ConnesNestedOrthogonalProjections P Q) :
    connesProjectionDefect P Q * connesProjectionDefect P Q =
      connesProjectionDefect P Q := by
  rw [connesProjectionDefect]
  calc
    (P - Q) * (P - Q) = P * P - P * Q - Q * P + Q * Q := by
      noncomm_ring
    _ = P - Q := by
      rw [h.left_idempotent, h.right_idempotent, h.left_mul_right, h.right_mul_left]
      noncomm_ring

theorem complexMatrix_trace_mul_conjTranspose_eq_sum_normSq (B : Matrix n n ℂ) :
    (B * Bᴴ).trace =
      ((∑ i : n, ∑ j : n, Complex.normSq (B i j) : ℝ) : ℂ) := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_conj]

theorem connesFiniteDefectTrace_eq_sum_normSq {P Q : Matrix n n ℂ}
    (h : ConnesNestedOrthogonalProjections P Q) (A : Matrix n n ℂ) :
    connesFiniteDefectTrace P Q A =
      ((∑ i : n, ∑ j : n,
        Complex.normSq ((connesProjectionDefect P Q * A) i j) : ℝ) : ℂ) := by
  let H := connesProjectionDefect P Q
  have hHstar : Hᴴ = H := connesProjectionDefect_selfAdjoint h
  have hHsq : H * H = H := connesProjectionDefect_idempotent h
  unfold connesFiniteDefectTrace
  change (H * (A * Aᴴ)).trace = _
  calc
    (H * (A * Aᴴ)).trace = ((H * (A * Aᴴ)) * H).trace := by
      rw [Matrix.trace_mul_comm (H * (A * Aᴴ)) H]
      simp only [← Matrix.mul_assoc, hHsq]
    _ = ((H * A) * (H * A)ᴴ).trace := by
      simp only [conjTranspose_mul, hHstar, Matrix.mul_assoc]
    _ = ((∑ i : n, ∑ j : n, Complex.normSq ((H * A) i j) : ℝ) : ℂ) :=
      complexMatrix_trace_mul_conjTranspose_eq_sum_normSq (H * A)

theorem connesFiniteDefectTrace_im_eq_zero {P Q : Matrix n n ℂ}
    (h : ConnesNestedOrthogonalProjections P Q) (A : Matrix n n ℂ) :
    (connesFiniteDefectTrace P Q A).im = 0 := by
  rw [connesFiniteDefectTrace_eq_sum_normSq h]
  simp

theorem connesFiniteDefectTrace_re_nonneg {P Q : Matrix n n ℂ}
    (h : ConnesNestedOrthogonalProjections P Q) (A : Matrix n n ℂ) :
    0 ≤ (connesFiniteDefectTrace P Q A).re := by
  rw [connesFiniteDefectTrace_eq_sum_normSq h]
  simp only [Complex.ofReal_re]
  exact Fintype.sum_nonneg fun i =>
    Fintype.sum_nonneg fun j =>
      Complex.normSq_nonneg ((connesProjectionDefect P Q * A) i j)

theorem connesFiniteDefectTrace_eq_zero_iff {P Q : Matrix n n ℂ}
    (h : ConnesNestedOrthogonalProjections P Q) (A : Matrix n n ℂ) :
    connesFiniteDefectTrace P Q A = 0 ↔ connesProjectionDefect P Q * A = 0 := by
  rw [connesFiniteDefectTrace_eq_sum_normSq h]
  constructor
  · intro hsum
    have hsumReal :
        (∑ i : n, ∑ j : n,
          Complex.normSq ((connesProjectionDefect P Q * A) i j)) = 0 := by
      simpa using congrArg Complex.re hsum
    ext i j
    have hi :
        (∑ j : n, Complex.normSq ((connesProjectionDefect P Q * A) i j)) = 0 := by
      have hiFun :=
        (Fintype.sum_eq_zero_iff_of_nonneg fun i =>
          Fintype.sum_nonneg fun j =>
            Complex.normSq_nonneg ((connesProjectionDefect P Q * A) i j)).mp hsumReal
      exact congrFun hiFun i
    have hij : Complex.normSq ((connesProjectionDefect P Q * A) i j) = 0 := by
      have hijFun :=
        (Fintype.sum_eq_zero_iff_of_nonneg fun j =>
          Complex.normSq_nonneg ((connesProjectionDefect P Q * A) i j)).mp hi
      exact congrFun hijFun j
    exact Complex.normSq_eq_zero.mp hij
  · intro hzero
    rw [hzero]
    simp

/-- The left projection in the one-dimensional no-nesting control. -/
def connesNonNestedLeft : Matrix (Fin 1) (Fin 1) ℂ :=
  0

/-- The right projection in the one-dimensional no-nesting control. -/
def connesNonNestedRight : Matrix (Fin 1) (Fin 1) ℂ :=
  1

/-- The test matrix in the one-dimensional no-nesting control. -/
def connesNonNestedTest : Matrix (Fin 1) (Fin 1) ℂ :=
  1

theorem connesNonNested_individual_projections :
    connesNonNestedLeftᴴ = connesNonNestedLeft ∧
      connesNonNestedLeft * connesNonNestedLeft = connesNonNestedLeft ∧
      connesNonNestedRightᴴ = connesNonNestedRight ∧
      connesNonNestedRight * connesNonNestedRight = connesNonNestedRight := by
  simp [connesNonNestedLeft, connesNonNestedRight]

theorem connesNonNested_not_nested :
    ¬ConnesNestedOrthogonalProjections connesNonNestedLeft connesNonNestedRight := by
  intro h
  have hentry := congrFun (congrFun h.left_mul_right 0) 0
  simp [connesNonNestedLeft, connesNonNestedRight, Matrix.mul_apply] at hentry

theorem connesNonNested_trace_re_eq_neg_one :
    (connesFiniteDefectTrace connesNonNestedLeft connesNonNestedRight
      connesNonNestedTest).re = -1 := by
  simp [connesFiniteDefectTrace, connesProjectionDefect, connesNonNestedLeft,
    connesNonNestedRight, connesNonNestedTest, Matrix.trace]

/-- Aggregate certificate for the source positive-type mechanism and its nesting boundary. -/
theorem connesProjectionDefect_endpoint :
    (∀ {n : Type} [Fintype n] {P Q : Matrix n n ℂ},
      ConnesNestedOrthogonalProjections P Q →
      ∀ A : Matrix n n ℂ,
        (connesProjectionDefect P Q)ᴴ = connesProjectionDefect P Q ∧
        connesProjectionDefect P Q * connesProjectionDefect P Q =
          connesProjectionDefect P Q ∧
        connesFiniteDefectTrace P Q A =
          ((∑ i : n, ∑ j : n,
            Complex.normSq ((connesProjectionDefect P Q * A) i j) : ℝ) : ℂ) ∧
        (connesFiniteDefectTrace P Q A).im = 0 ∧
        0 ≤ (connesFiniteDefectTrace P Q A).re ∧
        (connesFiniteDefectTrace P Q A = 0 ↔
          connesProjectionDefect P Q * A = 0)) ∧
    (connesNonNestedLeftᴴ = connesNonNestedLeft ∧
      connesNonNestedLeft * connesNonNestedLeft = connesNonNestedLeft ∧
      connesNonNestedRightᴴ = connesNonNestedRight ∧
      connesNonNestedRight * connesNonNestedRight = connesNonNestedRight) ∧
    ¬ConnesNestedOrthogonalProjections connesNonNestedLeft connesNonNestedRight ∧
    (connesFiniteDefectTrace connesNonNestedLeft connesNonNestedRight
      connesNonNestedTest).re = -1 := by
  refine ⟨?_, connesNonNested_individual_projections,
    connesNonNested_not_nested, connesNonNested_trace_re_eq_neg_one⟩
  intro n _ P Q h A
  exact ⟨connesProjectionDefect_selfAdjoint h, connesProjectionDefect_idempotent h,
    connesFiniteDefectTrace_eq_sum_normSq h A, connesFiniteDefectTrace_im_eq_zero h A,
    connesFiniteDefectTrace_re_nonneg h A, connesFiniteDefectTrace_eq_zero_iff h A⟩

end

end LeanLab.Riemann
