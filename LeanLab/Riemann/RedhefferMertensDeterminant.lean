import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The Redheffer matrix and the Mertens determinant

This file formalizes the finite integer elimination at the start of Vaughan's spectral study of
the Redheffer matrix. Positive integers `1, ..., N` are represented by `Fin N` after adding one
to the underlying value, so the Mobius function is never evaluated at zero.
-/

namespace LeanLab.Riemann

open scoped ArithmeticFunction.Moebius BigOperators

/-- The finite Mertens sum `M(N)`, with positive one-based indices. -/
def finiteMertens (N : ℕ) : ℤ :=
  ∑ k : Fin N, ArithmeticFunction.moebius (k.1 + 1)

/-- The order-`n+1` Redheffer matrix over the integers. -/
def redhefferMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j => if i.1 + 1 ∣ j.1 + 1 ∨ j = 0 then 1 else 0

/-- Vaughan's determinant-one first-row Mobius eliminator. -/
def redhefferEliminator (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j =>
    if i = 0 then ArithmeticFunction.moebius (j.1 + 1)
    else if i = j then 1 else 0

/-- The successor-index divisibility block left after expanding along the eliminated first row. -/
def redhefferTail (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (redhefferMatrix n).submatrix Fin.succ Fin.succ

private theorem finiteMobiusDivisorSum_eq_divisors {N m : ℕ}
    (hm : m ≠ 0) (hmN : m ≤ N) :
    (∑ k : Fin N,
      if k.1 + 1 ∣ m then ArithmeticFunction.moebius (k.1 + 1) else 0) =
      ∑ d ∈ m.divisors, ArithmeticFunction.moebius d := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => if k + 1 ∣ m then ArithmeticFunction.moebius (k + 1) else 0),
    ← Finset.sum_filter]
  refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk
    rw [Nat.mem_divisors]
    exact ⟨hk.2, hm⟩
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab
  · intro d hd
    have hd' := Nat.mem_divisors.mp hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd'.1 (Nat.pos_of_ne_zero hm)
    have hdOne : 1 ≤ d := hdpos
    refine ⟨d - 1, ?_, ?_⟩
    · change d - 1 ∈ (Finset.range N).filter (fun k => k + 1 ∣ m)
      rw [Finset.mem_filter]
      constructor
      · have hdle : d ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hd'.1
        exact Finset.mem_range.mpr
          (lt_of_lt_of_le (Nat.sub_lt hdpos Nat.zero_lt_one) (hdle.trans hmN))
      · simpa only [Nat.sub_add_cancel hdOne] using hd'.1
    · exact Nat.sub_add_cancel hdOne
  · intro k hk
    rfl

private theorem finiteMobiusDivisorSum_eq_zero {N m : ℕ}
    (hm : m ≠ 0) (hmOne : m ≠ 1) (hmN : m ≤ N) :
    (∑ k : Fin N,
      if k.1 + 1 ∣ m then ArithmeticFunction.moebius (k.1 + 1) else 0) = 0 := by
  rw [finiteMobiusDivisorSum_eq_divisors hm hmN,
    ← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta]
  simp [hmOne]

theorem redhefferEliminator_blockTriangular (n : ℕ) :
    (redhefferEliminator n).BlockTriangular id := by
  intro i j hji
  have hi : i ≠ 0 := by
    intro hi
    subst i
    simp at hji
  have hij : i ≠ j := ne_of_gt hji
  simp [redhefferEliminator, hi, hij]

theorem det_redhefferEliminator (n : ℕ) :
    (redhefferEliminator n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (redhefferEliminator_blockTriangular n)]
  apply Finset.prod_eq_one
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp [redhefferEliminator]
  · simp [redhefferEliminator, hi0]

theorem redhefferTail_blockTriangular (n : ℕ) :
    (redhefferTail n).BlockTriangular id := by
  intro i j hji
  have hji' : j < i := by
    simpa only [id_eq] using hji
  have hval : j.1 < i.1 := Fin.mk_lt_mk.mp hji'
  have hndvd : ¬(i.1 + 2 ∣ j.1 + 2) := by
    intro hdvd
    have hle := Nat.le_of_dvd (by omega : 0 < j.1 + 2) hdvd
    omega
  simp [redhefferTail, redhefferMatrix, hndvd]

theorem det_redhefferTail (n : ℕ) :
    (redhefferTail n).det = 1 := by
  rw [Matrix.det_of_upperTriangular (redhefferTail_blockTriangular n)]
  apply Finset.prod_eq_one
  intro i hi
  simp [redhefferTail, redhefferMatrix]

theorem redhefferEliminator_mul_redhefferMatrix (n : ℕ) :
    redhefferEliminator n * redhefferMatrix n =
      (redhefferMatrix n).updateRow 0
        (Pi.single 0 (finiteMertens (n + 1))) := by
  ext i j
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp [Matrix.mul_apply, redhefferEliminator, redhefferMatrix, finiteMertens]
    · have hm : j.1 + 1 ≠ 0 := by omega
      have hmOne : j.1 + 1 ≠ 1 := by
        intro h
        apply hj
        apply Fin.ext
        simpa using h
      have hmN : j.1 + 1 ≤ n + 1 := by omega
      rw [Matrix.mul_apply]
      simp only [redhefferEliminator, redhefferMatrix, Matrix.updateRow_self,
        Pi.single_eq_of_ne hj]
      simp only [hj, or_false, mul_ite, mul_one, mul_zero]
      exact finiteMobiusDivisorSum_eq_zero hm hmOne hmN
  · rw [Matrix.mul_apply]
    simp [redhefferEliminator, Matrix.updateRow, hi]

private theorem det_redhefferEliminated (n : ℕ) :
    ((redhefferMatrix n).updateRow 0
      (Pi.single 0 (finiteMertens (n + 1)))).det =
        finiteMertens (n + 1) := by
  have hminor :
      (((redhefferMatrix n).updateRow 0
        (Pi.single 0 (finiteMertens (n + 1)))).submatrix Fin.succ Fin.succ).det = 1 := by
    rw [show
      ((redhefferMatrix n).updateRow 0
        (Pi.single 0 (finiteMertens (n + 1)))).submatrix Fin.succ Fin.succ =
          redhefferTail n by
      ext i j
      simp [Matrix.updateRow, redhefferTail]]
    exact det_redhefferTail n
  have hzeroSuccAbove :
      (0 : Fin (n + 1)).succAbove = (Fin.succ : Fin n → Fin (n + 1)) := by
    funext i
    rfl
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, Matrix.updateRow_self,
      Pi.single_eq_same]
    rw [hzeroSuccAbove, hminor, mul_one]
  · intro j hj hj0
    simp [Matrix.updateRow_self, hj0]
  · simp

/-- Vaughan's exact identity: the Redheffer determinant is the finite Mertens sum. -/
theorem det_redhefferMatrix_eq_finiteMertens (n : ℕ) :
    (redhefferMatrix n).det = finiteMertens (n + 1) := by
  have hdet := congrArg Matrix.det (redhefferEliminator_mul_redhefferMatrix n)
  rw [Matrix.det_mul, det_redhefferEliminator, one_mul,
    det_redhefferEliminated] at hdet
  exact hdet

theorem det_redhefferMatrix_eq_zero_iff (n : ℕ) :
    (redhefferMatrix n).det = 0 ↔ finiteMertens (n + 1) = 0 := by
  rw [det_redhefferMatrix_eq_finiteMertens]

theorem det_redhefferMatrix_ne_zero_iff (n : ℕ) :
    (redhefferMatrix n).det ≠ 0 ↔ finiteMertens (n + 1) ≠ 0 := by
  rw [det_redhefferMatrix_eq_finiteMertens]

@[simp] theorem finiteMertens_one :
    finiteMertens 1 = 1 := by
  simp [finiteMertens]

@[simp] theorem finiteMertens_two :
    finiteMertens 2 = 0 := by
  norm_num [finiteMertens, Fin.sum_univ_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

@[simp] theorem finiteMertens_three :
    finiteMertens 3 = -1 := by
  norm_num [finiteMertens, Fin.sum_univ_three,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]

@[simp] theorem finiteMertens_four :
    finiteMertens 4 = -1 := by
  have hmuFour : ArithmeticFunction.moebius 4 = 0 := by
    rw [show 4 = 2 ^ 2 by norm_num,
      ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
        (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num
  norm_num [finiteMertens, Fin.sum_univ_four,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    hmuFour]

theorem det_redheffer_order_one :
    (redhefferMatrix 0).det = 1 := by
  rw [det_redhefferMatrix_eq_finiteMertens]
  exact finiteMertens_one

theorem det_redheffer_order_two :
    (redhefferMatrix 1).det = 0 := by
  rw [det_redhefferMatrix_eq_finiteMertens]
  exact finiteMertens_two

theorem det_redheffer_order_three :
    (redhefferMatrix 2).det = -1 := by
  rw [det_redhefferMatrix_eq_finiteMertens]
  exact finiteMertens_three

theorem det_redheffer_order_four :
    (redhefferMatrix 3).det = -1 := by
  rw [det_redhefferMatrix_eq_finiteMertens]
  exact finiteMertens_four

/-- The complete finite Redheffer--Mertens elimination certificate. -/
structure RedhefferMertensDeterminantCertificate : Prop where
  elimination :
    ∀ n : ℕ,
      redhefferEliminator n * redhefferMatrix n =
        (redhefferMatrix n).updateRow 0
          (Pi.single 0 (finiteMertens (n + 1)))
  eliminatorDet : ∀ n : ℕ, (redhefferEliminator n).det = 1
  tailDet : ∀ n : ℕ, (redhefferTail n).det = 1
  mertensDet :
    ∀ n : ℕ, (redhefferMatrix n).det = finiteMertens (n + 1)
  lowOrders :
    (redhefferMatrix 0).det = 1 ∧
    (redhefferMatrix 1).det = 0 ∧
    (redhefferMatrix 2).det = -1 ∧
    (redhefferMatrix 3).det = -1

theorem redhefferMertensDeterminant_endpoint :
    RedhefferMertensDeterminantCertificate where
  elimination := redhefferEliminator_mul_redhefferMatrix
  eliminatorDet := det_redhefferEliminator
  tailDet := det_redhefferTail
  mertensDet := det_redhefferMatrix_eq_finiteMertens
  lowOrders := ⟨det_redheffer_order_one, det_redheffer_order_two,
    det_redheffer_order_three, det_redheffer_order_four⟩

end LeanLab.Riemann
