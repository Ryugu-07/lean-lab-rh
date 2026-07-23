import LeanLab.Riemann.WeilGroundStateFiniteMatrix
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite Weil prime block

This module instantiates the integer-cutoff von Mangoldt sine source in the finite Weil matrix.
It proves the exact finite atom decomposition, reflection-sector preservation, and an actual
prime-power atom with opposite strict signs on explicit even and odd level-one vectors.

It does not prove a sign for the aggregate prime block or assemble the archimedean block.
-/

open Matrix
open scoped ArithmeticFunction BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- The source frequency `1-log(q)/log(C)` for an integer prime cutoff. -/
def weilPrimeFrequency (C q : ℕ) : ℝ :=
  1 - Real.log q / Real.log C

/-- The signed atom weight `-Lambda(q)/sqrt(q)`. -/
def weilPrimeAtomCoefficient (q : ℕ) : ℝ :=
  -ArithmeticFunction.vonMangoldt q / Real.sqrt q

theorem weilPrimeFrequency_mem_unitInterval {C q : ℕ}
    (hC : 2 ≤ C) (hq : 2 ≤ q) (hqC : q ≤ C) :
    0 ≤ weilPrimeFrequency C q ∧ weilPrimeFrequency C q ≤ 1 := by
  have hCpos : (0 : ℝ) < C := by positivity
  have hqpos : (0 : ℝ) < q := by positivity
  have hlogC : 0 < Real.log C := Real.log_pos (by exact_mod_cast hC)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hlog_le : Real.log q ≤ Real.log C :=
    Real.log_le_log hqpos (by exact_mod_cast hqC)
  have hdiv_nonneg : 0 ≤ Real.log q / Real.log C := div_nonneg hlogq hlogC.le
  have hdiv_le : Real.log q / Real.log C ≤ 1 := (div_le_one hlogC).2 hlog_le
  constructor <;> simp only [weilPrimeFrequency] <;> linarith

theorem weilPrimeAtomCoefficient_nonpos (q : ℕ) :
    weilPrimeAtomCoefficient q ≤ 0 := by
  rw [weilPrimeAtomCoefficient]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (ArithmeticFunction.vonMangoldt_nonneg (n := q))) (Real.sqrt_nonneg q)

theorem weilPrimeAtomCoefficient_neg {q : ℕ} (hq : 2 ≤ q)
    (hqPrimePow : IsPrimePow q) :
    weilPrimeAtomCoefficient q < 0 := by
  rw [weilPrimeAtomCoefficient]
  exact div_neg_of_neg_of_pos
    (neg_lt_zero.mpr (ArithmeticFunction.vonMangoldt_pos_iff.mpr hqPrimePow))
    (Real.sqrt_pos.2 (by positivity))

theorem weilPrimeAtomCoefficient_eq_zero_of_not_isPrimePow {q : ℕ}
    (hq : ¬IsPrimePow q) :
    weilPrimeAtomCoefficient q = 0 := by
  rw [weilPrimeAtomCoefficient, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hq]
  simp

/-- One literal von Mangoldt sine source atom. -/
def weilPrimeAtomSource (C q : ℕ) (x : ℝ) : ℝ :=
  weilPrimeAtomCoefficient q / Real.pi *
    Real.sin (2 * Real.pi * weilPrimeFrequency C q * x)

theorem hasDerivAt_weilPrimeAtomSource (C q : ℕ) (x : ℝ) :
    HasDerivAt (weilPrimeAtomSource C q)
      (2 * weilPrimeAtomCoefficient q * weilPrimeFrequency C q *
        Real.cos (2 * Real.pi * weilPrimeFrequency C q * x)) x := by
  change HasDerivAt
    (fun y : ℝ => weilPrimeAtomCoefficient q / Real.pi *
      Real.sin (2 * Real.pi * weilPrimeFrequency C q * y))
    (2 * weilPrimeAtomCoefficient q * weilPrimeFrequency C q *
      Real.cos (2 * Real.pi * weilPrimeFrequency C q * x)) x
  let k : ℝ := 2 * Real.pi * weilPrimeFrequency C q
  have hinner : HasDerivAt (fun y : ℝ => k * y) k x :=
    by simpa using (hasDerivAt_id x).const_mul k
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (k * y))
      (Real.cos (k * x) * k) x :=
    (Real.hasDerivAt_sin (k * x)).comp x hinner
  have hscaled := hsin.const_mul (weilPrimeAtomCoefficient q / Real.pi)
  have hder :
      weilPrimeAtomCoefficient q / Real.pi * (Real.cos (k * x) * k) =
        2 * weilPrimeAtomCoefficient q * weilPrimeFrequency C q *
          Real.cos (2 * Real.pi * weilPrimeFrequency C q * x) := by
    dsimp [k]
    field_simp [Real.pi_ne_zero]
  simpa only [k] using hscaled.congr_deriv hder

/-- Value samples of one von Mangoldt sine atom. -/
def weilPrimeAtomSourceValue (C q N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  weilPrimeAtomCoefficient q / Real.pi *
    Real.sin (2 * Real.pi * weilPrimeFrequency C q *
      weilFiniteCenteredFrequency N i)

theorem weilPrimeAtomSourceValue_eq (C q N : ℕ) (i : Fin (2 * N + 1)) :
    weilPrimeAtomSourceValue C q N i =
      weilPrimeAtomSource C q (weilFiniteCenteredFrequency N i) := by
  rfl

/-- Derivative samples of one von Mangoldt sine atom. -/
def weilPrimeAtomSourceDerivative (C q N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  2 * weilPrimeAtomCoefficient q * weilPrimeFrequency C q *
    Real.cos (2 * Real.pi * weilPrimeFrequency C q *
      weilFiniteCenteredFrequency N i)

theorem hasDerivAt_weilPrimeAtomSource_centered (C q N : ℕ)
    (i : Fin (2 * N + 1)) :
    HasDerivAt (weilPrimeAtomSource C q)
      (weilPrimeAtomSourceDerivative C q N i) (weilFiniteCenteredFrequency N i) := by
  exact hasDerivAt_weilPrimeAtomSource C q (weilFiniteCenteredFrequency N i)

theorem weilPrimeAtomSourceValue_rev (C q N : ℕ) (i : Fin (2 * N + 1)) :
    weilPrimeAtomSourceValue C q N i.rev = -weilPrimeAtomSourceValue C q N i := by
  rw [weilPrimeAtomSourceValue, weilPrimeAtomSourceValue,
    weilFiniteCenteredFrequency_rev]
  push_cast
  rw [show 2 * Real.pi * weilPrimeFrequency C q *
      (-(weilFiniteCenteredFrequency N i : ℝ)) =
      -(2 * Real.pi * weilPrimeFrequency C q *
        weilFiniteCenteredFrequency N i) by ring,
    Real.sin_neg]
  ring

theorem weilPrimeAtomSourceDerivative_rev (C q N : ℕ)
    (i : Fin (2 * N + 1)) :
    weilPrimeAtomSourceDerivative C q N i.rev =
      weilPrimeAtomSourceDerivative C q N i := by
  rw [weilPrimeAtomSourceDerivative, weilPrimeAtomSourceDerivative,
    weilFiniteCenteredFrequency_rev]
  push_cast
  rw [show 2 * Real.pi * weilPrimeFrequency C q *
      (-(weilFiniteCenteredFrequency N i : ℝ)) =
      -(2 * Real.pi * weilPrimeFrequency C q *
        weilFiniteCenteredFrequency N i) by ring,
    Real.cos_neg]

/-- The literal integer-cutoff prime source value samples. -/
def weilPrimeSourceValue (C N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ∑ q ∈ Finset.Icc 2 C, weilPrimeAtomSourceValue C q N i

/-- The literal integer-cutoff prime source derivative samples. -/
def weilPrimeSourceDerivative (C N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  ∑ q ∈ Finset.Icc 2 C, weilPrimeAtomSourceDerivative C q N i

theorem weilPrimeSourceValue_rev (C N : ℕ) (i : Fin (2 * N + 1)) :
    weilPrimeSourceValue C N i.rev = -weilPrimeSourceValue C N i := by
  simp_rw [weilPrimeSourceValue, weilPrimeAtomSourceValue_rev, Finset.sum_neg_distrib]

theorem weilPrimeSourceDerivative_rev (C N : ℕ) (i : Fin (2 * N + 1)) :
    weilPrimeSourceDerivative C N i.rev = weilPrimeSourceDerivative C N i := by
  simp_rw [weilPrimeSourceDerivative, weilPrimeAtomSourceDerivative_rev]

/-- The divided-difference matrix of one prime source atom. -/
def weilFinitePrimeAtomMatrix (C q N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  weilFiniteDividedDifferenceMatrix N
    (weilPrimeAtomSourceDerivative C q N) (weilPrimeAtomSourceValue C q N)

/-- The divided-difference matrix of the complete integer-cutoff prime source. -/
def weilFinitePrimeSourceMatrix (C N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  weilFiniteDividedDifferenceMatrix N
    (weilPrimeSourceDerivative C N) (weilPrimeSourceValue C N)

theorem weilFinitePrimeSourceMatrix_eq_sum_atoms (C N : ℕ) :
    weilFinitePrimeSourceMatrix C N =
      ∑ q ∈ Finset.Icc 2 C, weilFinitePrimeAtomMatrix C q N := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weilFinitePrimeSourceMatrix, weilFinitePrimeAtomMatrix,
      weilFiniteDividedDifferenceMatrix, weilPrimeSourceDerivative, Matrix.sum_apply]
  · simp only [weilFinitePrimeSourceMatrix, weilFinitePrimeAtomMatrix,
      weilFiniteDividedDifferenceMatrix, hij, if_false, Matrix.sum_apply]
    rw [weilPrimeSourceValue, weilPrimeSourceValue]
    simp only [div_eq_mul_inv, sub_mul, Finset.sum_mul, Finset.sum_sub_distrib]

theorem weilFinitePrimeSourceMatrix_reflection (C N : ℕ)
    (i j : Fin (2 * N + 1)) :
    weilFinitePrimeSourceMatrix C N i.rev j.rev =
      weilFinitePrimeSourceMatrix C N i j := by
  exact weilFiniteDividedDifferenceMatrix_reflection N _ _
    (weilPrimeSourceDerivative_rev C N) (weilPrimeSourceValue_rev C N) i j

theorem weilFinitePrimeSourceMatrix_mulVec_isEven (C N : ℕ)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsEven x) :
    WeilFiniteIsEven (weilFinitePrimeSourceMatrix C N *ᵥ x) :=
  weilFiniteMatrix_mulVec_isEven _ (weilFinitePrimeSourceMatrix_reflection C N) hx

theorem weilFinitePrimeSourceMatrix_mulVec_isOdd (C N : ℕ)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsOdd x) :
    WeilFiniteIsOdd (weilFinitePrimeSourceMatrix C N *ᵥ x) :=
  weilFiniteMatrix_mulVec_isOdd _ (weilFinitePrimeSourceMatrix_reflection C N) hx

theorem weilPrimeFrequency_sixteen_eight :
    weilPrimeFrequency 16 8 = 1 / 4 := by
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  change 1 - Real.log (8 : ℝ) / Real.log (16 : ℝ) = 1 / 4
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num,
    show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow, Real.log_pow]
  norm_num
  field_simp [hlogTwo]
  norm_num

theorem weilPrimeAtomCoefficient_eight_neg :
    weilPrimeAtomCoefficient 8 < 0 := by
  apply weilPrimeAtomCoefficient_neg (by norm_num)
  simpa using Nat.prime_two.isPrimePow.pow (by norm_num : 3 ≠ 0)

/-- The centered level-one even witness. -/
def weilPrimeLevelOneEven : Fin 3 → ℝ :=
  ![0, 1, 0]

/-- The antisymmetric level-one edge witness. -/
def weilPrimeLevelOneOdd : Fin 3 → ℝ :=
  ![1, 0, -1]

theorem weilPrimeLevelOneEven_isEven :
    WeilFiniteIsEven (N := 1) weilPrimeLevelOneEven := by
  rw [weilFiniteIsEven_iff]
  intro i
  fin_cases i <;> simp [weilPrimeLevelOneEven]

theorem weilPrimeLevelOneOdd_isOdd :
    WeilFiniteIsOdd (N := 1) weilPrimeLevelOneOdd := by
  rw [weilFiniteIsOdd_iff]
  intro i
  fin_cases i <;> simp [weilPrimeLevelOneOdd]

theorem weilFinitePrimeAtomMatrix_sixteen_eight_even_value :
    weilPrimeLevelOneEven ⬝ᵥ
        (weilFinitePrimeAtomMatrix 16 8 1 *ᵥ weilPrimeLevelOneEven) =
      weilPrimeAtomCoefficient 8 / 2 := by
  simp [dotProduct, mulVec, weilPrimeLevelOneEven, weilFinitePrimeAtomMatrix,
    weilFiniteDividedDifferenceMatrix, weilPrimeAtomSourceDerivative,
    weilPrimeFrequency_sixteen_eight, weilFiniteCenteredFrequency, Fin.sum_univ_succ]
  ring

theorem weilFinitePrimeAtomMatrix_sixteen_eight_odd_value :
    weilPrimeLevelOneOdd ⬝ᵥ
        (weilFinitePrimeAtomMatrix 16 8 1 *ᵥ weilPrimeLevelOneOdd) =
      -2 * weilPrimeAtomCoefficient 8 / Real.pi := by
  simp only [dotProduct, weilPrimeLevelOneOdd, mulVec, Nat.reduceMul, Nat.reduceAdd,
    weilFinitePrimeAtomMatrix, weilFiniteDividedDifferenceMatrix,
    weilPrimeAtomSourceDerivative, weilPrimeFrequency_sixteen_eight, one_div,
    weilFiniteCenteredFrequency, Nat.cast_one, Int.cast_sub, Int.cast_natCast, Int.cast_one,
    weilPrimeAtomSourceValue, sub_sub_sub_cancel_right, ite_mul, Fin.sum_univ_succ,
    Fin.isValue, cons_val_zero, mul_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    CharP.cast_eq_zero, zero_sub, mul_neg, Real.sin_neg, sub_neg_eq_add, sub_zero,
    cons_val_succ, Fin.val_succ, Nat.cast_add, add_sub_cancel_right,
    Fin.succ_zero_eq_one, mul_zero, Real.sin_zero, zero_add, ite_self,
    Finset.univ_unique, Fin.default_eq_zero, cons_val_fin_one, Fin.val_eq_zero,
    Finset.sum_singleton, Fin.succ_one_eq_two, ↓reduceIte, Real.cos_neg, Fin.reduceEq,
    neg_add_rev, one_mul, Fin.succ_ne_zero, add_sub_add_right_eq_sub, div_one,
    neg_div_neg_eq, add_neg_cancel, sub_self, div_zero, neg_zero, neg_mul, neg_neg]
  rw [show 2 * Real.pi * (4 : ℝ)⁻¹ = Real.pi / 2 by ring,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  ring

theorem weilFinitePrimeAtomMatrix_sixteen_eight_even_neg :
    weilPrimeLevelOneEven ⬝ᵥ
        (weilFinitePrimeAtomMatrix 16 8 1 *ᵥ weilPrimeLevelOneEven) < 0 := by
  rw [weilFinitePrimeAtomMatrix_sixteen_eight_even_value]
  linarith [weilPrimeAtomCoefficient_eight_neg]

theorem weilFinitePrimeAtomMatrix_sixteen_eight_odd_pos :
    0 < weilPrimeLevelOneOdd ⬝ᵥ
        (weilFinitePrimeAtomMatrix 16 8 1 *ᵥ weilPrimeLevelOneOdd) := by
  rw [weilFinitePrimeAtomMatrix_sixteen_eight_odd_value]
  exact div_pos (mul_pos_of_neg_of_neg (by norm_num) weilPrimeAtomCoefficient_eight_neg)
    Real.pi_pos

theorem weilFinitePrimeBlockAudit_endpoint (C N : ℕ) :
    weilFinitePrimeSourceMatrix C N =
        ∑ q ∈ Finset.Icc 2 C, weilFinitePrimeAtomMatrix C q N ∧
      (∀ x, WeilFiniteIsEven x →
        WeilFiniteIsEven (weilFinitePrimeSourceMatrix C N *ᵥ x)) ∧
      (∀ x, WeilFiniteIsOdd x →
        WeilFiniteIsOdd (weilFinitePrimeSourceMatrix C N *ᵥ x)) ∧
      weilPrimeLevelOneEven ⬝ᵥ
          (weilFinitePrimeAtomMatrix 16 8 1 *ᵥ weilPrimeLevelOneEven) < 0 ∧
      0 < weilPrimeLevelOneOdd ⬝ᵥ
          (weilFinitePrimeAtomMatrix 16 8 1 *ᵥ weilPrimeLevelOneOdd) := by
  exact ⟨weilFinitePrimeSourceMatrix_eq_sum_atoms C N,
    fun _ hx => weilFinitePrimeSourceMatrix_mulVec_isEven C N hx,
    fun _ hx => weilFinitePrimeSourceMatrix_mulVec_isOdd C N hx,
    weilFinitePrimeAtomMatrix_sixteen_eight_even_neg,
    weilFinitePrimeAtomMatrix_sixteen_eight_odd_pos⟩

end

end LeanLab.Riemann
