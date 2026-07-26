import LeanLab.Riemann.FinitePowerSumRigidity
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.Basic

/-!
# The Bombieri--Stepanov Frobenius auxiliary mechanism

This file isolates the finite-field algebra and root-multiplicity budget inside the
Bombieri--Stepanov proof of the Riemann hypothesis for curves over finite fields.
-/

namespace LeanLab

namespace Riemann

open Finset Polynomial
open scoped BigOperators Polynomial

noncomputable section

/-- The polynomial before applying the characteristic-power Frobenius. -/
def stepanovFrobeniusBase {K ι : Type*} [Semiring K] [Fintype ι]
    (r : ℕ) (v s : ι → K[X]) : K[X] :=
  ∑ i, v i * s i ^ r

/-- Bombieri's descent replaces the finite-field cardinal power by the first power. -/
def stepanovFrobeniusDescent {K ι : Type*} [Semiring K] [Fintype ι]
    (p μ : ℕ) (v s : ι → K[X]) : K[X] :=
  ∑ i, v i ^ (p ^ μ) * s i

/-- The source auxiliary is a perfect characteristic power. -/
def stepanovFrobeniusAuxiliary {K ι : Type*} [Semiring K] [Fintype ι]
    (p μ r : ℕ) (v s : ι → K[X]) : K[X] :=
  stepanovFrobeniusBase r v s ^ (p ^ μ)

theorem stepanovFrobeniusAuxiliary_eq_sum
    {K ι : Type*} [CommSemiring K] [Fintype ι]
    {p : ℕ} [ExpChar K p] (μ r : ℕ) (v s : ι → K[X]) :
    stepanovFrobeniusAuxiliary p μ r v s =
      ∑ i, v i ^ (p ^ μ) * s i ^ (r * p ^ μ) := by
  rw [stepanovFrobeniusAuxiliary, stepanovFrobeniusBase]
  calc
    (∑ i, v i * s i ^ r) ^ p ^ μ =
        ∑ i, (v i * s i ^ r) ^ (p ^ μ) := by
      simpa only [Finset.sum_filter, Finset.mem_univ, true_and] using
        (sum_pow_char_pow (R := K[X]) p μ Finset.univ fun i => v i * s i ^ r)
    _ = ∑ i, v i ^ (p ^ μ) * s i ^ (r * p ^ μ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [mul_pow, pow_mul]

theorem stepanovFrobeniusAuxiliary_eval_eq_descent
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    {p : ℕ} [CharP K p] [Fact p.Prime] (μ r : ℕ) (v s : ι → K[X])
    (hq : r * p ^ μ = Fintype.card K) (a : K) :
    (stepanovFrobeniusAuxiliary p μ r v s).eval a =
      (stepanovFrobeniusDescent p μ v s).eval a := by
  rw [stepanovFrobeniusAuxiliary_eq_sum, stepanovFrobeniusDescent]
  simp only [eval_finsetSum, eval_mul, eval_pow]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [hq, FiniteField.pow_card]

/-- Root multiplicity is exactly additive under a nonzero polynomial power. -/
theorem stepanov_rootMultiplicity_pow
    {K : Type*} [Field K] (f : K[X]) (a : K) (n : ℕ) (hf : f ≠ 0) :
    rootMultiplicity a (f ^ n) = n * rootMultiplicity a f := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hf) hf), ih,
        Nat.succ_mul]

theorem stepanovFrobeniusAuxiliary_rootMultiplicity
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    {p : ℕ} [CharP K p] [Fact p.Prime] {μ r : ℕ}
    (v s : ι → K[X]) (hq : r * p ^ μ = Fintype.card K)
    (hdescent : stepanovFrobeniusDescent p μ v s = 0)
    (hbase : stepanovFrobeniusBase r v s ≠ 0) (a : K) :
    p ^ μ ≤ rootMultiplicity a (stepanovFrobeniusAuxiliary p μ r v s) := by
  have hm : 0 < p ^ μ := pow_pos (Fact.out : p.Prime).pos μ
  have hroot :
      (stepanovFrobeniusAuxiliary p μ r v s).IsRoot a := by
    rw [IsRoot, stepanovFrobeniusAuxiliary_eval_eq_descent μ r v s hq, hdescent,
      eval_zero]
  have hbaseRoot : (stepanovFrobeniusBase r v s).IsRoot a := by
    rw [IsRoot] at hroot ⊢
    rw [stepanovFrobeniusAuxiliary, eval_pow] at hroot
    exact (pow_eq_zero_iff hm.ne').1 hroot
  have hbaseMultiplicity :
      1 ≤ rootMultiplicity a (stepanovFrobeniusBase r v s) :=
    (rootMultiplicity_pos hbase).2 hbaseRoot
  rw [stepanovFrobeniusAuxiliary,
    stepanov_rootMultiplicity_pow (stepanovFrobeniusBase r v s) a (p ^ μ) hbase]
  simpa only [Nat.mul_one] using
    Nat.mul_le_mul_left (p ^ μ) hbaseMultiplicity

/-- Distinct roots with uniform multiplicity consume that multiplicity in the degree budget. -/
theorem finset_card_mul_le_natDegree_of_rootMultiplicity
    {K : Type*} [Field K] (f : K[X]) (hf : f ≠ 0)
    (S : Finset K) {m : ℕ} (hm : 0 < m)
    (hmult : ∀ a ∈ S, m ≤ rootMultiplicity a f) :
    m * S.card ≤ f.natDegree := by
  classical
  have hsubset : S ⊆ f.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, mem_roots hf]
    exact (rootMultiplicity_pos hf).1 (hm.trans_le (hmult a ha))
  calc
    m * S.card = ∑ a ∈ S, m := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ S, rootMultiplicity a f :=
      Finset.sum_le_sum fun a ha => hmult a ha
    _ = ∑ a ∈ S, f.roots.count a := by
      simp only [count_roots]
    _ ≤ ∑ a ∈ f.roots.toFinset, f.roots.count a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _a _ha _hnot => Nat.zero_le _
    _ = f.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ f.natDegree := Polynomial.card_roots' f

theorem stepanovFrobenius_card_mul_le_natDegree
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    {p : ℕ} [CharP K p] [Fact p.Prime] {μ r : ℕ}
    (v s : ι → K[X]) (hq : r * p ^ μ = Fintype.card K)
    (hdescent : stepanovFrobeniusDescent p μ v s = 0)
    (hbase : stepanovFrobeniusBase r v s ≠ 0) :
    p ^ μ * Fintype.card K ≤
      (stepanovFrobeniusAuxiliary p μ r v s).natDegree := by
  simpa using
    finset_card_mul_le_natDegree_of_rootMultiplicity
      (stepanovFrobeniusAuxiliary p μ r v s)
      (pow_ne_zero (p ^ μ) hbase) Finset.univ
      (pow_pos (Fact.out : p.Prime).pos μ)
      (fun a _ha =>
        stepanovFrobeniusAuxiliary_rootMultiplicity v s hq hdescent hbase a)

theorem stepanovFrobenius_card_le_natDegree_div
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    {p : ℕ} [CharP K p] [Fact p.Prime] {μ r : ℕ}
    (v s : ι → K[X]) (hq : r * p ^ μ = Fintype.card K)
    (hdescent : stepanovFrobeniusDescent p μ v s = 0)
    (hbase : stepanovFrobeniusBase r v s ≠ 0) :
    Fintype.card K ≤
      (stepanovFrobeniusAuxiliary p μ r v s).natDegree / (p ^ μ) := by
  rw [Nat.le_div_iff_mul_le (pow_pos (Fact.out : p.Prime).pos μ)]
  simpa only [Nat.mul_comm] using
    stepanovFrobenius_card_mul_le_natDegree v s hq hdescent hbase

def stepanovZModTwoV : Fin 2 → (ZMod 2)[X]
  | 0 => X
  | 1 => 1

def stepanovZModTwoS : Fin 2 → (ZMod 2)[X]
  | 0 => 1
  | 1 => X ^ 2

theorem stepanovZModTwo_base :
    stepanovFrobeniusBase 1 stepanovZModTwoV stepanovZModTwoS = X + X ^ 2 := by
  simp [stepanovFrobeniusBase, stepanovZModTwoV, stepanovZModTwoS, Fin.sum_univ_two]

theorem stepanovZModTwo_descent :
    stepanovFrobeniusDescent 2 1 stepanovZModTwoV stepanovZModTwoS = 0 := by
  simp [stepanovFrobeniusDescent, stepanovZModTwoV, stepanovZModTwoS,
    Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem stepanovZModTwo_base_ne_zero :
    stepanovFrobeniusBase 1 stepanovZModTwoV stepanovZModTwoS ≠ 0 := by
  rw [stepanovZModTwo_base]
  intro h
  have hcoeff := congrArg (fun f : (ZMod 2)[X] => f.coeff 2) h
  norm_num [coeff_add, coeff_X, coeff_X_pow] at hcoeff

private theorem stepanovZModTwo_base_factor :
    stepanovFrobeniusBase 1 stepanovZModTwoV stepanovZModTwoS =
      X * (X + 1) := by
  rw [stepanovZModTwo_base]
  ring

theorem stepanovZModTwo_rootMultiplicity_zero :
    rootMultiplicity (0 : ZMod 2)
      (stepanovFrobeniusAuxiliary 2 1 1
        stepanovZModTwoV stepanovZModTwoS) = 2 := by
  rw [stepanovFrobeniusAuxiliary]
  simp only [pow_one]
  rw [
    stepanov_rootMultiplicity_pow
      (stepanovFrobeniusBase 1 stepanovZModTwoV stepanovZModTwoS)
      (0 : ZMod 2) 2 stepanovZModTwo_base_ne_zero,
    stepanovZModTwo_base_factor]
  have hXOne : (X + 1 : (ZMod 2)[X]) = X - C 1 := by
    ext n
    simp [sub_eq_add_neg]
  have hXne : (X : (ZMod 2)[X]) ≠ 0 := X_ne_zero
  have hXOneNe : (X + 1 : (ZMod 2)[X]) ≠ 0 := by
    rw [hXOne]
    exact X_sub_C_ne_zero 1
  have hrootX : rootMultiplicity (0 : ZMod 2) (X : (ZMod 2)[X]) = 1 := by
    rw [show (X : (ZMod 2)[X]) = X - C 0 by simp, rootMultiplicity_X_sub_C]
    simp
  have hrootXOne :
      rootMultiplicity (0 : ZMod 2) (X + 1 : (ZMod 2)[X]) = 0 := by
    rw [hXOne, rootMultiplicity_X_sub_C]
    norm_num
  rw [rootMultiplicity_mul (mul_ne_zero hXne hXOneNe), hrootX, hrootXOne]

theorem stepanovZModTwo_rootMultiplicity_one :
    rootMultiplicity (1 : ZMod 2)
      (stepanovFrobeniusAuxiliary 2 1 1
        stepanovZModTwoV stepanovZModTwoS) = 2 := by
  rw [stepanovFrobeniusAuxiliary]
  simp only [pow_one]
  rw [
    stepanov_rootMultiplicity_pow
      (stepanovFrobeniusBase 1 stepanovZModTwoV stepanovZModTwoS)
      (1 : ZMod 2) 2 stepanovZModTwo_base_ne_zero,
    stepanovZModTwo_base_factor]
  have hXOne : (X + 1 : (ZMod 2)[X]) = X - C 1 := by
    ext n
    simp [sub_eq_add_neg]
  have hXne : (X : (ZMod 2)[X]) ≠ 0 := X_ne_zero
  have hXOneNe : (X + 1 : (ZMod 2)[X]) ≠ 0 := by
    rw [hXOne]
    exact X_sub_C_ne_zero 1
  have hrootX : rootMultiplicity (1 : ZMod 2) (X : (ZMod 2)[X]) = 0 := by
    rw [show (X : (ZMod 2)[X]) = X - C 0 by simp, rootMultiplicity_X_sub_C]
    norm_num
  have hrootXOne :
      rootMultiplicity (1 : ZMod 2) (X + 1 : (ZMod 2)[X]) = 1 := by
    rw [hXOne, rootMultiplicity_X_sub_C]
    norm_num
  rw [rootMultiplicity_mul (mul_ne_zero hXne hXOneNe), hrootX, hrootXOne]

theorem stepanovZModTwo_saturated :
    (∀ a : ZMod 2,
      2 ≤ rootMultiplicity a
        (stepanovFrobeniusAuxiliary 2 1 1 stepanovZModTwoV stepanovZModTwoS)) ∧
    (stepanovFrobeniusAuxiliary 2 1 1
      stepanovZModTwoV stepanovZModTwoS).natDegree = 4 ∧
    2 * Fintype.card (ZMod 2) = 4 := by
  have hq : 1 * 2 ^ 1 = Fintype.card (ZMod 2) := by norm_num [ZMod.card]
  constructor
  · intro a
    simpa using
      stepanovFrobeniusAuxiliary_rootMultiplicity (p := 2)
        (μ := 1) (r := 1) stepanovZModTwoV stepanovZModTwoS hq
        stepanovZModTwo_descent stepanovZModTwo_base_ne_zero a
  constructor
  · rw [stepanovFrobeniusAuxiliary, stepanovZModTwo_base,
      Polynomial.natDegree_pow]
    have hdeg : ((X + X ^ 2 : (ZMod 2)[X])).natDegree = 2 := by
      have hlt :
          (X : (ZMod 2)[X]).natDegree < (X ^ 2 : (ZMod 2)[X]).natDegree := by
        norm_num [Polynomial.natDegree_X_pow]
      rw [natDegree_add_eq_right_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    rw [hdeg]
    norm_num
  · norm_num [ZMod.card]

end

end Riemann

end LeanLab
